//===-- Executor.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Class to perform actual execution, hides implementation details from external
// interpreter.
//
//===----------------------------------------------------------------------===//
#ifndef KLEE_EXECUTOR_H
#define KLEE_EXECUTOR_H
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/System/Time.h"
#include "klee/util/ArrayCache.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/DataLayout.h"
#include "klee/Solver.h"
#include <vector>
#include <string>
#include <map>
#include <set>
#include "klee/Constraints.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "../../lib/Core/AddressSpace.h"
#include "klee/Internal/Module/KInstIterator.h"

struct KTest;

namespace llvm {
  class BasicBlock;
  class BranchInst;
  class CallInst;
  class Constant;
  class ConstantExpr;
  class Function;
  class GlobalValue;
  class Instruction;
  class DataLayout;
  class Twine;
  class Value;
  class Module;
}

namespace klee {
  class ExternalDispatcher;
  class Expr;
  class KInstIterator;
  class MemoryManager;
  class MemoryObject;
  class ObjectState;
  class PTree;
  class SeedInfo;
  class SpecialFunctionHandler;
  struct StackFrame;
  class TreeStreamWriter;
  template<class T> class ref;
  struct KFunction;
  class KConstant;

  class Array;
  class CallPathNode;
  struct Cell;
  struct KInstruction;
  class PTreeNode;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);

struct StackFrame {
  KInstIterator caller;
  llvm::Function *func;
  unsigned numRegisters;
  std::vector<const MemoryObject *> allocas;
  Cell *locals;
  // For vararg functions: arguments not passed via parameter are
  // stored (packed tightly) in a local (alloca) memory object. This
  // is setup to match the way the front-end generates vaarg code (it
  // does not pass vaarg through as expected). VACopy is lowered inside
  // of intrinsic lowering.
  MemoryObject *varargs;
  StackFrame(KInstIterator _caller, llvm::Function *_kf, unsigned _numRegisters);
  StackFrame(const StackFrame &s);
  ~StackFrame();
};

/// @brief ExecutionState representing a path under exploration
class ExecutionState {
public:
  typedef std::vector<StackFrame> stack_ty; 
private:
  // unsupported, use copy constructor
  ExecutionState &operator=(const ExecutionState &); 
  std::map<std::string, std::string> fnAliases; 
public:
  /// @brief Pointer to instruction to be executed after the current /// instruction
  KInstIterator pc; 
  /// @brief Pointer to instruction which is currently executed
  KInstIterator prevPC; 
  /// @brief Stack representing the current instruction stream
  stack_ty stack; 
  /// @brief Remember from which Basic Block control flow arrived /// (i.e. to select the right phi values)
  unsigned incomingBBIndex; 
  /// @brief Address space used by this state (e.g. Global and Heap)
  AddressSpace addressSpace; 
  /// @brief Constraints collected so far
  ConstraintManager constraints; 
  /// @brief History of complete path: represents branches taken to
  /// reach/create this state (both concrete and symbolic)
  TreeOStream pathOS; 
  /// @brief History of symbolic path: represents symbolic branches
  /// taken to reach/create this state
  TreeOStream symPathOS; 
  /// @brief Counts how many instructions were executed since the last new
  /// instruction was covered.
  unsigned instsSinceCovNew; 
  /// @brief Whether a new instruction was covered in this state
  bool coveredNew;
  /// @brief Set containing which lines in which files are covered by this state
  std::map<const std::string *, std::set<unsigned> > coveredLines; 
  /// @brief Pointer to the process tree of the current state
  PTreeNode *ptreeNode; 
  /// @brief Ordered list of symbolics: used to generate test cases.
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<const MemoryObject *, const Array *> > symbolics; 
  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames; 
private:
  ExecutionState() : ptreeNode(0) {} 
public:
  ExecutionState(KInstruction **_instructions, llvm::Function *_func, unsigned _numRegisters);
  // XXX total hack, just used to make a state so solver can // use on structure
  ExecutionState(const std::vector<ref<Expr> > &assumptions); 
  ExecutionState(const ExecutionState &state); 
  ~ExecutionState(); 
  ExecutionState *branch(); 
  void pushFrame(KInstIterator caller, llvm::Function *_func, unsigned _numRegisters);
  void popFrame(); 
  void addSymbolic(const MemoryObject *mo, const Array *array);
  void addConstraint(ref<Expr> e) { constraints.addConstraint(e); } 
  void dumpStack(llvm::raw_ostream &out) const;
};

class Executor : public Interpreter {
public:
  typedef std::pair<ExecutionState*,ExecutionState*> StatePair;
  typedef enum { eSwitchTypeSimple, eSwitchTypeLLVM, eSwitchTypeInternal } SwitchImplType;

  std::set<ExecutionState*> states;
  InterpreterHandler *interpreterHandler;
  MemoryManager *memory;
  PTree *processTree;
  llvm::Module *module;
  unsigned getConstantID(llvm::Constant *c, KInstruction* ki);
private:
  ExternalDispatcher *externalDispatcher;
  Solver       *osolver;
  TreeStreamWriter *pathWriter, *symPathWriter;
  SpecialFunctionHandler *specialFunctionHandler;
  Cell *constantTable;
  std::map<llvm::Function*, KFunction*> functionMap;
  llvm::DataLayout *targetData;
  std::set<llvm::Function*> escapingFunctions;
  std::vector<llvm::Constant*> constants;
  std::map<llvm::Constant*, KConstant*> constantMap;
  SwitchImplType m_SwitchType;

  /// Used to track states that have been added during the current /// instructions step.
  /// \invariant \ref addedStates is a subset of \ref states.
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::set<ExecutionState*> addedStates;
  /// Used to track states that have been removed during the current /// instructions step.
  /// \invariant \ref removedStates is a subset of \ref states.
  /// \invariant \ref addedStates and \ref removedStates are disjoint.
  std::set<ExecutionState*> removedStates;
  /// When non-empty the Executor is running in "seed" mode. The
  /// states in this map will be executed in an arbitrary order
  /// (outside the normal search interface) until they terminate. When
  /// the states reach a symbolic branch then either direction that
  /// satisfies one or more seeds will be added to this map. What
  /// happens with other states (that don't satisfy the seeds) depends /// on as-yet-to-be-determined flags.
  std::map<ExecutionState*, std::vector<SeedInfo>> seedMap;
  /// Map of globals to their representative memory object.
  std::map<const llvm::GlobalValue*, MemoryObject*> globalObjects;
  /// Map of globals to their bound address. This also includes
  /// globals that have no representative object (i.e. functions).
  std::map<const llvm::GlobalValue*, ref<ConstantExpr>> globalAddresses;
  /// The set of legal function addresses, used to validate function
  /// pointers. We use the actual Function* address as the function address.
  std::set<uint64_t> legalFunctions;
  /// Assumes ownership of the created array objects
  ArrayCache arrayCache;

  llvm::Function* getTargetFunction(llvm::Value *calledVal, ExecutionState &state);
  void executeInstruction(ExecutionState &state);
  void runExecutor(ExecutionState &initialState);
  // Given a concrete object in our [klee's] address space, add it to // objects checked code can reference.
  MemoryObject *addExternalObject(ExecutionState &state, void *addr, unsigned size, bool isReadOnly);
  void initializeGlobalObject(ExecutionState &state, ObjectState *os, const llvm::Constant *c, unsigned offset);
  void initializeGlobals(ExecutionState &state);
  void transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state);
  void callExternalFunction(ExecutionState &state, KInstruction *target, llvm::Function *function, std::vector<ref<Expr>> &arguments);
  // do address resolution / object binding / out of bounds checking // and perform the operation
  void executeMemoryOperation(ExecutionState &state, bool isWrite, ref<Expr> address, ref<Expr> value /* undef if read */, KInstruction *target /* undef if write */);
  /// Create a new state where each input condition has been added as
  /// a constraint and return the results. The input state is included
  /// as one of the results. Note that the output vector may included
  /// NULL pointers for states which were unable to be created.
  void branch(ExecutionState &state, const std::vector<ref<Expr>> &conditions, std::vector<ExecutionState*> &result);
  const ref<Expr> eval(KInstruction *ki, unsigned index, ExecutionState &state) const;
  void getArgumentCell(ExecutionState &state, KFunction *kf, unsigned aSize, std::vector<ref<Expr>> &arguments) {
    for (unsigned i = 0; i < aSize; i++)
        state.stack.back().locals[i].value = arguments[i];
  }
  ref<klee::ConstantExpr> evalConstantExpr(const llvm::ConstantExpr *ce);
  /// Return a constant value for the given expression, forcing it to
  /// be constant in the given state by adding a constraint if
  /// necessary. Note that this function breaks completeness and
  /// should generally be avoided.  /// /// \param purpose An identify string to printed in case of concretization.
  ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e, const char *purpose);
  void terminateStateEarly(ExecutionState &state, const llvm::Twine &message);
  template <typename TypeIt>
  void computeOffsets(KInstruction *ki, TypeIt ib, TypeIt ie);
  void prepareModule(const Interpreter::ModuleOptions &opts);
  double startWallTime;
  unsigned fullBranches, partialBranches;
  void writeStatsLine();
  unsigned numBranches;
  void computeReachableUncovered();
public: //friends
  bool mustBeTrue(const ExecutionState&, ref<Expr>, bool &result);
  bool mustBeFalse(const ExecutionState& state, ref<Expr> expr, bool &result) {
    return mustBeTrue(state, Expr::createIsZero(expr), result);
  }
  bool mayBeTrue(const ExecutionState& state, ref<Expr> expr, bool &result) {
    bool res;
    if (!mustBeFalse(state, expr, res))
      return false;
    result = !res;
    return true;
  }
  bool solveGetValue(const ExecutionState &, ref<Expr> expr, ref<ConstantExpr> &result);
  ObjectState *bindObjectInState(ExecutionState &state, const MemoryObject *mo, bool isLocal, const Array *array = 0);
  /// Resolve a pointer to the memory objects it could point to the
  /// start of, forking execution when necessary and generating errors
  /// for pointers to invalid locations (either out of bounds or
  /// address inside the middle of objects).  ///
  /// \param results[out] A list of ((MemoryObject,ObjectState),
  /// state) pairs for each object the given address can point to the /// beginning of.
  typedef std::vector< std::pair<std::pair<const MemoryObject*, const ObjectState*>, ExecutionState*>> ExactResolutionList;
  void resolveExact(ExecutionState &state, ref<Expr> p, ExactResolutionList &results, const std::string &name);
  /// Allocate and bind a new object in a particular state. NOTE: This /// function may fork.  ///
  /// \param isLocal Flag to indicate if the object should be
  /// automatically deallocated on function return (this also makes it /// illegal to free directly).  ///
  /// \param target Value at which to bind the base address of the new /// object.  ///
  /// \param reallocFrom If non-zero and the allocation succeeds,
  /// initialize the new object from the given one and unbind it when
  /// done (realloc semantics). The initialized bytes will be the
  /// minimum of the size of the old and new objects, with remaining
  /// bytes initialized as specified by zeroMemory.
  void executeAlloc(ExecutionState &state, ref<Expr> size, bool isLocal, KInstruction *target, bool zeroMemory=false, const ObjectState *reallocFrom=0);
  /// Free the given address with checking for errors. If target is
  /// given it will be bound to 0 in the resulting states (this is a
  /// convenience for realloc). Note that this function can cause the
  /// state to fork and that \ref state cannot be safely accessed /// afterwards.
  void executeFree(ExecutionState &state, ref<Expr> address, KInstruction *target = 0);
  void executeCall(ExecutionState &state, KInstruction *ki, llvm::Function *f, std::vector<ref<Expr>> &arguments);
  void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo, const std::string &name);
  // Fork current and return states in which condition holds / does
  // not hold, respectively. One of the states is necessarily the // current state, and one of the states may be null.
  StatePair stateFork(ExecutionState &current, ref<Expr> condition, bool isInternal);

  /// Add the given (boolean) condition as a constraint on state. This
  /// function is a wrapper around the state's addConstraint function
  /// which also manages propagation of implied values, /// validity checks, and seed patching.
  void executeAddConstraint(ExecutionState &state, ref<Expr> condition);
  void bindLocal(KInstruction *target, ExecutionState &state, ref<Expr> value);
  /// Return a unique constant value for the given expression in the
  /// given state, if it has one (i.e. it provably only has a single
  /// value). Otherwise return the original expression.
  ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &e);
  /// Bind a constant value for e to the given target. NOTE: This
  /// function may fork state if the state has multiple seeds.
  void executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target);
  /// Get textual information regarding a memory address.
  std::string getAddressInfo(ExecutionState &state, ref<Expr> address);
  void terminateStateCase(ExecutionState &state, const char *err, const char *suffix);
  void terminateStateOnError(ExecutionState &state, const llvm::Twine &message, const char *suffix, const llvm::Twine &longMessage="");
  void terminateStateOnExecError(ExecutionState &state, const llvm::Twine &message, const llvm::Twine &info="") {
    terminateStateOnError(state, message, "exec.err", info);
  }
  void terminateStateOnExit(ExecutionState &state);
  Executor(const InterpreterOptions &opts, InterpreterHandler *ie);
  virtual ~Executor();
  // XXX should just be moved out to utility module
  ref<klee::ConstantExpr> evalConstant(const llvm::Constant *c);
  virtual void setPathWriter(TreeStreamWriter *tsw) { pathWriter = tsw; }
  virtual void setSymbolicPathWriter(TreeStreamWriter *tsw) { symPathWriter = tsw; }
  virtual const llvm::Module *
  setModule(llvm::Module *module, const ModuleOptions &opts);
  virtual void runFunctionAsMain(llvm::Function *f, int argc, char **argv, char **envp);
  /*** State accessor methods ***/
  virtual unsigned getPathStreamID(const ExecutionState &state);
  virtual unsigned getSymbolicPathStreamID(const ExecutionState &state);
  virtual void getConstraintLog(const ExecutionState &state, std::string &res, Interpreter::LogType logFormat);
  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector< std::pair<std::string, std::vector<unsigned char>>> &res);
  void getCoveredLines(const ExecutionState &state, std::map<const std::string*, std::set<unsigned>> &res) {res = state.coveredLines;}
  Expr::Width getWidthForLLVMType(LLVM_TYPE_Q llvm::Type *type) const { return targetData->getTypeSizeInBits(type); }
  std::pair<ref<Expr>, ref<Expr>> solveGetRange(const ExecutionState&, ref<Expr> query) const;
};
} // End klee namespace
#endif

