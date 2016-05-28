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
#include "klee/Constraints.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KInstIterator.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/util/ArrayCache.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/DataLayout.h"
#include "klee/Solver.h"
#include "Memory.h"
#include "ObjectHolder.h"
#include <vector>
#include <string>
#include <map>
#include <set>

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
  struct KFunction;
  class KConstant;
  class PTree;
  class PTreeNode;
  class SeedInfo;
  class SpecialFunctionHandler;
  template<class T> class ref;
  typedef ref<Expr> Cell;
  typedef std::pair<const MemoryObject*, const ObjectState*> ObjectPair;
  typedef std::vector<ObjectPair> ResolutionList;

  class MemoryMap {
  class MemNode {
  public:
    static MemNode terminator;
    MemNode *left, *right;
    ObjectPair value;
    unsigned height, references;
  private:
    MemNode(): left(&terminator), right(&terminator), height(0), references(3){assert(this==&terminator);}
    static MemNode *balance(MemNode *left, const ObjectPair &value, MemNode *right) { return new MemNode(left, right, value); }
    MemNode *popMin(ObjectPair &valueOut) {
      if (left->isTerminator()) {
        valueOut = value;
        return right->incref();
      }
      return balance(left->popMin(valueOut), value, right->incref());
    }
  public:
    MemNode(MemNode *_left, MemNode *_right, const ObjectPair &_value)
      : left(_left), right(_right), value(_value), 
        height(std::max(left->height, right->height) + 1), references(1) { }
    ~MemNode() {
      left->decref();
      right->decref();
    }
    void decref() { if (--references==0) delete this; }
    MemNode *incref() {
      ++references;
      return this;
    }
    bool isTerminator() { return this==&terminator; }
    MemNode *insert(const ObjectPair &v) {
      if (isTerminator())
        return new MemNode(terminator.incref(), terminator.incref(), v);
      else if (v.first->address < value.first->address)
        return balance(left->insert(v), value, right->incref());
      else if (value.first->address < v.first->address)
        return balance(left->incref(), value, right->insert(v));
      return incref();
    }
    MemNode *replace(const ObjectPair &v) {
      if (isTerminator())
        return new MemNode(terminator.incref(), terminator.incref(), v);
      else if (v.first->address < value.first->address)
        return balance(left->replace(v), value, right->incref());
      else if (value.first->address < v.first->address)
        return balance(left->incref(), value, right->replace(v));
      return new MemNode(left->incref(), right->incref(), v);
    }
    MemNode *remove(const MemoryObject* &k) {
      if (isTerminator())
        return incref();
      else if (k->address < value.first->address)
        return balance(left->remove(k), value, right->incref());
      else if (value.first->address < k->address)
        return balance(left->incref(), value, right->remove(k));
      else if (left->isTerminator()) 
        return right->incref();
      else if (right->isTerminator())
        return left->incref();
      ObjectPair min;
      MemNode *nr = right->popMin(min);
      return balance(left->incref(), min, nr);
    }
  };
    MemNode *node;
    MemoryMap(MemNode *_node) : node(_node) { }
public:
    class iterator {
      friend class MemoryMap;
      MemNode *root; 
      unsigned pos, max;
      MemNode **elts;
    public:
      bool empty() { return pos==0; }
      void push_back(MemNode* elt) { elts[pos++] = elt; }
      void pop_back() { --pos; }
      MemNode* &back() { return elts[pos-1]; }
      iterator(MemNode *_root, bool atBeginning) : root(_root->incref()), pos(0), max(root->height), elts(new MemNode*[max]) {
        if (atBeginning)
          for (MemNode *n=root; !n->isTerminator(); n=n->left)
            push_back(n);
      }
      ~iterator() {
        root->decref();
        delete[] elts;
      }
      iterator &operator=(const iterator &b) {
        b.root->incref();
        root->decref();
        root = b.root;
        assert(max == b.max); 
        pos = b.pos;
        std::copy(b.elts, b.elts+pos, elts);
        return *this;
      }
      const ObjectPair &operator*() { return back()->value; }
      const ObjectPair *operator->() { return &back()->value; }
      bool operator==(const iterator &b) {
        return (pos == b.pos && std::equal(elts, elts+pos, b.elts));
      }
      bool operator!=(const iterator &b) { return !(*this==b); }
      iterator &operator--() {
        if (empty())
          for (MemNode *n=root; !n->isTerminator(); n=n->right)
            push_back(n);
        else {
          MemNode *n = back();
          if (n->left->isTerminator())
            for (;;) {
              MemNode *prev = n;
              pop_back();
              if (empty() || prev==back()->right)
                break;
            }
          else {
            push_back(n->left);
            for (n=n->left->right; !n->isTerminator(); n=n->right)
              push_back(n);
          }
        }
        return *this;
      }
      iterator &operator++() {
        assert(!empty());
        MemNode *n = back();
        if (n->right->isTerminator())
          for (;;) {
            MemNode *prev = n;
            pop_back();
            if (empty() || prev==back()->left)
              break;
          }
        else {
          push_back(n->right);
          for (n=n->right->left; !n->isTerminator(); n=n->left)
            push_back(n);
        }
        return *this;
      }
    };
  public:
    MemoryMap &operator=(const MemoryMap &s) {
      MemNode *n = s.node->incref();
      node->decref();
      node = n;
      return *this;
    }
    const ObjectPair *lookup(const MemoryObject* k) const {
      MemNode *n = node;
      while (!n->isTerminator()) {
        const MemoryObject* key = n->value.first;
        if (k->address < key->address)
          n = n->left;
        else if (key->address < k->address)
          n = n->right;
        else
          return &n->value;
      }
      return 0;
    }
    const ObjectPair *lookup_previous(const MemoryObject* k) const {
      MemNode *n = node;
      MemNode *result = 0;
      while (!n->isTerminator()) {
        const MemoryObject* key = n->value.first;
        if (k->address < key->address)
          n = n->left;
        else if (key->address < k->address) {
          result = n;
          n = n->right;
        } else
          return &n->value;
      }
      return result ? &result->value : 0;
    }
    MemoryMap insert(const ObjectPair &value) const { return MemoryMap(node->insert(value)); }
    MemoryMap replace(const ObjectPair &value) const { return MemoryMap(node->replace(value)); }
    MemoryMap remove(const MemoryObject* &key) const { return MemoryMap(node->remove(key)); }
    iterator begin() const { return iterator(node, true); }
    iterator end() const { return iterator(node, false); }
    iterator upper_bound(const MemoryObject* key) const {
      iterator end(node,false);
      iterator it(node,false);
      for (MemNode *root=node; !root->isTerminator();) {
        it.push_back(root);
        if (key->address < root->value.first->address)
          root = root->left;
        else if (root->value.first->address < key->address)
          root = root->right;
        else
          goto retlab;
      }
      if (!it.empty()) {
        MemNode *last = it.back();
        if (last->value.first->address < key->address)
          ++it;
      }
retlab:
      if (it!=end && !(key->address < it->first->address))
        ++it;
      return it;
    }
    MemoryMap() : node(MemNode::terminator.incref()) { }
    MemoryMap(const MemoryMap &s) : node(s.node->incref()) { }
    ~MemoryMap() { node->decref(); }
  };

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);


struct StackFrame {
  KInstIterator caller;
  llvm::Function *containingFunc;
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
  private:
  /// Epoch counter used to control ownership of objects.
  mutable unsigned cowKey;
  public:
  /// The MemoryObject -> ObjectState map that constitutes the address space.
  /// The set of objects where o->copyOnWriteOwner == cowKey are the objects that we own.
  /// \invariant forall o in objects, o->copyOnWriteOwner <= cowKey
  MemoryMap objects;
  bool resolveOne(const ref<ConstantExpr> &address, ObjectPair &result);
  /// Resolve address to a list of ObjectPairs it can point to. If
  /// maxResolutions is non-zero then no more than that many pairs will be returned.
  /// \return true iff the resolution is incomplete (maxResolutions
  /// is non-zero and the search terminated early, or a query timed out).
  void bindObject(const MemoryObject *mo, ObjectState *os) {
    assert(os->copyOnWriteOwner==0 && "object already has owner");
    os->copyOnWriteOwner = cowKey;
    objects = objects.replace(std::make_pair(mo, os));
  }
  void unbindObject(const MemoryObject *mo) {
    objects = objects.remove(mo);
  }
  /// \brief Obtain an ObjectState suitable for writing.
  /// This returns a writeable object state, creating a new copy of
  /// the given ObjectState if necessary. If the address space owns
  /// the ObjectState then this routine effectively just strips the const qualifier it.
  /// \param mo The MemoryObject to get a writeable ObjectState for.
  /// \param os The current binding of the MemoryObject.
  /// \return A writeable ObjectState (\a os or a copy).
  ObjectState *getWriteable(const MemoryObject *mo, const ObjectState *os);
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
  llvm::Module *module;
  std::vector<llvm::Constant*> constants;
  std::map<llvm::Constant*, KConstant*> constantMap;
private:
  ExternalDispatcher *externalDispatcher;
  Solver       *osolver;
  TreeStreamWriter *pathWriter, *symPathWriter;
  SpecialFunctionHandler *specialFunctionHandler;
  std::map<llvm::Function*, KFunction*> functionMap;
  llvm::DataLayout *targetData;
  std::set<llvm::Function*> escapingFunctions;

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
  void executeInstruction(ExecutionState &state);
  void runExecutor(ExecutionState &initialState);
  void initializeGlobalObject(ExecutionState &state, ObjectState *os, const llvm::Constant *c, unsigned offset);
  void transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state);
  // do address resolution / object binding / out of bounds checking // and perform the operation
  void executeMemoryOperation(ExecutionState &state, bool isWrite, ref<Expr> address, ref<Expr> value /* undef if read */, KInstruction *target /* undef if write */);
  /// Create a new state where each input condition has been added as
  /// a constraint and return the results. The input state is included
  /// as one of the results. Note that the output vector may included
  /// NULL pointers for states which were unable to be created.
  void branch(ExecutionState &state, std::vector<SeedInfo> *itemp, ref<Expr> e, KInstruction *ki, std::map<llvm::BasicBlock *, ref<Expr>> *targets);
  const ref<Expr> eval(KInstruction *ki, unsigned index, ExecutionState &state);
  void getArgumentCell(ExecutionState &state, KFunction *kf, unsigned aSize, std::vector<ref<Expr>> &arguments) {
    for (unsigned i = 0; i < aSize; i++)
        state.stack.back().locals[i] = arguments[i];
  }
  ref<klee::ConstantExpr> evalConstantExpr(const llvm::ConstantExpr *ce);
  template <typename TypeIt>
  void computeOffsets(KInstruction *ki, TypeIt ib, TypeIt ie);
  void prepareModule(const Interpreter::ModuleOptions &opts);
  double startWallTime;
  unsigned fullBranches, partialBranches;
  void writeStatsLine();
  unsigned numBranches;
  void computeReachableUncovered();
  bool resolve(ExecutionState &state, ref<Expr> address, ResolutionList &rl);
public: //friends
  /// Return a constant value for the given expression, forcing it to
  /// be constant in the given state by adding a constraint if
  /// necessary. Note that this function breaks completeness and
  /// should generally be avoided.  /// /// \param purpose An identify string to printed in case of concretization.
  ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e, const char *purpose);
  int mustBeTrue(const ExecutionState&, ref<Expr>);
  int mustBeFalse(const ExecutionState& state, ref<Expr> expr) {
    return mustBeTrue(state, Expr::createIsZero(expr));
  }
  bool mayBeTrue(const ExecutionState& state, ref<Expr> expr) {
    int res = mustBeFalse(state, expr);
    if (res == -1)
      return -1;
    return 1-res;
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
  void executeIntCall(ExecutionState &state, KInstruction *ki, llvm::Function *f, std::vector<ref<Expr>> &arguments);
  void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo, const std::string &name);
  // Fork current and return states in which condition holds / does
  // not hold, respectively. One of the states is necessarily the // current state, and one of the states may be null.
  StatePair stateFork(ExecutionState &current, ref<Expr> condition);

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
  void terminateStateOnError(ExecutionState &state, const llvm::Twine &message, const char *suffix, const llvm::Twine &longMessage = "");
  void terminateStateOnExecError(ExecutionState &state, const llvm::Twine &message) {
    terminateStateOnError(state, message, "exec.err", "");
  }
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
  unsigned getPathStreamID(const ExecutionState &state) {
    assert(pathWriter);
    return state.pathOS.getID();
  }
  unsigned getSymbolicPathStreamID(const ExecutionState &state) {
    assert(symPathWriter);
    return state.symPathOS.getID();
  }
  virtual void getConstraintLog(const ExecutionState &state, std::string &res, Interpreter::LogType logFormat);
  virtual bool getSymbolicSolution(const ExecutionState &state, std::vector< std::pair<std::string, std::vector<unsigned char>>> &res);
  void getCoveredLines(const ExecutionState &state, std::map<const std::string*, std::set<unsigned>> &res) {res = state.coveredLines;}
  Expr::Width getWidthForLLVMType(LLVM_TYPE_Q llvm::Type *type) const { return targetData->getTypeSizeInBits(type); }
  std::pair<ref<Expr>, ref<Expr>> solveGetRange(const ExecutionState&, ref<Expr> query) const;
};
} // End klee namespace
#endif

