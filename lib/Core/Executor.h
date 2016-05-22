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

#if 1 //jca
namespace klee {
  struct MemoryObjectLT {
    bool operator()(const MemoryObject *a, const MemoryObject *b) const { return a->address < b->address; }
  };
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree {
  public:
    static size_t allocated;
    class iterator;
    typedef K key_type;
    typedef V value_type;
    typedef KOV key_of_value;
    typedef CMP key_compare;
  public:
    ImmutableTree() : node(Node::terminator.incref()) { }
    ImmutableTree(const ImmutableTree &s) : node(s.node->incref()) { }
    ~ImmutableTree() { node->decref(); }
    ImmutableTree &operator=(const ImmutableTree &s) {
      Node *n = s.node->incref();
      node->decref();
      node = n;
      return *this;
    }
    const value_type *lookup(const key_type &k) const {
      Node *n = node;
      while (!n->isTerminator()) {
        key_type key = key_of_value()(n->value);
        if (key_compare()(k, key)) {
          n = n->left;
        } else if (key_compare()(key, k)) {
          n = n->right;
        } else {
          return &n->value;
        }
      }
      return 0;
    }
    const value_type *lookup_previous(const key_type &k) const {
      Node *n = node;
      Node *result = 0;
      while (!n->isTerminator()) {
        key_type key = key_of_value()(n->value);
        if (key_compare()(k, key)) {
          n = n->left;
        } else if (key_compare()(key, k)) {
          result = n;
          n = n->right;
        } else {
          return &n->value;
        }
      }
      return result ? &result->value : 0;
    }
    size_t size() const { return node->size(); }
    ImmutableTree insert(const value_type &value) const { return ImmutableTree(node->insert(value)); }
    ImmutableTree replace(const value_type &value) const { return ImmutableTree(node->replace(value)); }
    ImmutableTree remove(const key_type &key) const { return ImmutableTree(node->remove(key)); }
    ImmutableTree popMin(value_type &valueOut) const { return ImmutableTree(node->popMin(valueOut)); }
    iterator begin() const { return iterator(node, true); }
    iterator end() const { return iterator(node, false); }
    iterator lower_bound(const key_type &k) const {
      iterator it(node,false);
      for (Node *root=node; !root->isTerminator();) {
        it.stack.push_back(root);
        if (key_compare()(k, key_of_value()(root->value))) {
          root = root->left;
        } else if (key_compare()(key_of_value()(root->value), k)) {
          root = root->right;
        } else {
          return it;
        }
      }
      if (!it.stack.empty()) {
        Node *last = it.stack.back();
        if (key_compare()(key_of_value()(last->value), k))
          ++it;
      }
      return it;
    }
    iterator upper_bound(const key_type &key) const {
      iterator end(node,false),it = lower_bound(key);
      if (it!=end && !key_compare()(key,key_of_value()(*it)))
        ++it;
      return it;
    }
    static size_t getAllocated() { return allocated; }
  private:
    class Node;
    Node *node;
    ImmutableTree(Node *_node) : node(_node) { }
  };
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree<K,V,KOV,CMP>::Node {
  public:
    static Node terminator;
    Node *left, *right;
    value_type value;
    unsigned height, references;
  protected:
    Node() : left(&terminator), right(&terminator), height(0), references(3) { assert(this==&terminator); }
    static Node *balance(Node *left, const value_type &value, Node *right) {
      if (left->height > right->height + 2) {
        Node *ll = left->left;
        Node *lr = left->right;
        if (ll->height >= lr->height) {
          Node *nlr = new Node(lr->incref(), right, value);
          Node *res = new Node(ll->incref(), nlr, left->value);
          left->decref();
          return res;
        } else {
          Node *lrl = lr->left;
          Node *lrr = lr->right;
          Node *nll = new Node(ll->incref(), lrl->incref(), left->value);
          Node *nlr = new Node(lrr->incref(), right, value);
          Node *res = new Node(nll, nlr, lr->value);
          left->decref();
          return res;
        }
      } else if (right->height > left->height + 2) {
        Node *rl = right->left;
        Node *rr = right->right;
        if (rr->height >= rl->height) {
          Node *nrl = new Node(left, rl->incref(), value);
          Node *res = new Node(nrl, rr->incref(), right->value);
          right->decref();
          return res;
        } else {
          Node *rll = rl->left;
          Node *rlr = rl->right;
          Node *nrl = new Node(left, rll->incref(), value);
          Node *nrr = new Node(rlr->incref(), rr->incref(), right->value);
          Node *res = new Node(nrl, nrr, rl->value);
          right->decref();
          return res;
        }
      } else {
        return new Node(left, right, value);
      }
    }
  public:
    Node(Node *_left, Node *_right, const value_type &_value)
      : left(_left), right(_right), value(_value), 
        height(std::max(left->height, right->height) + 1), references(1) {
      ++allocated;
    }
    ~Node() {
      left->decref();
      right->decref();
      --allocated;
    }
    void decref() {
      --references;
      if (references==0) delete this;
    }
    Node *incref() {
      ++references;
      return this;
    }
    bool isTerminator() { return this==&terminator; }
    size_t size() {
      if (isTerminator()) {
        return 0;
      } else {
        return left->size() + 1 + right->size();
      }
    }
    Node *popMin(value_type &valueOut) {
      if (left->isTerminator()) {
        valueOut = value;
        return right->incref();
      } else {
        return balance(left->popMin(valueOut), value, right->incref());
      }
    }
    Node *insert(const value_type &v) {
      if (isTerminator()) {
        return new Node(terminator.incref(), terminator.incref(), v);
      } else {
        if (key_compare()(key_of_value()(v), key_of_value()(value))) {
          return balance(left->insert(v), value, right->incref());
        } else if (key_compare()(key_of_value()(value), key_of_value()(v))) {
          return balance(left->incref(), value, right->insert(v));
        } else {
          return incref();
        }
      }
    }
    Node *replace(const value_type &v) {
      if (isTerminator()) {
        return new Node(terminator.incref(), terminator.incref(), v);
      } else {
        if (key_compare()(key_of_value()(v), key_of_value()(value))) {
          return balance(left->replace(v), value, right->incref());
        } else if (key_compare()(key_of_value()(value), key_of_value()(v))) {
          return balance(left->incref(), value, right->replace(v));
        } else {
          return new Node(left->incref(), right->incref(), v);
        }
      }
    }
    Node *remove(const key_type &k) {
      if (isTerminator()) {
        return incref();
      } else {
        if (key_compare()(k, key_of_value()(value))) {
          return balance(left->remove(k), value, right->incref());
        } else if (key_compare()(key_of_value()(value), k)) {
          return balance(left->incref(), value, right->remove(k));
        } else {
          if (left->isTerminator()) {
            return right->incref();
          } else if (right->isTerminator()) {
            return left->incref();
          } else {
            value_type min;
            Node *nr = right->popMin(min);
            return balance(left->incref(), min, nr);
          }
        }
      }
    }
  };
  template<typename T>
  class FixedStack {
    unsigned pos, max;
    T *elts;
  public:
    FixedStack(unsigned _max) : pos(0), max(_max), elts(new T[max]) {}
    FixedStack(const FixedStack &b) : pos(b.pos), max(b.max), elts(new T[b.max]) {
      std::copy(b.elts, b.elts+pos, elts);
    }
    ~FixedStack() { delete[] elts; }
    void push_back(const T &elt) { elts[pos++] = elt; }
    void pop_back() { --pos; }
    bool empty() { return pos==0; }
    T &back() { return elts[pos-1]; }
    FixedStack &operator=(const FixedStack &b) {
      assert(max == b.max); 
      pos = b.pos;
      std::copy(b.elts, b.elts+pos, elts);
      return *this;
    }
    bool operator==(const FixedStack &b) {
      return (pos == b.pos && std::equal(elts, elts+pos, b.elts));
    }
    bool operator!=(const FixedStack &b) { return !(*this==b); }
  };
  template<class K, class V, class KOV, class CMP>
  class ImmutableTree<K,V,KOV,CMP>::iterator {
    friend class ImmutableTree<K,V,KOV,CMP>;
  private:
    Node *root; 
    FixedStack<Node*> stack;
  public:
    iterator(Node *_root, bool atBeginning) : root(_root->incref()), stack(root->height) {
      if (atBeginning) {
        for (Node *n=root; !n->isTerminator(); n=n->left)
          stack.push_back(n);
      }
    }
    iterator(const iterator &i) : root(i.root->incref()), stack(i.stack) { }
    ~iterator() { root->decref(); }
    iterator &operator=(const iterator &b) {
      b.root->incref();
      root->decref();
      root = b.root;
      stack = b.stack;
      return *this;
    }
    const value_type &operator*() {
      Node *n = stack.back();
      return n->value;
    }
    const value_type *operator->() {
      Node *n = stack.back();
      return &n->value;
    }
    bool operator==(const iterator &b) { return stack==b.stack; }
    bool operator!=(const iterator &b) { return stack!=b.stack; }
    iterator &operator--() {
      if (stack.empty()) {
        for (Node *n=root; !n->isTerminator(); n=n->right)
          stack.push_back(n);
      } else {
        Node *n = stack.back();
        if (n->left->isTerminator()) {
          for (;;) {
            Node *prev = n;
            stack.pop_back();
            if (stack.empty()) {
              break;
            } else {
              n = stack.back();
              if (prev==n->right)
                break;
            }
          }
        } else {
          stack.push_back(n->left);
          for (n=n->left->right; !n->isTerminator(); n=n->right)
            stack.push_back(n);
        }
      }
      return *this;
    }
    iterator &operator++() {
      assert(!stack.empty());
      Node *n = stack.back();
      if (n->right->isTerminator()) {
        for (;;) {
          Node *prev = n;
          stack.pop_back();
          if (stack.empty()) {
            break;
          } else {
            n = stack.back();
            if (prev==n->left)
              break;
          }
        }
      } else {
        stack.push_back(n->right);
        for (n=n->right->left; !n->isTerminator(); n=n->left)
          stack.push_back(n);
      }
      return *this;
    }
  };
  /***/
  template<class K, class V, class KOV, class CMP> 
  typename ImmutableTree<K,V,KOV,CMP>::Node 
  ImmutableTree<K,V,KOV,CMP>::Node::terminator;
  template<class K, class V, class KOV, class CMP> 
  size_t ImmutableTree<K,V,KOV,CMP>::allocated = 0;
  template<class V, class D>
  struct _Select1st {
    D &operator()(V &a) const { return a.first; }
    const D &operator()(const V &a) const { return a.first; }
  };
  class MemoryMap {
  public:
    typedef const MemoryObject* key_type;
    typedef std::pair<const MemoryObject*,ObjectHolder> value_type;
    typedef ImmutableTree<const MemoryObject*, value_type, _Select1st<value_type,key_type>, MemoryObjectLT> Tree;
    typedef typename Tree::iterator iterator;
  private:
    Tree elts;
    MemoryMap(const Tree &b): elts(b) {}
  public:
    MemoryMap() {}
    MemoryMap(const MemoryMap &b) : elts(b.elts) {}
    ~MemoryMap() {}
    const value_type *lookup(const key_type &key) const { return elts.lookup(key); }
    const value_type *lookup_previous(const key_type &key) const { return elts.lookup_previous(key); }
    MemoryMap replace(const value_type &value) const { return elts.replace(value); }
    MemoryMap remove(const key_type &key) const { return elts.remove(key); }
    iterator begin() const { return elts.begin(); }
    iterator end() const { return elts.end(); }
    iterator upper_bound(const key_type &key) const { return elts.upper_bound(key); }
  };
}
#endif //jca

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
  typedef ref<Expr> Cell;
  struct KInstruction;
  class PTreeNode;
  class ExecutionState;
  class Executor;
  typedef std::pair<const MemoryObject*, const ObjectState*> ObjectPair;
  typedef std::vector<ObjectPair> ResolutionList;

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
  PTree *processTree;
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
  void branch(ExecutionState &state, const std::vector<ref<Expr>> &conditions, std::vector<ExecutionState*> &result);
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

