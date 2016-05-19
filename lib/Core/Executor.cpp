//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "Executor.h"
#include "CoreStats.h"
#include "ExternalDispatcher.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "klee/Common.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/System/MemoryUsage.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Process.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/CFG.h"
#include "../Module/Passes.h"
#include <cassert>
#include <vector>
#include <string>
#include <set>
#include <unistd.h>

namespace llvm {
  extern void Optimize(Module*);
}

using namespace llvm;
using namespace klee;

static RNG theRNG;

namespace klee {
  struct KFunction {
public:
    llvm::Function *function;
    unsigned numRegisters;
    unsigned numInstructions;
    KInstruction **instructions;
    std::map<llvm::BasicBlock*, unsigned> basicBlockEntry;
  public:
    KFunction(llvm::Function *_function) : function(_function), numInstructions(0), instructions(NULL) {}
    ~KFunction() {
      if (instructions) {
        for (unsigned i=0; i<numInstructions; ++i)
          delete instructions[i];
        delete[] instructions;
      }
    }
  };
  class KConstant {
  public:
    llvm::Constant* ct;
    unsigned id;
    KInstruction *ki;
    KConstant(llvm::Constant* _ct, unsigned _id, KInstruction* _ki): ct(_ct), id(_id), ki(_ki) {}
  };

class Searcher {
public:
  virtual ~Searcher() {}
  virtual ExecutionState &selectState() = 0;
  virtual void update(ExecutionState *current, const std::set<ExecutionState*> &addedStates, const std::set<ExecutionState*> &removedStates) = 0;
  virtual bool empty() = 0;
  enum CoreSearchType { DFS, BFS };
};

class PTreeNode {
    friend class PTree;
public:
    PTreeNode *parent, *left, *right;
    ExecutionState *data;
    ref<Expr> condition;
private:
    PTreeNode(PTreeNode *_parent, ExecutionState *_data)
      : parent(_parent), left(0), right(0), data(_data), condition(0) { }
    ~PTreeNode() { }
};
class PTree {
    typedef ExecutionState* data_type;
public:
    PTreeNode *root;
    PTree(const data_type &_root) : root(new PTreeNode(0,_root)) { }
    ~PTree() {}
    std::pair<PTreeNode*,PTreeNode*> split(PTreeNode *n, const data_type &leftData, const data_type &rightData) {
      assert(n && !n->left && !n->right);
      n->left = new PTreeNode(n, leftData);
      n->right = new PTreeNode(n, rightData);
      return std::make_pair(n->left, n->right);
    }
    void remove(PTreeNode *n) {
      assert(!n->left && !n->right);
      do {
        PTreeNode *p = n->parent;
        delete n;
        if (p) {
          if (n == p->left)
            p->left = 0;
          else {
            assert(n == p->right);
            p->right = 0;
          }
        }
        n = p;
      } while (n && !n->left && !n->right);
    }
};
} // namespace klee

namespace {
  cl::list<Searcher::CoreSearchType>
  CoreSearch("search", cl::desc("Specify the search heuristic (default=random-path interleaved with nurs:covnew)"),
     cl::values(clEnumValN(Searcher::DFS, "dfs", "use Depth First Search (DFS)"),
	clEnumValN(Searcher::BFS, "bfs", "use Breadth First Search (BFS)"), clEnumValEnd));
  cl::opt<Executor::SwitchImplType>
  SwitchType("switch-type", cl::desc("Select the implementation of switch"),
     cl::values(clEnumValN(Executor::eSwitchTypeSimple, "simple", "lower to ordered branches"),
                clEnumValN(Executor::eSwitchTypeLLVM, "llvm", "lower using LLVM"),
                clEnumValN(Executor::eSwitchTypeInternal, "internal", "execute switch internally"),
                clEnumValEnd),
        cl::init(Executor::eSwitchTypeInternal));
}

class DFSSearcher : public Searcher {
  std::vector<ExecutionState*> states;
public:
  ExecutionState &selectState() { return *states.back(); }
  void update(ExecutionState *current, const std::set<ExecutionState*> &addedStates, const std::set<ExecutionState*> &removedStates) {
    states.insert(states.end(), addedStates.begin(), addedStates.end());
    for (auto it = removedStates.begin(), ie = removedStates.end(); it != ie; ++it) {
      ExecutionState *es = *it;
      if (es == states.back())
        states.pop_back();
      else {
        bool ok = false;
        for (auto it = states.begin(), ie = states.end(); it != ie; ++it) {
          if (es==*it) {
            states.erase(it);
            ok = true;
            break;
          }
        }
        assert(ok && "invalid state removed");
      }
    }
  }
  bool empty() { return states.empty(); }
};
class BFSSearcher : public Searcher {
  std::deque<ExecutionState*> states;
public:
  ExecutionState &selectState() { return *states.front(); }
  void update(ExecutionState *current, const std::set<ExecutionState*> &addedStates, const std::set<ExecutionState*> &removedStates) {
    states.insert(states.end(), addedStates.begin(), addedStates.end());
    for (auto it = removedStates.begin(), ie = removedStates.end(); it != ie; ++it) {
      ExecutionState *es = *it;
      if (es == states.front())
        states.pop_front();
      else {
        bool ok = false;
        for (auto it = states.begin(), ie = states.end(); it != ie; ++it) {
          if (es==*it) {
            states.erase(it);
            ok = true;
            break;
          }
        }
        assert(ok && "invalid state removed");
      }
    }
  }
  bool empty() { return states.empty(); }
};

void ExecutionState::bindObject(const MemoryObject *mo, ObjectState *os) {
  assert(os->copyOnWriteOwner==0 && "object already has owner");
  os->copyOnWriteOwner = cowKey;
  objects = objects.replace(std::make_pair(mo, os));
}

void ExecutionState::unbindObject(const MemoryObject *mo) {
  objects = objects.remove(mo);
}

const ObjectState *ExecutionState::findObject(const MemoryObject *mo) const {
  const MemoryMap::value_type *res = objects.lookup(mo);
  return res ? res->second : 0;
}

ObjectState *ExecutionState::getWriteable(const MemoryObject *mo, const ObjectState *os) {
  assert(!os->readOnly);
  if (cowKey==os->copyOnWriteOwner)
    return const_cast<ObjectState*>(os);
  else {
    ObjectState *n = new ObjectState(*os);
    n->copyOnWriteOwner = cowKey;
    objects = objects.replace(std::make_pair(mo, n));
    return n;
  }
}

bool ExecutionState::resolveOne(const ref<ConstantExpr> &addr, ObjectPair &result) {
  uint64_t address = addr->getZExtValue();
  MemoryObject hack(address);
  if (const MemoryMap::value_type *res = objects.lookup_previous(&hack)) {
    const MemoryObject *mo = res->first;
    if ((mo->size==0 && address==mo->address) || (address - mo->address < mo->size)) {
      result = *res;
      return true;
    }
  }
  return false;
}

bool Executor::resolve(ExecutionState &state, ref<Expr> p, ResolutionList &rl, unsigned maxResolutions, double timeout) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(p)) {
    ObjectPair res;
    if (state.resolveOne(CE, res))
      rl.push_back(res);
    return false;
  } else {
    TimerStatIncrementer timer(stats::resolveTime);
    uint64_t timeout_us = (uint64_t) (timeout*1000000.);
    // XXX in general this isn't exactly what we want... for
    // a multiple resolution case (or for example, a \in {b,c,0})
    // we want to find the first object, find a cex assuming
    // not the first, find a cex assuming not the second...  etc.
    // XXX how do we smartly amortize the cost of checking to
    // see if we need to keep searching up/down, in bad cases?
    // maybe we don't care?
    // XXX we really just need a smart place to start (although
    // if its a known solution then the code below is guaranteed
    // to hit the fast path with exactly 2 queries). we could also
    // just get this by inspection of the expr.
    ref<ConstantExpr> cex;
    if (!solveGetValue(state, p, cex))
      return true;
    uint64_t example = cex->getZExtValue();
    MemoryObject hack(example);
    MemoryMap::iterator oi = state.objects.upper_bound(&hack);
    MemoryMap::iterator begin = state.objects.begin();
    MemoryMap::iterator end = state.objects.end();
    MemoryMap::iterator start = oi;
    // XXX in the common case we can save one query if we ask
    // mustBeTrue before mayBeTrue for the first result. easy
    // to add I just want to have a nice symbolic test case first.
    // search backwards, start with one minus because this
    // is the object that p *should* be within, which means we
    // get write off the end with 4 queries (XXX can be better, no?)
    while (oi!=begin) {
      --oi;
      const MemoryObject *mo = oi->first;
      if (timeout_us && timeout_us < timer.check())
        return true;
      // XXX I think there is some query wasteage here?
      ref<Expr> inBounds = mo->getBoundsCheckPointer(p);
      bool mayBeTruef;
      if (!mayBeTrue(state, inBounds, mayBeTruef))
        return true;
      if (mayBeTruef) {
        rl.push_back(*oi);
        // fast path check
        unsigned size = rl.size();
        if (size==1) {
          bool mustBeTruef;
          if (!mustBeTrue(state, inBounds, mustBeTruef))
            return true;
          if (mustBeTruef)
            return false;
        } else if (size==maxResolutions) {
          return true;
        }
      }
      bool mustBeTruef;
      if (!mustBeTrue(state, UgeExpr::create(p, mo->getBaseExpr()), mustBeTruef))
        return true;
      if (mustBeTruef)
        break;
    }
    // search forwards
    for (oi=start; oi!=end; ++oi) {
      const MemoryObject *mo = oi->first;
      if (timeout_us && timeout_us < timer.check())
        return true;
      bool mustBeTruef;
      if (!mustBeTrue(state, UltExpr::create(p, mo->getBaseExpr()), mustBeTruef))
        return true;
      if (mustBeTruef)
        break;
      // XXX I think there is some query wasteage here?
      ref<Expr> inBounds = mo->getBoundsCheckPointer(p);
      bool mayBeTruef;
      if (!mayBeTrue(state, inBounds, mayBeTruef))
        return true;
      if (mayBeTruef) {
        rl.push_back(*oi);
        // fast path check
        unsigned size = rl.size();
        if (size==1) {
          bool mustBeTruef;
          if (!mustBeTrue(state, inBounds, mustBeTruef))
            return true;
          if (mustBeTruef)
            return false;
        } else if (size==maxResolutions) {
          return true;
        }
      }
    }
  }
  return false;
}

// These two are pretty big hack so we can sort of pass memory back
// and forth to externals. They work by abusing the concrete cache
// store inside of the object states, which allows them to
// transparently avoid screwing up symbolics (if the byte is symbolic
// then its concrete cache byte isn't being used) but is just a hack.
void ExecutionState::copyOutConcretes() {
  for (MemoryMap::iterator it = objects.begin(), ie = objects.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first;
    if (!mo->isUserSpecified) {
      ObjectState *os = it->second;
      uint8_t *address = (uint8_t*) (unsigned long) mo->address;
      if (!os->readOnly)
        memcpy(address, os->concreteStore, mo->size);
    }
  }
}

bool ExecutionState::copyInConcretes() {
  for (MemoryMap::iterator it = objects.begin(), ie = objects.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first;
    if (!mo->isUserSpecified) {
      const ObjectState *os = it->second;
      uint8_t *address = (uint8_t*) (unsigned long) mo->address;
      if (memcmp(address, os->concreteStore, mo->size)!=0) {
        if (os->readOnly)
          return false;
        else {
          ObjectState *wos = getWriteable(mo, os);
          memcpy(wos->concreteStore, address, mo->size);
        }
      }
    }
  }
  return true;
}

bool MemoryObjectLT::operator()(const MemoryObject *a, const MemoryObject *b) const {
  return a->address < b->address;
}

/// Check for special cases where we statically know an instruction is
/// uncoverable. Currently the case is an unreachable instruction
/// following a noreturn call; the instruction is really only there to
/// satisfy LLVM's termination requirement.
static bool instructionIsCoverable(Instruction *i) {
  if (i->getOpcode() == Instruction::Unreachable) {
    BasicBlock *bb = i->getParent();
    BasicBlock::iterator it(i);
    if (it != bb->begin()) {
      Instruction *prev = --it;
      if (isa<CallInst>(prev) || isa<InvokeInst>(prev)) {
        CallSite cs(prev);
        Function *target = getDirectCallTarget(cs);
        if (target && target->doesNotReturn())
          return false;
      }
    }
  }
  return true;
}

void Executor::writeStatsLine() {
  llvm::outs() << "(" << stats::instructions << "," << fullBranches << "," << partialBranches
       << "," << numBranches << "," << util::getUserTime() << "," << states.size()
       << "," << util::GetTotalMallocUsage() << "," << stats::queries << "," << stats::queryConstructs
       << "," << 0 << "," << (util::getWallTime() - startWallTime) << "," << stats::coveredInstructions
       << "," << stats::uncoveredInstructions << "," << stats::queryTime / 1000000.
       << "," << stats::solverTime / 1000000.  << "," << stats::cexCacheTime / 1000000.
       << "," << stats::forkTime / 1000000.  << "," << stats::resolveTime / 1000000.
#ifdef DEBUG
       << "," << stats::arrayHashTime / 1000000.
#endif
       << ")\n";
}

unsigned Executor::getPathStreamID(const ExecutionState &state) {
  assert(pathWriter);
  return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
  assert(symPathWriter);
  return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res, Interpreter::LogType logFormat) {
  std::ostringstream info;
  switch (logFormat) {
  case STP: {
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    char *log = osolver->getConstraintLog(query);
    res = std::string(log);
    free(log);
  } break;
  case KQUERY: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprPPrinter::printConstraints(info, state.constraints);
    res = info.str();
  } break;
  case SMTLIB2: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprSMTLIBPrinter printer;
    printer.setOutput(info);
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    printer.setQuery(query);
    printer.generateOutput();
    res = info.str();
  } break;
  default:
    klee_warning("Executor::getConstraintLog() : Log format not supported!");
  }
}

bool Executor::getSymbolicSolution(const ExecutionState &state, std::vector<std::pair<std::string, std::vector<unsigned char>>> &res){
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
  osolver->setCoreSolverTimeout(0);
  ExecutionState tmp(state);
  // Go through each byte in every test case and attempt to restrict
  // it to the constraints contained in cexPreferences.  (Note:
  // usually this means trying to make it an ASCII character (0-127)
  // and therefore human readable. It is also possible to customize
  // the preferred constraints.  See test/Features/PreferCex.c for
  // an example) While this process can be very expensive, it can
  // also make understanding individual test cases much easier.
  for (unsigned i = 0; i != state.symbolics.size(); ++i) {
    const MemoryObject *mo = state.symbolics[i].first;
    auto pi = mo->cexPreferences.begin(), pie = mo->cexPreferences.end();
    for (; pi != pie; ++pi) {
      bool lmustBeTrue;
      // Attempt to bound byte to constraints held in cexPreferences
      bool success = mustBeTrue(tmp, Expr::createIsZero(*pi), lmustBeTrue);
      // If it isn't possible to constrain this particular byte in the desired
      // way (normally this would mean that the byte can't be constrained to
      // be between 0 and 127 without making the entire constraint list UNSAT)
      // then just continue on to the next byte.
      if (!success) break;
      // If the particular constraint operated on in this iteration through
      // the loop isn't implied then add it to the list of constraints.
      if (!lmustBeTrue) tmp.addConstraint(*pi);
    }
    if (pi!=pie) break;
  }
  std::vector< std::vector<unsigned char>> values;
  std::vector<const Array*> objects;
  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    objects.push_back(state.symbolics[i].second);
  bool success = true;
  if (!objects.empty()) {
      sys::TimeValue now = util::getWallTimeVal();
      success = osolver->getInitialValues(Query(tmp.constraints, ConstantExpr::alloc(0, Expr::Bool)), objects, values);
      stats::solverTime += (util::getWallTimeVal() - now).usec();
  }
  osolver->setCoreSolverTimeout(0);
  if (!success) {
    klee_warning("unable to compute initial values (invalid constraints?)!");
    ExprPPrinter::printQuery(llvm::errs(), state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    return false;
  }
  for (unsigned i = 0; i != state.symbolics.size(); ++i) {
printf("[%s:%d] name %s val \n", __FUNCTION__, __LINE__, state.symbolics[i].first->name.c_str()); //, values[i]);
    res.push_back(std::make_pair(state.symbolics[i].first->name, values[i]));
  }
  return true;
}

Executor::StatePair
Executor::stateFork(ExecutionState &current, ref<Expr> condition, bool isInternal) {
  Solver::Validity res;
  auto it = seedMap.find(&current);
  osolver->setCoreSolverTimeout(0);
  sys::TimeValue now = util::getWallTimeVal();
  bool success = osolver->evaluate(Query(current.constraints, current.constraints.simplifyExpr(condition)), res);
  stats::solverTime += (util::getWallTimeVal() - now).usec();
  if (!success) {
    current.pc = current.prevPC;
    terminateStateEarly(current, "Query timed out (fork).");
    return StatePair(0, 0);
  }

  // XXX - even if the constraint is provable one way or the other we can probably benefit by adding this constraint and allowing it to
  // reduce the other constraints. For example, if we do a binary search on a particular value, and then see a comparison against
  // the value it has been fixed at, we should take this as a nice hint to just use the single constraint instead of all the binary
  // search ones. If that makes sense.
  if (res==Solver::True) {
    if (!isInternal && pathWriter)
        current.pathOS << "1";
    return StatePair(&current, 0);
  } else if (res==Solver::False) {
    if (!isInternal && pathWriter)
        current.pathOS << "0";
    return StatePair(0, &current);
  }
  TimerStatIncrementer timer(stats::forkTime);
  ExecutionState *falseState, *trueState = &current;
  ++stats::forks;
  falseState = trueState->branch();
  addedStates.insert(falseState);
  if (it != seedMap.end()) {
    std::vector<SeedInfo> seeds = it->second;
    it->second.clear();
    std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
    std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
    for (auto siit = seeds.begin(), siie = seeds.end(); siit != siie; ++siit) {
      ref<ConstantExpr> res;
      bool success = solveGetValue(current, siit->assignment.evaluate(condition), res);
      assert(success && "FIXME: Unhandled solver failure");
      if (res->isTrue())
        trueSeeds.push_back(*siit);
      else
        falseSeeds.push_back(*siit);
    }
    bool swapInfo = false;
    if (trueSeeds.empty()) {
      if (&current == trueState) swapInfo = true;
      seedMap.erase(trueState);
    }
    if (falseSeeds.empty()) {
      if (&current == falseState) swapInfo = true;
      seedMap.erase(falseState);
    }
    if (swapInfo) {
      std::swap(trueState->coveredNew, falseState->coveredNew);
      std::swap(trueState->coveredLines, falseState->coveredLines);
    }
  }
  current.ptreeNode->data = 0;
  std::pair<PTreeNode*, PTreeNode*> res2 = processTree->split(current.ptreeNode, falseState, trueState);
  falseState->ptreeNode = res2.first;
  trueState->ptreeNode = res2.second;
  if (!isInternal) {
    if (pathWriter) {
      falseState->pathOS = pathWriter->open(current.pathOS);
      trueState->pathOS << "1";
      falseState->pathOS << "0";
    }
    if (symPathWriter) {
      falseState->symPathOS = symPathWriter->open(current.symPathOS);
      trueState->symPathOS << "1";
      falseState->symPathOS << "0";
    }
  }
  executeAddConstraint(*trueState, condition);
  executeAddConstraint(*falseState, Expr::createIsZero(condition));
  return StatePair(trueState, falseState);
}

std::pair<ref<Expr>, ref<Expr>>
Executor::solveGetRange(const ExecutionState& state, ref<Expr> expr) const {
  return osolver->getRange(Query(state.constraints, expr));
}

bool Executor::mustBeTrue(const ExecutionState& state, ref<Expr> expr, bool &result) {
  sys::TimeValue now = util::getWallTimeVal();
  expr = state.constraints.simplifyExpr(expr);
  bool success = osolver->mustBeTrue(Query(state.constraints, expr), result);
  stats::solverTime += (util::getWallTimeVal() - now).usec();
  return success;
}

bool Executor::solveGetValue(const ExecutionState& state, ref<Expr> expr, ref<ConstantExpr> &result) {
  sys::TimeValue now = util::getWallTimeVal();
  expr = state.constraints.simplifyExpr(expr);
  bool success = osolver->getValue(Query(state.constraints, expr), result);
  stats::solverTime += (util::getWallTimeVal() - now).usec();
  return success;
}

Interpreter *Interpreter::create(const InterpreterOptions &opts, InterpreterHandler *ih) {
  return new Executor(opts, ih);
}

Executor::Executor(const InterpreterOptions &opts, InterpreterHandler *ih)
  : Interpreter(opts),
    interpreterHandler(ih),
    processTree(0),
    module(0),
    externalDispatcher(new ExternalDispatcher()),
    pathWriter(0),
    symPathWriter(0),
    specialFunctionHandler(0) {
printf("[%s:%d] constructor \n", __FUNCTION__, __LINE__);
  Solver *coreSolver = klee::createCoreSolver(CoreSolverToUse);
  if (!coreSolver) {
    llvm::errs() << "Failed to create core solver\n";
    exit(1);
  }
  osolver = constructSolverChain( coreSolver,
      interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(ALL_QUERIES_PC_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_PC_FILE_NAME));
  memory = new MemoryManager(&arrayCache);
}

Executor::~Executor() {
  delete memory;
  delete externalDispatcher;
  if (processTree)
    delete processTree;
  if (specialFunctionHandler)
    delete specialFunctionHandler;
  for (auto it=constantMap.begin(), itE=constantMap.end(); it!=itE;++it)
    delete it->second;
  delete targetData;
}

/***/
void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os, const Constant *c, unsigned offset) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
  if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
    unsigned elementSize = targetData->getTypeStoreSize(cp->getType()->getElementType());
    for (unsigned i=0, e=cp->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cp->getOperand(i), offset + i*elementSize);
  } else if (isa<ConstantAggregateZero>(c)) {
    unsigned i, size = targetData->getTypeStoreSize(c->getType());
    for (i=0; i<size; i++)
      os->write8(offset+i, (uint8_t) 0);
  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
    unsigned elementSize = targetData->getTypeStoreSize(ca->getType()->getElementType());
    for (unsigned i=0, e=ca->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, ca->getOperand(i), offset + i*elementSize);
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
    const StructLayout *sl = targetData->getStructLayout(cast<StructType>(cs->getType()));
    for (unsigned i=0, e=cs->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cs->getOperand(i), offset + sl->getElementOffset(i));
  } else if (const ConstantDataSequential *cds = dyn_cast<ConstantDataSequential>(c)) {
    unsigned elementSize = targetData->getTypeStoreSize(cds->getElementType());
    for (unsigned i=0, e=cds->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, cds->getElementAsConstant(i), offset + i*elementSize);
  } else if (!isa<UndefValue>(c)) {
    unsigned StoreBits = targetData->getTypeStoreSizeInBits(c->getType());
    ref<ConstantExpr> C = evalConstant(c);
    // Extend the constant if necessary;
    assert(StoreBits >= C->getWidth() && "Invalid store size!");
    if (StoreBits > C->getWidth())
      C = C->ZExt(StoreBits);
    os->write(offset, C);
  }
}

MemoryObject * Executor::addExternalObject(ExecutionState &state, void *addr, unsigned size, bool isReadOnly) {
  MemoryObject *mo = memory->allocateFixed((uint64_t) (unsigned long) addr, size, 0);
  ObjectState *os = bindObjectInState(state, mo, false);
  for(unsigned i = 0; i < size; i++)
    os->write8(i, ((uint8_t*)addr)[i]);
  if(isReadOnly)
    os->setReadOnly(true);
  return mo;
}

void Executor::initializeGlobals(ExecutionState &state) {
  Module *m = module;
  // represent function globals using the address of the actual llvm function
  // object. given that we use malloc to allocate memory in states this also
  // ensures that we won't conflict. we don't need to allocate a memory object
  // since reading/writing via a function pointer is unsupported anyway.
  for (auto i = m->begin(), ie = m->end(); i != ie; ++i) {
    ref<ConstantExpr> addr(0);
    addr = Expr::createPointer((unsigned long) (void*) i);
    legalFunctions.insert((uint64_t) (unsigned long) (void*) i);
    globalAddresses.insert(std::make_pair(i, addr));
  }

  // allocate and initialize globals, done in two passes since we may
  // need address of a global in order to initialize some other one.
  // allocate memory objects for all globals
  for (auto i = m->global_begin(), e = m->global_end(); i != e; ++i) {
    LLVM_TYPE_Q Type *ty = i->getType()->getElementType();
    uint64_t size = targetData->getTypeStoreSize(ty);
    MemoryObject *mo = memory->allocate(size, false, true, i);
    ObjectState *os = bindObjectInState(state, mo, false);
    globalObjects.insert(std::make_pair(i, mo));
    globalAddresses.insert(std::make_pair(i, mo->getBaseExpr()));
    if (i->isDeclaration()) {
      // Program already running = object already initialized.  Read // concrete value and write it to our copy.
      if (size == 0)
        llvm::errs() << "Unable to find size for global variable: " << i->getName() << " (use will result in out of bounds access)\n";
      else {
        unsigned char *addr = (unsigned char *)externalDispatcher->resolveSymbol(i->getName());
        if (!addr)
          klee_error("unable to load symbol(%s) while initializing globals.", i->getName().data());
        for (unsigned offset=0; offset<mo->size; offset++)
          os->write8(offset, addr[offset]);
      }
    }
    else if (!i->hasInitializer())
        os->initializeToRandom();
  }
  // once all objects are allocated, do the actual initialization
  for (auto i = m->global_begin(), e = m->global_end(); i != e; ++i) {
    if (i->hasInitializer()) {
      MemoryObject *mo = globalObjects.find(i)->second;
      const ObjectState *os = state.findObject(mo);
      assert(os);
      ObjectState *wos = state.getWriteable(mo, os);
      initializeGlobalObject(state, wos, i->getInitializer(), 0);
    }
  }
}

void Executor::branch(ExecutionState &state, const std::vector<ref<Expr>> &conditions, std::vector<ExecutionState*> &result) {
  TimerStatIncrementer timer(stats::forkTime);
  unsigned N = conditions.size();
  assert(N);
    stats::forks += N-1;
    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i=1; i<N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      addedStates.insert(ns);
      result.push_back(ns);
      es->ptreeNode->data = 0;
      std::pair<PTreeNode*,PTreeNode*> res = processTree->split(es->ptreeNode, ns, es);
      ns->ptreeNode = res.first;
      es->ptreeNode = res.second;
    }
  // redistribute seeds to match conditions, killing states if necessary (inefficient but simple).
  auto it = seedMap.find(&state);
  if (it != seedMap.end()) {
    std::vector<SeedInfo> seeds = it->second;
    seedMap.erase(it);
    // Assume each seed only satisfies one condition (necessarily true
    // when conditions are mutually exclusive and their conjunction is // a tautology).
    for (auto siit = seeds.begin(), siie = seeds.end(); siit != siie; ++siit) {
      unsigned i;
      for (i=0; i<N; ++i) {
        ref<ConstantExpr> res;
        bool success = solveGetValue(state, siit->assignment.evaluate(conditions[i]), res);
        assert(success && "FIXME: Unhandled solver failure");
        if (res->isTrue())
          break;
      }
      // If we didn't find a satisfying condition randomly pick one // (the seed will be patched).
      if (i==N)
        i = theRNG.getInt32() % N;
      // Extra check in case we're replaying seeds with a max-fork
      if (result[i])
        seedMap[result[i]].push_back(*siit);
    }
  }
  for (unsigned i=0; i<N; ++i)
      if (result[i])
          executeAddConstraint(*result[i], conditions[i]);
}

void Executor::executeAddConstraint(ExecutionState &state, ref<Expr> condition) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }
  // Check to see if this constraint violates seeds.
  auto it = seedMap.find(&state);
  if (it != seedMap.end()) {
    bool warn = false;
    for (auto siit = it->second.begin(), siie = it->second.end(); siit != siie; ++siit) {
      bool res;
      bool success = mustBeFalse(state, siit->assignment.evaluate(condition), res);
      assert(success && "FIXME: Unhandled solver failure");
      if (res) {
        siit->patchSeed(state, condition, this);
        warn = true;
      }
    }
    if (warn)
      klee_warning("seeds patched for violating constraint");
  }
  state.addConstraint(condition);
}

ref<klee::ConstantExpr> Executor::evalConstant(const Constant *c) {
  std::vector<ref<Expr>> kids;
  if (const llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c))
      return evalConstantExpr(ce);
  else if (const ConstantInt *ci = dyn_cast<ConstantInt>(c))
      return ConstantExpr::alloc(ci->getValue());
  else if (const ConstantFP *cf = dyn_cast<ConstantFP>(c))
      return ConstantExpr::alloc(cf->getValueAPF().bitcastToAPInt());
  else if (const GlobalValue *gv = dyn_cast<GlobalValue>(c))
      return globalAddresses.find(gv)->second;
  else if (isa<ConstantPointerNull>(c))
      return Expr::createPointer(0);
  else if (isa<UndefValue>(c) || isa<ConstantAggregateZero>(c))
      return ConstantExpr::create(0, getWidthForLLVMType(c->getType()));
  else if (const ConstantDataSequential *cds = dyn_cast<ConstantDataSequential>(c)) {
      for (unsigned i = 0, e = cds->getNumElements(); i != e; ++i)
        kids.push_back(evalConstant(cds->getElementAsConstant(i)));
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
      const StructLayout *sl = targetData->getStructLayout(cs->getType());
      for (unsigned i = cs->getNumOperands(); i != 0; --i) {
        unsigned op = i-1;
        uint64_t thisOffset = sl->getElementOffsetInBits(op),
           nextOffset = (op == cs->getNumOperands() - 1) ? sl->getSizeInBits() : sl->getElementOffsetInBits(op+1);
        ref<Expr> kid = evalConstant(cs->getOperand(op));
        if (nextOffset-thisOffset > kid->getWidth()) {
          uint64_t paddingWidth = nextOffset-thisOffset-kid->getWidth();
          kids.push_back(ConstantExpr::create(0, paddingWidth));
        }
        kids.push_back(kid);
      }
  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)){
      for (unsigned i = ca->getNumOperands(); i != 0; --i)
        kids.push_back(evalConstant(ca->getOperand(i - 1)));
  }
  else
      llvm::report_fatal_error("invalid argument to evalConstant()");
  ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
  return cast<ConstantExpr>(res);
}

ref<Expr> Executor::toUnique(const ExecutionState &state, ref<Expr> &e) {
  ref<Expr> result = e;
  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    osolver->setCoreSolverTimeout(0);
    if (solveGetValue(state, e, value)
     && mustBeTrue(state, EqExpr::create(e, value), isTrue) && isTrue)
      result = value;
    osolver->setCoreSolverTimeout(0);
  }
  return result;
}

/* Concretize the given expression, and return a possible constant value.
   'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr>
Executor::toConstant(ExecutionState &state, ref<Expr> e, const char *reason) {
  e = state.constraints.simplifyExpr(e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;
  ref<ConstantExpr> value;
  bool success = solveGetValue(state, e, value);
  assert(success && "FIXME: Unhandled solver failure");
  std::string str;
  llvm::raw_string_ostream os(str);
  os << "silently concretizing (reason: " << reason << ") expression " << e << " to value " << value;
  klee_warning(reason, os.str().c_str());
  executeAddConstraint(state, EqExpr::create(e, value));
  return value;
}

void Executor::executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target) {
  e = state.constraints.simplifyExpr(e);
  auto it = seedMap.find(&state);
  if (it==seedMap.end() || isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool success = solveGetValue(state, e, value);
    assert(success && "FIXME: Unhandled solver failure");
    bindLocal(target, state, value);
  } else {
    std::set<ref<Expr>> values;
    for (auto siit = it->second.begin(), siie = it->second.end(); siit != siie; ++siit) {
      ref<ConstantExpr> value;
      bool success = solveGetValue(state, siit->assignment.evaluate(e), value);
      assert(success && "FIXME: Unhandled solver failure");
      values.insert(value);
    }
    std::vector<ref<Expr>> conditions;
    for (auto vit = values.begin(), vie = values.end(); vit != vie; ++vit)
      conditions.push_back(EqExpr::create(e, *vit));
    std::vector<ExecutionState*> branches;
    branch(state, conditions, branches);
    auto bit = branches.begin();
    for (auto vit = values.begin(), vie = values.end(); vit != vie; ++vit) {
      ExecutionState *es = *bit;
      if (es)
        bindLocal(target, *es, *vit);
      ++bit;
    }
  }
}

// XXX shoot me
static const char *okExternalsList[] = { "printf", "fprintf", "puts", "getpid" };
static std::set<std::string> okExternals(okExternalsList, okExternalsList + (sizeof(okExternalsList)/sizeof(okExternalsList[0])));

void Executor::executeCall(ExecutionState &state, KInstruction *ki, Function *f, std::vector<ref<Expr>> &arguments) {
  Instruction *i = ki->inst;
  if (f && f->isDeclaration()) {
    switch(f->getIntrinsicID()) {
      // state may be destroyed by this call, cannot touch
    case Intrinsic::not_intrinsic: {
      Function *function = f;
      if (specialFunctionHandler->handle(state, function, ki, arguments))
        break;
      // normal external function handling path
      // allocate 128 bits for each argument (+return value) to support fp80's;
      // we could iterate through all the arguments first and determine the exact
      // size we need, but this is faster, and the memory usage isn't significant.
      uint64_t *args = (uint64_t*) alloca(2*sizeof(*args) * (arguments.size() + 1));
      memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
      unsigned wordIndex = 2;
      for (auto ai = arguments.begin(), ae = arguments.end(); ai!=ae; ++ai) {
          ref<Expr> arg = toUnique(state, *ai);
          if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
            // XXX kick toMemory fns from here
            ce->toMemory(&args[wordIndex]);
            wordIndex += (ce->getWidth()+63)/64;
          } else {
            terminateStateOnExecError(state, "external call with symbolic argument: " + function->getName());
            goto overlab;
          }
      }
      state.copyOutConcretes();
    printf("[%s:%d] lib/Core/Executor.cpp \n", __FUNCTION__, __LINE__);
      std::string TmpStr;
      llvm::raw_string_ostream messageOs(TmpStr);
      messageOs << "calling external: " << function->getName().str() << "(";
      for (unsigned i=0; i<arguments.size(); i++) {
          messageOs << arguments[i];
          if (i != arguments.size()-1)
	    messageOs << ", ";
      }
      messageOs << ")";
      klee_warning("%s", messageOs.str().c_str());
      // MCJIT needs unique module, so we create quick external dispatcher for call.
      // reference: // http://blog.llvm.org/2013/07/using-mcjit-with-kaleidoscope-tutorial.html
      ExternalDispatcher *e = new ExternalDispatcher();
      bool success = e->executeCall(function, ki->inst, args);
      delete e;
      if (!success)
          terminateStateOnError(state, "failed external call: " + function->getName(), "external.err");
      else if (!state.copyInConcretes())
          terminateStateOnError(state, "external modified read-only object", "external.err");
      else {
          LLVM_TYPE_Q Type *resultType = ki->inst->getType();
          if (resultType != Type::getVoidTy(getGlobalContext())) {
            ref<Expr> e = ConstantExpr::fromMemory((void*) args, getWidthForLLVMType(resultType));
            bindLocal(ki, state, e);
          }
      }
    }
overlab:
      break;
      // va_arg is handled by caller and intrinsic lowering, see comment for // ExecutionState::varargs
    case Intrinsic::vastart:  {
      StackFrame &sf = state.stack.back();
      assert(sf.varargs && "vastart called in function with no vararg object");
      // FIXME: This is really specific to the architecture, not the pointer
      // size. This happens to work fir x86-32 and x86-64, however.
      Expr::Width WordSize = Context::get().getPointerWidth();
      if (WordSize == Expr::Int32) {
        executeMemoryOperation(state, true, arguments[0], sf.varargs->getBaseExpr(), 0);
      } else {
        assert(WordSize == Expr::Int64 && "Unknown word size!");
        // X86-64 has quite complicated calling convention. However,
        // instead of implementing it, we can do a simple hack: just
        // make a function believe that all varargs are on stack.
        executeMemoryOperation(state, true, arguments[0], ConstantExpr::create(48, 32), 0); // gp_offset
        executeMemoryOperation(state, true, AddExpr::create(arguments[0], ConstantExpr::create(4, 64)),
              ConstantExpr::create(304, 32), 0); // fp_offset
        executeMemoryOperation(state, true, AddExpr::create(arguments[0], ConstantExpr::create(8, 64)),
              sf.varargs->getBaseExpr(), 0); // overflow_arg_area
        executeMemoryOperation(state, true, AddExpr::create(arguments[0], ConstantExpr::create(16, 64)),
              ConstantExpr::create(0, 64), 0); // reg_save_area
      }
      break;
    }
    case Intrinsic::vaend: // va_end is a noop for the interpreter.
      // FIXME: We should validate that the target didn't do something bad
      // with vaeend, however (like call it twice).
      break;
    case Intrinsic::vacopy: // va_copy should have been lowered.
      // FIXME: It would be nice to check for errors in the usage of this as // well.
    default:
      klee_error("unknown intrinsic: %s", f->getName().data());
    }
    if (InvokeInst *ii = dyn_cast<InvokeInst>(i))
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
  } else {
    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = functionMap[f];
    state.pushFrame(state.prevPC, kf->function, kf->numRegisters);
    state.pc = kf->instructions;
     // TODO: support "byval" parameter attribute
     // TODO: support zeroext, signext, sret attributes
    unsigned callingArgs = arguments.size(), funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs)
        klee_warning_once(f, "calling %s with extra arguments.", f->getName().data());
      else if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments", "user.err");
        return;
      }
    } else {
      Expr::Width WordSize = Context::get().getPointerWidth();
      if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments", "user.err");
        return;
      }
      StackFrame &sf = state.stack.back();
      unsigned size = 0;
      for (unsigned i = funcArgs; i < callingArgs; i++) {
        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work fir x86-32 and x86-64, however.
        if (WordSize == Expr::Int32)
          size += Expr::getMinBytesForWidth(arguments[i]->getWidth());
        else {
          Expr::Width argWidth = arguments[i]->getWidth();
          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a 16
          // byte boundary if alignment needed by type exceeds 8 byte boundary.  //
          // Alignment requirements for scalar types is the same as their size
          if (argWidth > Expr::Int64)
             size = llvm::RoundUpToAlignment(size, 16);
          size += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
        }
      }
      MemoryObject *mo = sf.varargs = memory->allocate(size, true, false, state.prevPC->inst);
      if ((WordSize == Expr::Int64) && (mo->address & 15))
        klee_warning_once(0, "While allocating varargs: malloc did not align to 16 bytes.");
      ObjectState *os = bindObjectInState(state, mo, true);
      unsigned offset = 0;
      for (unsigned i = funcArgs; i < callingArgs; i++) {
        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work fir x86-32 and x86-64, however.
        if (WordSize == Expr::Int32) {
          os->write(offset, arguments[i]);
          offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
        } else {
          assert(WordSize == Expr::Int64 && "Unknown word size!");
          Expr::Width argWidth = arguments[i]->getWidth();
          if (argWidth > Expr::Int64)
             offset = llvm::RoundUpToAlignment(offset, 16);
          os->write(offset, arguments[i]);
          offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
        }
      }
    }
    getArgumentCell(state, kf, f->arg_size(), arguments);
  }
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src, ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.

  // XXX this lookup has to go ?
  KFunction *kf = functionMap[state.stack.back().containingFunc];
  state.pc = &kf->instructions[kf->basicBlockEntry[dst]];
  if (state.pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode*>(state.pc->inst);
    state.incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

/// Compute the true target of a function call, resolving LLVM and KLEE aliases
/// and bitcasts.
Function* Executor::getTargetFunction(Value *calledVal, ExecutionState &state) {
  SmallPtrSet<const GlobalValue*, 3> Visited;
  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;
  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (Visited.insert(gv).second)
          if (Function *f = dyn_cast<Function>(gv))
              return f;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast) {
          c = ce->getOperand(0);
          continue;
      }
    }
    return 0;
  }
}

static inline const llvm::fltSemantics * fpWidthToSemantics(unsigned width) {
  switch(width) {
  case Expr::Int32: return &llvm::APFloat::IEEEsingle;
  case Expr::Int64: return &llvm::APFloat::IEEEdouble;
  case Expr::Fl80:  return &llvm::APFloat::x87DoubleExtended;
  default:          return 0;
  }
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state, ref<Expr> value) {
  state.stack.back().locals[target->dest] = value;
}

std::string Executor::getAddressInfo(ExecutionState &state, ref<Expr> address) {
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address))
    example = CE->getZExtValue();
  else {
    ref<ConstantExpr> value;
    bool success = solveGetValue(state, address, value);
    assert(success && "FIXME: Unhandled solver failure");
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair<ref<Expr>, ref<Expr>> res = solveGetRange(state, address);
    info << "\trange: [" << res.first << ", " << res.second <<"]\n";
  }

  MemoryObject hack((unsigned) example);
  auto lower = state.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower==state.objects.end())
    info << "none\n";
  else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address << " of size " << mo->size << "\n" << "\t\t" << alloc_info << "\n";
  }
  if (lower!=state.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower==state.objects.end())
      info << "none\n";
    else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address << " of size " << mo->size << "\n" << "\t\t" << alloc_info << "\n";
    }
  }
  return info.str();
}

void Executor::terminateStateCase(ExecutionState &state, const char *err, const char *suffix)
{
  interpreterHandler->processTestCase(state, err, suffix);
  interpreterHandler->incPathsExplored();

  auto it = addedStates.find(&state);
  if (it==addedStates.end()) {
    state.pc = state.prevPC;
    removedStates.insert(&state);
  } else {
    // never reached searcher, just delete immediately
    auto it3 = seedMap.find(&state);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    addedStates.erase(it);
    processTree->remove(state.ptreeNode);
    delete &state;
  }
}

void Executor::terminateStateEarly(ExecutionState &state, const Twine &message) {
  terminateStateCase(state, (message + "\n").str().c_str(), "early");
}

void Executor::terminateStateOnExit(ExecutionState &state) {
  terminateStateCase(state, 0, 0);
}

void Executor::terminateStateOnError(ExecutionState &state, const llvm::Twine &messaget, const char *suffix, const llvm::Twine &info) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
  std::string message = messaget.str();
  klee_message("ERROR: (location information missing) %s", message.c_str());
  std::string MsgString;
  llvm::raw_string_ostream msg(MsgString);
  msg << "Error: " << message << "\n" << "Stack: \n";
  state.dumpStack(msg);
  std::string info_str = info.str();
  if (info_str != "")
    msg << "Info: \n" << info_str;
  terminateStateCase(state, msg.str().c_str(), suffix);
}

ObjectState *Executor::bindObjectInState(ExecutionState &state, const MemoryObject *mo, bool isLocal, const Array *array) {
  ObjectState *os = array ? new ObjectState(mo, array) : new ObjectState(mo);
  state.bindObject(mo, os);
  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object // on function return.
  if (isLocal)
    state.stack.back().allocas.push_back(mo);
  return os;
}

void Executor::executeAlloc(ExecutionState &state, ref<Expr> size, bool isLocal, KInstruction *target, bool zeroMemory, const ObjectState *reallocFrom) {
  size = toUnique(state, size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
    MemoryObject *mo = memory->allocate(CE->getZExtValue(), isLocal, false, state.prevPC->inst);
      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory)
        os->initializeToZero();
      else
        os->initializeToRandom();
      bindLocal(target, state, mo->getBaseExpr());
      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i=0; i<count; i++)
          os->write(i, reallocFrom->read8(i));
        state.unbindObject(reallocFrom->getObject());
      }
  } else {
    // XXX For now we just pick a size. Ideally we would support
    // symbolic sizes fully but even if we don't it would be better to
    // "smartly" pick a value, for example we could fork and pick the
    // min and max values and perhaps some intermediate (reasonable // value).
    // It would also be nice to recognize the case when size has
    // exactly two values and just fork (but we need to get rid of
    // return argument first). This shows up in pcre when llvm
    // collapses the size expression with a select.
    ref<ConstantExpr> example;
    bool success = solveGetValue(state, size, example);
    assert(success && "FIXME: Unhandled solver failure");
    // Try and start with a small example.
    Expr::Width W = example->getWidth();
    while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
      ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
      bool res;
      bool success = mayBeTrue(state, EqExpr::create(tmp, size), res);
      assert(success && "FIXME: Unhandled solver failure");
      if (!res)
        break;
      example = tmp;
    }
    StatePair fixedSize = stateFork(state, EqExpr::create(example, size), true);
    if (fixedSize.second) {
      // Check for exactly two values
      ref<ConstantExpr> tmp;
      bool success = solveGetValue(*fixedSize.second, size, tmp);
      assert(success && "FIXME: Unhandled solver failure");
      bool res;
      success = mustBeTrue(*fixedSize.second, EqExpr::create(tmp, size), res);
      assert(success && "FIXME: Unhandled solver failure");
      if (res)
        executeAlloc(*fixedSize.second, tmp, isLocal, target, zeroMemory, reallocFrom);
      else {
        // See if a *really* big value is possible. If so assume
        // malloc will fail for it, so lets fork and return 0.
        StatePair hugeSize = stateFork(*fixedSize.second,UltExpr::create(ConstantExpr::alloc(1<<31,W),size), true);
        if (hugeSize.first) {
          klee_message("NOTE: found huge malloc, returning 0");
          bindLocal(target, *hugeSize.first, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
        }
        if (hugeSize.second) {
          std::string Str;
          llvm::raw_string_ostream info(Str);
          ExprPPrinter::printOne(info, "  size expr", size);
          info << "  concretization : " << example << "\n  unbound example: " << tmp << "\n";
          terminateStateOnError(*hugeSize.second, "concretized symbolic size", "model.err", info.str());
        }
      }
    }
    if (fixedSize.first) // can be zero when fork fails
      executeAlloc(*fixedSize.first, example, isLocal, target, zeroMemory, reallocFrom);
  }
}

void Executor::executeFree(ExecutionState &state, ref<Expr> address, KInstruction *target) {
  StatePair zeroPointer = stateFork(state, Expr::createIsZero(address), true);
  if (zeroPointer.first && target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  if (zeroPointer.second) { // address != 0
    ExactResolutionList rl;
    resolveExact(*zeroPointer.second, address, rl, "free");
    for (auto it = rl.begin(), ie = rl.end(); it != ie; ++it) {
      const MemoryObject *mo = it->first.first;
      if (mo->isLocal || mo->isGlobal)
        terminateStateOnError(*it->second, "free of global", "free.err", getAddressInfo(*it->second, address));
      else {
        it->second->unbindObject(mo);
        if (target)
          bindLocal(target, *it->second, Expr::createPointer(0));
      }
    }
  }
}

void Executor::resolveExact(ExecutionState &state, ref<Expr> p, ExactResolutionList &results, const std::string &name) {
  // XXX we may want to be capping this?
  ResolutionList rl;
  resolve(state, p, rl);
  ExecutionState *unbound = &state;
  for (auto it = rl.begin(), ie = rl.end(); it != ie; ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());
    StatePair branches = stateFork(*unbound, inBounds, true);
    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));
    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }
  if (unbound)
    terminateStateOnError(*unbound, "merror: invalid pointer: " + name, "ptr.err", getAddressInfo(*unbound, p));
}

void Executor::executeMemoryOperation(ExecutionState &state, bool isWrite, ref<Expr> address, ref<Expr> value /* undef if read */, KInstruction *target /* undef if write */) {
  Expr::Width type = (isWrite ? value->getWidth() : getWidthForLLVMType(target->inst->getType()));
  unsigned bytes = Expr::getMinBytesForWidth(type);
  // fast path: single in-bounds resolution
  ObjectPair op;
  osolver->setCoreSolverTimeout(0);
  bool success = true;
  if (!dyn_cast<ConstantExpr>(address)) {
  TimerStatIncrementer timer(stats::resolveTime);
  // try cheap search, will succeed for any inbounds pointer
  ref<ConstantExpr> cex;
  if (solveGetValue(state, address, cex)) {
    uint64_t example = cex->getZExtValue();
    MemoryObject hack(example);
    if (const MemoryMap::value_type *res = state.objects.lookup_previous(&hack)) {
      const MemoryObject *mo = res->first;
      if (example - mo->address < mo->size) {
        op = *res;
        goto nextlab;
      }
    }
    // didn't work, now we have to search
    MemoryMap::iterator oi = state.objects.upper_bound(&hack);
    MemoryMap::iterator begin = state.objects.begin();
    MemoryMap::iterator end = state.objects.end();
    MemoryMap::iterator start = oi;
    while (oi!=begin) {
      --oi;
      const MemoryObject *mo = oi->first;
      bool mayBeTruef;
      if (!mayBeTrue(state, mo->getBoundsCheckPointer(address), mayBeTruef))
        goto falselab;
      if (mayBeTruef) {
        op = *oi;
        goto nextlab;
      } else {
        bool mustBeTruef;
        if (!mustBeTrue(state, UgeExpr::create(address, mo->getBaseExpr()), mustBeTruef))
          goto falselab;
        if (mustBeTruef)
          break;
      }
    }
    // search forwards
    for (oi=start; oi!=end; ++oi) {
      const MemoryObject *mo = oi->first;
      bool mustBeTruef;
      if (!mustBeTrue(state, UltExpr::create(address, mo->getBaseExpr()), mustBeTruef))
        goto falselab;
      if (mustBeTruef) {
        break;
      } else {
        bool mayBeTruef;
        if (!mayBeTrue(state, mo->getBoundsCheckPointer(address), mayBeTruef))
          goto falselab;
        if (mayBeTruef) {
          op = *oi;
          goto nextlab;
        }
      }
    }
    success = false;
    goto nextlab;
    }
falselab:
    address = toConstant(state, address, "resolveOneS failure");
  }
  success = state.resolveOne(cast<ConstantExpr>(address), op);
nextlab:
  osolver->setCoreSolverTimeout(0);
  if (success) {
    const MemoryObject *mo = op.first;
    ref<Expr> offset = mo->getOffsetExpr(address);
    bool inBounds;
    osolver->setCoreSolverTimeout(0);
    bool success = mustBeTrue(state, mo->getBoundsCheckOffset(offset, bytes), inBounds);
    osolver->setCoreSolverTimeout(0);
    if (!success) {
      state.pc = state.prevPC;
      terminateStateEarly(state, "Query timed out (bounds check).");
      return;
    }
    if (inBounds) {
      const ObjectState *os = op.second;
      if (isWrite) {
        if (os->readOnly)
          terminateStateOnError(state, "memory error: object read only", "readonly.err");
        else {
          ObjectState *wos = state.getWriteable(mo, os);
          wos->write(offset, value);
        }
      } else {
        ref<Expr> result = os->read(offset, type);
        // right now, we don't replace symbolics (is there any reason to?)
        if (unsigned n = interpreterOpts.MakeConcreteSymbolic)
        if (isa<ConstantExpr>(result) && (n == 1 || !(random() % n))) {
            // create a new fresh location, assert it is equal to concrete value in e // and return it.
            static unsigned id;
            const Array *array = arrayCache.CreateArray("rrws_arr" + llvm::utostr(++id), Expr::getMinBytesForWidth(result->getWidth()));
            ref<Expr>res = Expr::createTempRead(array, result->getWidth());
            ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(result, res));
            llvm::errs() << "Making symbolic: " << eq << "\n";
            state.addConstraint(eq);
            result = res;
        }
        bindLocal(target, state, result);
      }
      return;
    }
  }
  // we are on an error path (no resolution, multiple resolution, one // resolution with out of bounds)
  ResolutionList rl;
  osolver->setCoreSolverTimeout(0);
  bool incomplete = resolve(state, address, rl, 0, 0);
  osolver->setCoreSolverTimeout(0);
  // XXX there is some query wasteage here. who cares?
  ExecutionState *unbound = &state;
  for (auto i = rl.begin(), ie = rl.end(); i != ie; ++i) {
    const MemoryObject *mo = i->first;
    const ObjectState *os = i->second;
    ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);
    StatePair branches = stateFork(*unbound, inBounds, true);
    ExecutionState *bound = branches.first;
    // bound can be 0 on failure or overlapped
    if (bound) {
      if (isWrite) {
        if (os->readOnly)
          terminateStateOnError(*bound, "memory error: object read only", "readonly.err");
        else {
          ObjectState *wos = bound->getWriteable(mo, os);
          wos->write(mo->getOffsetExpr(address), value);
        }
      } else {
        ref<Expr> result = os->read(mo->getOffsetExpr(address), type);
        bindLocal(target, *bound, result);
      }
    }
    unbound = branches.second;
    if (!unbound)
      break;
  }
  // XXX should we distinguish out of bounds and overlapped cases?
  if (unbound) {
    if (incomplete)
      terminateStateEarly(*unbound, "Query timed out (resolve).");
    else
      terminateStateOnError(*unbound, "memory error: out of bound pointer", "ptr.err", getAddressInfo(*unbound, address));
  }
}

void Executor::executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo, const std::string &name) {
  // Create a new object state for the memory object (instead of a copy).
    // Find a unique name for this array.  First try the original name, // or if that fails try adding a unique identifier.
    unsigned id = 0;
    std::string uniqueName = name;
    while (!state.arrayNames.insert(uniqueName).second)
        uniqueName = name + "_" + llvm::utostr(++id);
    const Array *array = arrayCache.CreateArray(uniqueName, mo->size);
    bindObjectInState(state, mo, false, array);
    state.addSymbolic(mo, array);
    auto it = seedMap.find(&state);
    if (it!=seedMap.end())        // In seed mode we need to add this as a binding
      for (auto siit = it->second.begin(), siie = it->second.end(); siit != siie; ++siit) {
        SeedInfo &si = *siit;
        KTestObject *obj = si.getNextInput(mo, false);
        if (!obj) {
            terminateStateOnError(state, "ran out of inputs during seeding", "user.err");
            break;
        }
        if (obj->numBytes > mo->size) {
	    std::stringstream msg;
	    msg << "replace size mismatch: " << mo->name << "[" << mo->size << "]" << " vs " << obj->name << "[" << obj->numBytes << "]" << " in test\n";
            terminateStateOnError(state, msg.str(), "user.err");
            break;
        }
        std::vector<unsigned char> &values = si.assignment.bindings[array];
        values.insert(values.begin(), obj->bytes, obj->bytes + std::min(obj->numBytes, mo->size));
      }
}

const ref<Expr> Executor::eval(KInstruction *ki, unsigned index, ExecutionState &state)
{
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];
  assert(vnumber != -1 && "Invalid operand to eval(), not a value or constant!");
  // Determine if this is a constant or not.
  if (vnumber < 0)
      return evalConstant(constants[-vnumber - 2]);
  return state.stack.back().locals[vnumber];
}

void Executor::executeInstruction(ExecutionState &state)
{
  KInstruction *ki = state.pc;
  Instruction *i = ki->inst;
  llvm::errs() << "     [EXECUTE]:";
  llvm::errs().indent(10) << stats::instructions << " " << *(state.pc->inst) << '\n';
  static sys::TimeValue lastNowTime(0,0),lastUserTime(0,0);
  sys::TimeValue sys(0,0);
  if (lastUserTime.seconds()==0 && lastUserTime.nanoseconds()==0)
    sys::Process::GetTimeUsage(lastNowTime,lastUserTime,sys);
  else {
    sys::TimeValue now(0,0),user(0,0);
    sys::Process::GetTimeUsage(now,user,sys);
    stats::instructionTime += (user - lastUserTime).usec();
    stats::instructionRealTime += (now - lastNowTime).usec();
    lastUserTime = user;
    lastNowTime = now;
  }
  theStatisticManager->setIndex(0/*ii.id*/);
  if (state.instsSinceCovNew)
    ++state.instsSinceCovNew;
  if (instructionIsCoverable(state.pc->inst)) {
    if (!theStatisticManager->getIndexedValue(stats::coveredInstructions, 0/*ii.id*/)) {
      state.coveredNew = true;
      state.instsSinceCovNew = 1;
      ++stats::coveredInstructions;
      stats::uncoveredInstructions += (uint64_t)-1;
    }
  }
  ++stats::instructions;
  state.prevPC = state.pc;
  ++state.pc;
  int opcode = i->getOpcode();
  switch (opcode) {
    // Control flow
  case Instruction::Ret: {
    ReturnInst *ri = cast<ReturnInst>(i);
    KInstIterator kcaller = state.stack.back().caller;
    Instruction *caller = kcaller ? kcaller->inst : 0;
    bool isVoidReturn = (ri->getNumOperands() == 0);
    ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);
    if (!isVoidReturn)
      result = eval(ki, 0, state);
    if (state.stack.size() <= 1) {
      assert(!caller && "caller set on initial stack frame");
      terminateStateOnExit(state);
    } else {
      state.popFrame();
      if (InvokeInst *ii = dyn_cast<InvokeInst>(caller))
        transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
      else {
        state.pc = kcaller;
        ++state.pc;
      }
      if (!isVoidReturn) {
        LLVM_TYPE_Q Type *t = caller->getType();
        if (t != Type::getVoidTy(getGlobalContext())) {
          // may need to do coercion due to bitcasts
          Expr::Width from = result->getWidth();
          Expr::Width to = getWidthForLLVMType(t);
          if (from != to) {
            CallSite cs = (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) : CallSite(cast<CallInst>(caller)));
            // XXX need to check other param attrs ?
            if (cs.paramHasAttr(0, llvm::Attribute::SExt))
              result = SExtExpr::create(result, to);
            else
              result = ZExtExpr::create(result, to);
          }
          bindLocal(kcaller, state, result);
        }
      } else if (!caller->use_empty())
        terminateStateOnExecError(state, "return void when caller expected a result");
        // check that return value has no users instead of checking the type, since C defaults to returning int for undeclared fns
    }
    break;
  }
  case Instruction::Br: {
    BranchInst *bi = cast<BranchInst>(i);
    if (bi->isUnconditional())
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
    else {
      // FIXME: Find a way that we don't have this hidden dependency.
      assert(bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
      ref<Expr> cond = eval(ki, 0, state);
      Executor::StatePair branches = stateFork(state, cond, false);
      ExecutionState *visitedTrue = branches.first, *visitedFalse = branches.second;
      unsigned id = theStatisticManager->getIndex();
      uint64_t hasTrue = theStatisticManager->getIndexedValue(stats::trueBranches, id);
      uint64_t hasFalse = theStatisticManager->getIndexedValue(stats::falseBranches, id);
      if (visitedTrue && !hasTrue) {
        visitedTrue->coveredNew = true;
        visitedTrue->instsSinceCovNew = 1;
        ++stats::trueBranches;
        if (hasFalse) { ++fullBranches; --partialBranches; }
        else ++partialBranches;
        hasTrue = 1;
      }
      if (visitedFalse && !hasFalse) {
        visitedFalse->coveredNew = true;
        visitedFalse->instsSinceCovNew = 1;
        ++stats::falseBranches;
        if (hasTrue) { ++fullBranches; --partialBranches; }
        else ++partialBranches;
      }
      if (branches.first)
        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
      if (branches.second)
        transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);
    }
    break;
  }
  case Instruction::Switch: {
    SwitchInst *si = cast<SwitchInst>(i);
    ref<Expr> cond = eval(ki, 0, state);
    BasicBlock *bb = si->getParent();
    cond = toUnique(state, cond);
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
      // Somewhat gross to create these all the time, but fine till we // switch to an internal rep.
      LLVM_TYPE_Q llvm::IntegerType *Ty = cast<IntegerType>(si->getCondition()->getType());
      ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
      unsigned index = si->findCaseValue(ci).getSuccessorIndex();
      transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
    } else {
      std::map<BasicBlock *, ref<Expr>> targets;
      ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
      for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end(); i != e; ++i) {
        ref<Expr> value = evalConstant(i.getCaseValue());
        ref<Expr> match = EqExpr::create(cond, value);
        isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
        bool result;
        bool success = mayBeTrue(state, match, result);
        assert(success && "FIXME: Unhandled solver failure");
        (void)success;
        if (result) {
          BasicBlock *caseSuccessor = i.getCaseSuccessor();
          auto it = targets.insert(std::make_pair(caseSuccessor, ConstantExpr::alloc(0, Expr::Bool))).first;
          it->second = OrExpr::create(match, it->second);
        }
      }
      bool res;
      bool success = mayBeTrue(state, isDefault, res);
      assert(success && "FIXME: Unhandled solver failure");
      (void)success;
      if (res)
        targets.insert(std::make_pair(si->getDefaultDest(), isDefault));
      std::vector<ref<Expr>> conditions;
      for (auto it = targets.begin(), ie = targets.end(); it != ie; ++it)
        conditions.push_back(it->second);
      std::vector<ExecutionState *> branches;
      branch(state, conditions, branches);
      auto bit = branches.begin();
      for (auto it = targets.begin(), ie = targets.end(); it != ie; ++it) {
        ExecutionState *es = *bit;
        if (es)
          transferToBasicBlock(it->first, bb, *es);
        ++bit;
      }
    }
    break;
 }
  case Instruction::Unreachable:
    // Note that this is not necessarily an internal bug, llvm will
    // generate unreachable instructions in cases where it knows the
    // program will crash. So it is effectively a SEGV or internal
    // error.
    terminateStateOnExecError(state, "reached \"unreachable\" instruction");
    break;

  case Instruction::Invoke:
  case Instruction::Call: {
    CallSite cs(i);
    unsigned numArgs = cs.arg_size();
    Value *fp = cs.getCalledValue();
    Function *f = getTargetFunction(fp, state);
    if (isa<InlineAsm>(fp)) {
      terminateStateOnExecError(state, "inline assembly is unsupported");
      break;
    }
    // evaluate arguments
    std::vector<ref<Expr>> arguments;
    arguments.reserve(numArgs);
    for (unsigned j=0; j<numArgs; ++j)
      arguments.push_back(eval(ki, j+1, state));
    if (f) {
      const FunctionType *fType = dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
      const FunctionType *fpType = dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());
      // special case the call with a bitcast case
      if (fType != fpType) {
        assert(fType && fpType && "unable to get function type");
        // XXX check result coercion
        // XXX this really needs thought and validation
        unsigned i=0;
        for (auto ai = arguments.begin(), ie = arguments.end(); ai != ie; ++ai) {
          Expr::Width to, from = (*ai)->getWidth();
          if (i<fType->getNumParams()) {
            to = getWidthForLLVMType(fType->getParamType(i));
            if (from != to) {
              // XXX need to check other param attrs ?
              if (cs.paramHasAttr(i+1, llvm::Attribute::SExt))
                arguments[i] = SExtExpr::create(arguments[i], to);
              else
                arguments[i] = ZExtExpr::create(arguments[i], to);
            }
          }
          i++;
        }
      }
      executeCall(state, ki, f, arguments);
    } else {
      ref<Expr> v = eval(ki, 0, state);
      ExecutionState *free = &state;
      bool hasInvalid = false, first = true;
      /* XXX This is wasteful, no need to do a full evaluate since we
         have already got a value. But in the end the caches should handle it for us, albeit with some overhead. */
      do {
        ref<ConstantExpr> value;
        bool success = solveGetValue(*free, v, value);
        assert(success && "FIXME: Unhandled solver failure");
        StatePair res = stateFork(*free, EqExpr::create(v, value), true);
        if (res.first) {
          uint64_t addr = value->getZExtValue();
          if (legalFunctions.count(addr)) {
            f = (Function*) addr;
            // Don't give warning on unique resolution
            if (res.second || !first)
              klee_warning_once((void*) (unsigned long) addr, "resolved symbolic function pointer to: %s", f->getName().data());
            executeCall(*res.first, ki, f, arguments);
          } else {
            if (!hasInvalid) {
              terminateStateOnExecError(state, "invalid function pointer");
              hasInvalid = true;
            }
          }
        }
        first = false;
        free = res.second;
      } while (free);
    }
    break;
  }
  case Instruction::PHI: {
    ref<Expr> result = eval(ki, state.incomingBBIndex, state);
    bindLocal(ki, state, result);
    break;
  }

    // Special instructions
  case Instruction::Select: {
    ref<Expr> cond = eval(ki, 0, state);
    ref<Expr> tExpr = eval(ki, 1, state);
    ref<Expr> fExpr = eval(ki, 2, state);
    ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::VAArg:
    terminateStateOnExecError(state, "unexpected VAArg instruction");
    break;

    // Arithmetic / logical
  case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
  case Instruction::UDiv: case Instruction::SDiv:
  case Instruction::URem: case Instruction::SRem:
  case Instruction::And: case Instruction::Or: case Instruction::Xor:
  case Instruction::Shl: case Instruction::LShr: case Instruction::AShr: {
    ref<Expr> left = eval(ki, 0, state);
    ref<Expr> right = eval(ki, 1, state);
    ref<Expr> result;
    switch (opcode) {
    case Instruction::Add:
        result = AddExpr::create(left, right);
        break;
    case Instruction::Sub:
        result = SubExpr::create(left, right);
        break;
    case Instruction::Mul:
        result = MulExpr::create(left, right);
        break;
    case Instruction::UDiv:
        result = UDivExpr::create(left, right);
        break;
    case Instruction::SDiv:
        result = SDivExpr::create(left, right);
        break;
    case Instruction::URem:
        result = URemExpr::create(left, right);
        break;
    case Instruction::SRem:
        result = SRemExpr::create(left, right);
        break;
    case Instruction::LShr:
        result = LShrExpr::create(left, right);
        break;
    case Instruction::AShr:
        result = AShrExpr::create(left, right);
        break;
    case Instruction::Shl:
        result = ShlExpr::create(left, right);
        break;
    case Instruction::Xor:
        result = XorExpr::create(left, right);
        break;
    case Instruction::Or:
        result = OrExpr::create(left, right);
        break;
    case Instruction::And:
        result = AndExpr::create(left, right);
        break;
    }
    bindLocal(ki, state, result);
    break;
  }

    // Compare
  case Instruction::ICmp: {
    ICmpInst *ii = cast<ICmpInst>(i);
    ref<Expr> left = eval(ki, 0, state);
    ref<Expr> right = eval(ki, 1, state);
    ref<Expr> result;
    switch(ii->getPredicate()) {
    case ICmpInst::ICMP_EQ:
      result = EqExpr::create(left, right);
      break;
    case ICmpInst::ICMP_NE:
      result = NeExpr::create(left, right);
      break;
    case ICmpInst::ICMP_UGT:
      result = UgtExpr::create(left, right);
      break;
    case ICmpInst::ICMP_UGE:
      result = UgeExpr::create(left, right);
      break;
    case ICmpInst::ICMP_ULT:
      result = UltExpr::create(left, right);
      break;
    case ICmpInst::ICMP_ULE:
      result = UleExpr::create(left, right);
      break;
    case ICmpInst::ICMP_SGT:
      result = SgtExpr::create(left, right);
      break;
    case ICmpInst::ICMP_SGE:
      result = SgeExpr::create(left, right);
      break;
    case ICmpInst::ICMP_SLT:
      result = SltExpr::create(left, right);
      break;
    case ICmpInst::ICMP_SLE:
      result = SleExpr::create(left, right);
      break;
    default:
      terminateStateOnExecError(state, "invalid ICmp predicate");
    }
    bindLocal(ki, state, result);
    break;
  }

    // Memory instructions...
  case Instruction::Alloca: {
    AllocaInst *ai = cast<AllocaInst>(i);
    unsigned elementSize = targetData->getTypeStoreSize(ai->getAllocatedType());
    ref<Expr> size = Expr::createPointer(elementSize);
    if (ai->isArrayAllocation()) {
      ref<Expr> count = eval(ki, 0, state);
      count = Expr::createZExtToPointerWidth(count);
      size = MulExpr::create(size, count);
    }
    executeAlloc(state, size, true, ki);
    break;
  }

  case Instruction::Load: {
    ref<Expr> base = eval(ki, 0, state);
    executeMemoryOperation(state, false, base, 0, ki);
    break;
  }
  case Instruction::Store: {
    ref<Expr> base = eval(ki, 1, state);
    ref<Expr> value = eval(ki, 0, state);
    executeMemoryOperation(state, true, base, value, 0);
    break;
  }

  case Instruction::GetElementPtr: {
    ref<Expr> base = eval(ki, 0, state);
    for (auto it = ki->indices.begin(), ie = ki->indices.end(); it != ie; ++it){
      uint64_t elementSize = it->second;
      ref<Expr> index = eval(ki, it->first, state);
      base = AddExpr::create(base, MulExpr::create(Expr::createSExtToPointerWidth(index), Expr::createPointer(elementSize)));
    }
    if (ki->offset)
      base = AddExpr::create(base, Expr::createPointer(ki->offset));
    bindLocal(ki, state, base);
    break;
  }

    // Conversion
  case Instruction::Trunc: case Instruction::ZExt: case Instruction::SExt:
  case Instruction::IntToPtr: case Instruction::PtrToInt: {
    Expr::Width iType = getWidthForLLVMType(i->getType());
    ref<Expr> arg = eval(ki, 0, state);
    ref<Expr> result;
    switch (opcode) {
    case Instruction::Trunc:
        result = ExtractExpr::create(arg, 0, iType);
        break;
    case Instruction::ZExt:
        result = ZExtExpr::create(arg, iType);
        break;
    case Instruction::SExt:
        result = SExtExpr::create(arg, iType);
        break;
    case Instruction::IntToPtr:
        result = ZExtExpr::create(arg, iType);
        break;
    case Instruction::PtrToInt:
        result = ZExtExpr::create(arg, iType);
        break;
    }
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::BitCast: {
    ref<Expr> result = eval(ki, 0, state);
    bindLocal(ki, state, result);
    break;
  }

    // Floating point instructions
  case Instruction::FAdd: case Instruction::FSub:
  case Instruction::FMul: case Instruction::FDiv: case Instruction::FRem: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state), "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state), "floating point");
    if (!fpWidthToSemantics(left->getWidth()) || !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FRem operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    llvm::APFloat rop(*fpWidthToSemantics(right->getWidth()), right->getAPValue());
    switch(opcode) {
    case Instruction::FAdd:
        Res.add(rop, APFloat::rmNearestTiesToEven);
        break;
    case Instruction::FSub:
        Res.subtract(rop, APFloat::rmNearestTiesToEven);
        break;
    case Instruction::FMul:
        Res.multiply(rop, APFloat::rmNearestTiesToEven);
        break;
    case Instruction::FDiv:
        Res.divide(rop, APFloat::rmNearestTiesToEven);
        break;
    case Instruction::FRem:
        Res.mod(rop, APFloat::rmNearestTiesToEven);
        break;
    }
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FPTrunc: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
      return terminateStateOnExecError(state, "Unsupported FPTrunc operation");
    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType), llvm::APFloat::rmNearestTiesToEven, &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPExt: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
      return terminateStateOnExecError(state, "Unsupported FPExt operation");
    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType), llvm::APFloat::rmNearestTiesToEven, &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPToUI: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToUI operation");
    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    uint64_t value = 0;
    bool isExact = true;
    Arg.convertToInteger(&value, resultType, false, llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::FPToSI: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToSI operation");
    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    uint64_t value = 0;
    bool isExact = true;
    Arg.convertToInteger(&value, resultType, true, llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::UIToFP: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported UIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), false, llvm::APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::SIToFP: {
    Expr::Width resultType = getWidthForLLVMType(i->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state), "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported SIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), true, llvm::APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::FCmp: {
    FCmpInst *fi = cast<FCmpInst>(i);
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state), "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state), "floating point");
    if (!fpWidthToSemantics(left->getWidth()) || !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FCmp operation");
    APFloat LHS(*fpWidthToSemantics(left->getWidth()),left->getAPValue());
    APFloat RHS(*fpWidthToSemantics(right->getWidth()),right->getAPValue());
    APFloat::cmpResult CmpRes = LHS.compare(RHS);
    bool Result = false;
    switch( fi->getPredicate() ) {
      // Predicates which only care about whether or not the operands are NaNs.
    case FCmpInst::FCMP_ORD:
      Result = CmpRes != APFloat::cmpUnordered;
      break;
    case FCmpInst::FCMP_UNO:
      Result = CmpRes == APFloat::cmpUnordered;
      break;
      // Ordered comparisons return false if either operand is NaN.  Unordered
      // comparisons return true if either operand is NaN.
    case FCmpInst::FCMP_UEQ:
      Result = CmpRes == APFloat::cmpUnordered;
    case FCmpInst::FCMP_OEQ:
      Result |= CmpRes == APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_UGT:
      Result = CmpRes == APFloat::cmpUnordered;
    case FCmpInst::FCMP_OGT:
      Result |= CmpRes == APFloat::cmpGreaterThan;
      break;
    case FCmpInst::FCMP_UGE:
      Result = CmpRes == APFloat::cmpUnordered;
    case FCmpInst::FCMP_OGE:
      Result |= CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_ULT:
      Result = CmpRes == APFloat::cmpUnordered;
    case FCmpInst::FCMP_OLT:
      Result |= CmpRes == APFloat::cmpLessThan;
      break;
    case FCmpInst::FCMP_ULE:
      Result = CmpRes == APFloat::cmpUnordered;
    case FCmpInst::FCMP_OLE:
      Result |= CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_UNE:
      Result = CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_ONE:
      Result = CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_FALSE:
      Result = false;
      break;
    case FCmpInst::FCMP_TRUE:
      Result = true;
      break;
    default:
      assert(0 && "Invalid FCMP predicate!");
    }
    bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
    break;
  }
  case Instruction::InsertValue: {
    assert(ki->indices.empty() && "InsertValue constant offset expected");
    ref<Expr> agg = eval(ki, 0, state);
    ref<Expr> val = eval(ki, 1, state);
    ref<Expr> l = NULL, r = NULL;
    unsigned lOffset = ki->offset*8, rOffset = ki->offset*8 + val->getWidth();
    if (lOffset > 0)
      l = ExtractExpr::create(agg, 0, lOffset);
    if (rOffset < agg->getWidth())
      r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);
    ref<Expr> result = val;
    if (!l.isNull() && !r.isNull())
      result = ConcatExpr::create(r, ConcatExpr::create(val, l));
    else if (!l.isNull())
      result = ConcatExpr::create(val, l);
    else if (!r.isNull())
      result = ConcatExpr::create(r, val);
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ExtractValue: {
    assert(ki->indices.empty() && "ExtractValue constant offset expected");
    ref<Expr> agg = eval(ki, 0, state);
    ref<Expr> result = ExtractExpr::create(agg, ki->offset*8, getWidthForLLVMType(i->getType()));
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::ExtractElement:
  case Instruction::InsertElement:
  case Instruction::ShuffleVector:
  default:
    terminateStateOnExecError(state, "illegal instruction");
    break;
  }
}

void Executor::runFunctionAsMain(Function *f, int argc, char **argv, char **envp)
{
printf("[%s:%d] start\n", __FUNCTION__, __LINE__);
  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  std::vector<ref<Expr>> arguments;
  KFunction *kf = functionMap[f];
  assert(kf);
  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);
  MemoryObject *argvMO = 0;
  int envc;
  for (envc=0; envp[envc]; ++envc) ;
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  if (ai != ae) {
    arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));
    if (++ai != ae) {
      argvMO = memory->allocate((argc+1+envc+1+1) * NumPtrBytes, false, true, f->begin()->begin());
      arguments.push_back(argvMO->getBaseExpr());
      if (++ai != ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.push_back(Expr::createPointer(envp_start));
        if (++ai != ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }
  ExecutionState *startingState = new ExecutionState(kf->instructions, f, kf->numRegisters);
  if (pathWriter)
    startingState->pathOS = pathWriter->open();
  if (symPathWriter)
    startingState->symPathOS = symPathWriter->open();
  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  getArgumentCell(*startingState, kf, f->arg_size(), arguments);
  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*startingState, argvMO, false);
    for (int i=0; i<argc+1+envc+1+1; i++) {
      ref<ConstantExpr> val = Expr::createPointer(0);
      if (i != argc && i < argc+1+envc) {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);
        MemoryObject *arg = memory->allocate(len+1, false, true, startingState->pc->inst);
        ObjectState *os = bindObjectInState(*startingState, arg, false);
        for (j=0; j<len+1; j++)
          os->write8(j, s[j]);
        // Write pointer to newly allocated and initialised argv/envp c-string
        val = arg->getBaseExpr();
      }
      argvOS->write(i * NumPtrBytes, val);
    }
  }
  initializeGlobals(*startingState);
  processTree = new PTree(startingState);
  startingState->ptreeNode = processTree->root;
  // Delay init till now so that ticks don't accrue during optimization and such.
  states.insert(startingState);
  if (CoreSearch.size() == 0) {
    CoreSearch.push_back(Searcher::DFS);
  }
  std::vector<Searcher *> s;
  Searcher *searcher = NULL;
  for (unsigned i=0; i < CoreSearch.size(); i++) {
      switch (CoreSearch[i]) {
      case Searcher::DFS: searcher = new DFSSearcher(); break;
      case Searcher::BFS: searcher = new BFSSearcher(); break;
      }
      s.push_back(searcher);
  }
  searcher->update(0, states, std::set<ExecutionState*>());
printf("[%s:%d] Executorbefore run\n", __FUNCTION__, __LINE__);
  while (!states.empty()) {
    ExecutionState &state = searcher->selectState();
    executeInstruction(state);
    searcher->update(&state, addedStates, removedStates);
    states.insert(addedStates.begin(), addedStates.end());
    addedStates.clear();
    for (auto it = removedStates.begin(), ie = removedStates.end(); it != ie; ++it) {
      ExecutionState *es = *it;
      auto it2 = states.find(es);
      assert(it2!=states.end());
      states.erase(it2);
      auto it3 = seedMap.find(es);
      if (it3 != seedMap.end())
        seedMap.erase(it3);
      processTree->remove(es->ptreeNode);
      delete es;
    }
    removedStates.clear();
  }
printf("[%s:%d] Executorafter run\n", __FUNCTION__, __LINE__);
  delete processTree;
  processTree = 0;
  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);
  globalObjects.clear();
  globalAddresses.clear();
  writeStatsLine();
  llvm::outs() << "version: 1;creator: klee;pid: " << getpid() << ";cmd: " << module->getModuleIdentifier() << "; positions: instr line;events: \n";
}

// what a hack
static Function *getStubFunctionForCtorList(Module *m, GlobalVariable *gv, std::string name) {
  assert(!gv->isDeclaration() && !gv->hasInternalLinkage() && "do not support old LLVM style constructor/destructor lists");
  std::vector<LLVM_TYPE_Q Type*> nullary;
  Function *fn = Function::Create( FunctionType::get(Type::getVoidTy(getGlobalContext()), nullary, false),
      GlobalVariable::InternalLinkage, name, m);
  BasicBlock *bb = BasicBlock::Create(getGlobalContext(), "entry", fn);
  // From lli: // Should be an array of '{ int, void ()* }' structs.  The first value is // the init priority, which we ignore.
  if (ConstantArray *arr = dyn_cast<ConstantArray>(gv->getInitializer()))
    for (unsigned i=0; i<arr->getNumOperands(); i++) {
      ConstantStruct *cs = cast<ConstantStruct>(arr->getOperand(i));
      // There is a third *optional* element in global_ctor elements (``i8 // @data``).
      assert((cs->getNumOperands() == 2 || cs->getNumOperands() == 3) && "unexpected element in ctor initializer list");
      Constant *fp = cs->getOperand(1);
      if (!fp->isNullValue()) {
        if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(fp))
          fp = ce->getOperand(0);
        if (Function *f = dyn_cast<Function>(fp))
	  CallInst::Create(f, "", bb);
        else
          assert(0 && "unable to get function pointer from ctor initializer list");
      }
    }
  ReturnInst::Create(getGlobalContext(), bb);
  return fn;
}

template <typename TypeIt>
void Executor::computeOffsets(KInstruction *ki, TypeIt ib, TypeIt ie) {
  ref<ConstantExpr> constantOffset = ConstantExpr::alloc(0, Context::get().getPointerWidth());
  uint64_t index = 1;
  for (TypeIt ii = ib; ii != ie; ++ii) {
    if (LLVM_TYPE_Q StructType *st = dyn_cast<StructType>(*ii)) {
      const StructLayout *sl = targetData->getStructLayout(st);
      const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
      uint64_t addend = sl->getElementOffset((unsigned) ci->getZExtValue());
      constantOffset = constantOffset->Add(ConstantExpr::alloc(addend, Context::get().getPointerWidth()));
    } else {
      const SequentialType *set = cast<SequentialType>(*ii);
      uint64_t elementSize = targetData->getTypeStoreSize(set->getElementType());
      Value *operand = ii.getOperand();
      if (Constant *c = dyn_cast<Constant>(operand)) {
        ref<ConstantExpr> index = evalConstant(c)->SExt(Context::get().getPointerWidth());
        ref<ConstantExpr> addend = index->Mul(ConstantExpr::alloc(elementSize, Context::get().getPointerWidth()));
        constantOffset = constantOffset->Add(addend);
      } else
        ki->indices.push_back(std::make_pair(index, elementSize));
    }
    index++;
  }
  ki->offset = constantOffset->getZExtValue();
}

static int getOperandNum(Value *v, std::map<Instruction*, unsigned> &registerMap, KInstruction *ki, Executor *exec) {
  if (Instruction *inst = dyn_cast<Instruction>(v))
    return registerMap[inst];
  else if (Argument *a = dyn_cast<Argument>(v))
    return a->getArgNo(); // Metadata is no longer a Value
  else if (isa<BasicBlock>(v) || isa<InlineAsm>(v))
    return -1;
  else {
    assert(isa<Constant>(v));
    Constant *c = cast<Constant>(v);
    unsigned id = exec->constants.size();
    auto it = exec->constantMap.find(c);
    if (it != exec->constantMap.end())
      id = it->second->id;
    else {
      exec->constantMap.insert(std::make_pair(c, new KConstant(c, id, ki)));
      exec->constants.push_back(c);
    }
    return -(id + 2);
  }
}

const Module *Executor::setModule(llvm::Module *_module, const ModuleOptions &opts)
{
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
  assert(!module && _module && "can only register one module"); // XXX gross
  module = _module;
  targetData = new DataLayout(module);
  m_SwitchType = SwitchType;
  Context::initialize(targetData->isLittleEndian(), (Expr::Width) targetData->getPointerSizeInBits());
  specialFunctionHandler = new SpecialFunctionHandler(*this);
  specialFunctionHandler->prepare();
  // Inject checks prior to optimization... we also perform the // invariant transformations that we will end up doing later so that
  // optimize is seeing what is as close as possible to the final // module.
  legacy::PassManager pm;
  pm.add(new RaiseAsmPass());
  pm.add(new DivCheckPass());
  pm.add(new OvershiftCheckPass());
  // FIXME: This false here is to work around a bug in // IntrinsicLowering which caches values which may eventually be
  // deleted (via RAUW). This can be removed once LLVM fixes this // issue.
  pm.add(new IntrinsicCleanerPass(*targetData, false));
printf("[%s:%d] before runpreprocessmodule\n", __FUNCTION__, __LINE__);
  pm.run(*module);
  if (opts.Optimize)
    Optimize(module);
  // After linking (since ctors/dtors can be modified) and optimization (global optimization can rewrite lists).
  GlobalVariable *ctors = module->getNamedGlobal("llvm.global_ctors");
  GlobalVariable *dtors = module->getNamedGlobal("llvm.global_dtors");
  if (ctors || dtors) {
    Function *mainFn = module->getFunction("main");
    if (!mainFn)
      klee_error("Could not find main() function.");
    if (ctors)
      CallInst::Create(getStubFunctionForCtorList(module, ctors, "klee.ctor_stub"), "", mainFn->begin()->begin());
    if (dtors) {
      Function *dtorStub = getStubFunctionForCtorList(module, dtors, "klee.dtor_stub");
      for (auto it = mainFn->begin(), ie = mainFn->end(); it != ie; ++it)
        if (isa<ReturnInst>(it->getTerminator()))
	  CallInst::Create(dtorStub, "", it->getTerminator());
    }
  }

  // Finally, run the passes that maintain invariants we expect during
  // interpretation. We run the intrinsic cleaner just in case we
  // linked in something with intrinsics but any external calls are
  // going to be unresolved. We really need to handle the intrinsics
  // directly I think?
  legacy::PassManager pm3;
  pm3.add(createCFGSimplificationPass());
  switch(m_SwitchType) {
  case Executor::eSwitchTypeInternal: break;
  case Executor::eSwitchTypeSimple: pm3.add(new LowerSwitchPass()); break;
  case Executor::eSwitchTypeLLVM:  pm3.add(createLowerSwitchPass()); break;
  default: klee_error("invalid --switch-type");
  }
  pm3.add(new IntrinsicCleanerPass(*targetData));
  pm3.add(new PhiCleanerPass());
  pm3.run(*module);

#if 0
printf("[%s:%d] openassemblyll\n", __FUNCTION__, __LINE__);
  llvm::outs() << *module;
#endif
  startWallTime = util::getWallTime();
  fullBranches = 0;
  partialBranches = 0;
  numBranches = 0;
  theStatisticManager->useIndexedStats(0/*km->infos->getMaxID()*/);
  llvm::outs() << "('Instructions'," << "'FullBranches'," << "'PartialBranches',"
       << "'NumBranches'," << "'UserTime'," << "'NumStates',"
       << "'MallocUsage'," << "'NumQueries'," << "'NumQueryConstructs',"
       << "'NumObjects'," << "'WallTime'," << "'CoveredInstructions',"
       << "'UncoveredInstructions'," << "'QueryTime'," << "'SolverTime',"
       << "'CexCacheTime'," << "'ForkTime'," << "'ResolveTime',"
#ifdef DEBUG
       << "'ArrayHashTime',"
#endif
       << ")\n";
  writeStatsLine();
  /* Build shadow structures */
  for (auto it = module->begin(), ie = module->end(); it != ie; ++it)
    if (!it->isDeclaration()) {
      KFunction *kf = new KFunction(it);
      llvm::Function *thisFunc = it;
      for (auto bbit = thisFunc->begin(), bbie = thisFunc->end(); bbit != bbie; ++bbit) {
        BasicBlock *bb = bbit;
        kf->basicBlockEntry[bb] = kf->numInstructions;
        kf->numInstructions += bb->size();
      }
      kf->instructions = new KInstruction*[kf->numInstructions];
      std::map<Instruction*, unsigned> registerMap;
      unsigned insInd = 0;
      unsigned rnum = thisFunc->arg_size(); // The first arg_size() registers are reserved for formals.
      for (auto bbit = thisFunc->begin(), bbie = thisFunc->end(); bbit != bbie; ++bbit)
        for (auto it = bbit->begin(), ie = bbit->end(); it != ie; ++it) {
          KInstruction *ki = new KInstruction();
          ki->offset = -1;
          ki->inst = it;
          registerMap[it] = rnum++;
          ki->dest = registerMap[it];
          if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(it))
            computeOffsets(ki, gep_type_begin(gepi), gep_type_end(gepi));
          else if (InsertValueInst *ivi = dyn_cast<InsertValueInst>(it))
            computeOffsets(ki, iv_type_begin(ivi), iv_type_end(ivi));
          else if (ExtractValueInst *evi = dyn_cast<ExtractValueInst>(it))
            computeOffsets(ki, ev_type_begin(evi), ev_type_end(evi));
          if (isa<CallInst>(it) || isa<InvokeInst>(it)) {
            CallSite cs(it);
            unsigned numArgs = cs.arg_size();
            ki->operands = new int[numArgs+1];
            ki->operands[0] = getOperandNum(cs.getCalledValue(), registerMap, ki, this);
            for (unsigned j=0; j<numArgs; j++)
              ki->operands[j+1] = getOperandNum(cs.getArgument(j), registerMap, ki, this);
          } else {
            unsigned numOperands = it->getNumOperands();
            ki->operands = new int[numOperands];
            for (unsigned j=0; j<numOperands; j++)
              ki->operands[j] = getOperandNum(it->getOperand(j), registerMap, ki, this);
          }
          theStatisticManager->setIndex(0);
          if (instructionIsCoverable(ki->inst))
            ++stats::uncoveredInstructions;
          if (BranchInst *bi = dyn_cast<BranchInst>(ki->inst))
            if (!bi->isUnconditional())
              numBranches++;
          kf->instructions[insInd++] = ki;
        }
      kf->numRegisters = rnum;
      functionMap.insert(std::make_pair(it, kf));
      if (functionEscapes(it))
        escapingFunctions.insert(it);
    }
  specialFunctionHandler->bind();
  if (!escapingFunctions.empty()) {
    llvm::errs() << "KLEE: escaping fns: [";
    for (auto it = escapingFunctions.begin(), ie = escapingFunctions.end(); it != ie; ++it)
      llvm::errs() << (*it)->getName() << ", ";
    llvm::errs() << "]\n";
  }
  if (module->getModuleInlineAsm() != "")
    klee_warning("executable has module level assembly (ignoring)");
  std::set<std::string> undefinedSymbols;
  GetAllUndefinedSymbols(module, undefinedSymbols);
  return module;
}
