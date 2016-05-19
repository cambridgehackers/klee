//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "Memory.h"
#include "Executor.h"
#include "llvm/IR/Function.h"
#include <iomanip>

using namespace llvm;
using namespace klee;

StackFrame::StackFrame(KInstIterator _caller, Function *_kf, unsigned _numRegisters)
  : caller(_caller), containingFunc(_kf), numRegisters(_numRegisters), varargs(0) {
  locals = new Cell[numRegisters];
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    containingFunc(s.containingFunc),
    numRegisters(s.numRegisters),
    allocas(s.allocas),
    varargs(s.varargs) {
  locals = new Cell[numRegisters];
  for (unsigned i = 0; i < numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

ExecutionState::ExecutionState(KInstruction **_instructions, Function *_func, unsigned _numRegisters):
    pc(_instructions),
    prevPC(pc), 
    instsSinceCovNew(0),
    coveredNew(false),
    ptreeNode(0) {
  pushFrame(0, _func, _numRegisters);
}

ExecutionState::ExecutionState(const std::vector<ref<Expr> > &assumptions)
    : constraints(assumptions), ptreeNode(0) {}

ExecutionState::~ExecutionState() {
  for (unsigned int i=0; i<symbolics.size(); i++) {
    const MemoryObject *mo = symbolics[i].first;
    assert(mo->refCount > 0);
    mo->refCount--;
    if (mo->refCount == 0)
      delete mo;
  }

  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    fnAliases(state.fnAliases),
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex), 
    addressSpace(state.addressSpace),
    constraints(state.constraints), 
    pathOS(state.pathOS),
    symPathOS(state.symPathOS), 
    instsSinceCovNew(state.instsSinceCovNew),
    coveredNew(state.coveredNew),
    coveredLines(state.coveredLines),
    ptreeNode(state.ptreeNode),
    symbolics(state.symbolics),
    arrayNames(state.arrayNames)
{
  for (unsigned int i=0; i<symbolics.size(); i++)
    symbolics[i].first->refCount++;
}

ExecutionState *ExecutionState::branch() {
  ExecutionState *falseState = new ExecutionState(*this);
  falseState->coveredNew = false;
  falseState->coveredLines.clear(); 
  return falseState;
}

void ExecutionState::pushFrame(KInstIterator caller, Function *_func, unsigned _numRegisters) {
  stack.push_back(StackFrame(caller,_func, _numRegisters));
}

void ExecutionState::popFrame() {
  StackFrame &sf = stack.back();
  for (auto it = sf.allocas.begin(), ie = sf.allocas.end(); it != ie; ++it)
    addressSpace.unbindObject(*it);
  stack.pop_back();
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) { 
  mo->refCount++;
  symbolics.push_back(std::make_pair(mo, array));
}
///

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  auto it = mm.begin();
  auto ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second;
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second;
  }
  os << "}";
  return os;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (auto it = stack.rbegin(), ie = stack.rend(); it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.containingFunc;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0');
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (auto ai = f->arg_begin(), ae = f->arg_end(); ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", "; 
      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[index++]; 
      if (isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    out << "\n";
    target = sf.caller;
  }
}
