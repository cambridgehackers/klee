//===-- KModule.cpp -------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define DEBUG_TYPE "KModule"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/Path.h"
#include <llvm/Transforms/Utils/Cloning.h>
#include <sstream>

using namespace llvm;
using namespace klee;

namespace {
  cl::opt<KModule::SwitchImplType>
  SwitchType("switch-type", cl::desc("Select the implementation of switch"),
             cl::values(clEnumValN(KModule::eSwitchTypeSimple, "simple", "lower to ordered branches"),
                        clEnumValN(KModule::eSwitchTypeLLVM, "llvm", "lower using LLVM"),
                        clEnumValN(KModule::eSwitchTypeInternal, "internal", "execute switch internally"),
                        clEnumValEnd),
             cl::init(KModule::eSwitchTypeInternal)); 
}

KModule::KModule(Module *_module) 
  : module(_module),
    targetData(new DataLayout(module)),
    kleeMergeFn(0),
    infos(0),
    m_SwitchType(SwitchType) {
}

KModule::~KModule() {
  delete infos; 
  for (auto it = functions.begin(), ie = functions.end(); it != ie; ++it)
    delete *it; 
  for (auto it=constantMap.begin(), itE=constantMap.end(); it!=itE;++it)
    delete it->second; 
  delete targetData;
  delete module;
}

void KModule::addInternalFunction(const char* functionName){
  Function* internalFunction = module->getFunction(functionName);
  if (!internalFunction) {
    KLEE_DEBUG(klee_warning( "Failed to add internal function %s. Not found.", functionName));
    return ;
  }
  KLEE_DEBUG(klee_message("Added function %s.",functionName));
  internalFunctions.insert(internalFunction);
}

KConstant* KModule::getKConstant(Constant *c) {
  auto it = constantMap.find(c);
  if (it != constantMap.end())
    return it->second;
  return NULL;
}

unsigned KModule::getConstantID(Constant *c, KInstruction* ki) {
  KConstant *kc = getKConstant(c);
  if (kc)
    return kc->id;  
  unsigned id = constants.size();
  kc = new KConstant(c, id, ki);
  constantMap.insert(std::make_pair(c, kc));
  constants.push_back(c);
  return id;
}

/***/ 
KConstant::KConstant(llvm::Constant* _ct, unsigned _id, KInstruction* _ki) {
  ct = _ct;
  id = _id;
  ki = _ki;
}

/***/

static int getOperandNum(Value *v, std::map<Instruction*, unsigned> &registerMap, KModule *km, KInstruction *ki) {
  if (Instruction *inst = dyn_cast<Instruction>(v))
    return registerMap[inst];
  else if (Argument *a = dyn_cast<Argument>(v))
    return a->getArgNo(); // Metadata is no longer a Value
  else if (isa<BasicBlock>(v) || isa<InlineAsm>(v))
    return -1;
  else {
    assert(isa<Constant>(v));
    Constant *c = cast<Constant>(v);
    return -(km->getConstantID(c, ki) + 2);
  }
}

KFunction::KFunction(llvm::Function *_function, KModule *km) 
  : function(_function),
    numArgs(function->arg_size()),
    numInstructions(0),
    trackCoverage(true) {
  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = bbit;
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  } 
  instructions = new KInstruction*[numInstructions]; 
  std::map<Instruction*, unsigned> registerMap; 
  // The first arg_size() registers are reserved for formals.
  unsigned rnum = numArgs;
  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit)
    for (auto it = bbit->begin(), ie = bbit->end(); it != ie; ++it)
      registerMap[it] = rnum++;
  numRegisters = rnum; 
  unsigned i = 0;
  for (auto bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit)
    for (auto it = bbit->begin(), ie = bbit->end(); it != ie; ++it) {
      KInstruction *ki; 
      switch(it->getOpcode()) {
      case Instruction::GetElementPtr: case Instruction::InsertValue: case Instruction::ExtractValue:
        ki = new KGEPInstruction(); break;
      default:
        ki = new KInstruction(); break;
      } 
      ki->inst = it;      
      ki->dest = registerMap[it]; 
      if (isa<CallInst>(it) || isa<InvokeInst>(it)) {
        CallSite cs(it);
        unsigned numArgs = cs.arg_size();
        ki->operands = new int[numArgs+1];
        ki->operands[0] = getOperandNum(cs.getCalledValue(), registerMap, km, ki);
        for (unsigned j=0; j<numArgs; j++) {
          Value *v = cs.getArgument(j);
          ki->operands[j+1] = getOperandNum(v, registerMap, km, ki);
        }
      } else {
        unsigned numOperands = it->getNumOperands();
        ki->operands = new int[numOperands];
        for (unsigned j=0; j<numOperands; j++)
          ki->operands[j] = getOperandNum(it->getOperand(j), registerMap, km, ki);
      } 
      instructions[i++] = ki;
    }
}

KFunction::~KFunction() {
  for (unsigned i=0; i<numInstructions; ++i)
    delete instructions[i];
  delete[] instructions;
}
