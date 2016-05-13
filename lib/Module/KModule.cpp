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
#include "Passes.h"
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
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar.h"
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
  for (std::vector<KFunction*>::iterator it = functions.begin(), ie = functions.end(); it != ie; ++it)
    delete *it; 
  for (std::map<llvm::Constant*, KConstant*>::iterator it=constantMap.begin(), itE=constantMap.end(); it!=itE;++it)
    delete it->second; 
  delete targetData;
  delete module;
}

/***/

void KModule::addInternalFunction(const char* functionName){
  Function* internalFunction = module->getFunction(functionName);
  if (!internalFunction) {
    KLEE_DEBUG(klee_warning( "Failed to add internal function %s. Not found.", functionName));
    return ;
  }
  KLEE_DEBUG(klee_message("Added function %s.",functionName));
  internalFunctions.insert(internalFunction);
}

namespace llvm {
extern void Optimize(Module*);
}

// what a hack
static Function *getStubFunctionForCtorList(Module *m, GlobalVariable *gv, std::string name) {
  assert(!gv->isDeclaration() && !gv->hasInternalLinkage() && "do not support old LLVM style constructor/destructor lists"); 
  std::vector<LLVM_TYPE_Q Type*> nullary; 
  Function *fn = Function::Create( FunctionType::get(Type::getVoidTy(getGlobalContext()), nullary, false),
      GlobalVariable::InternalLinkage, name, m);
  BasicBlock *bb = BasicBlock::Create(getGlobalContext(), "entry", fn); 
  // From lli:
  // Should be an array of '{ int, void ()* }' structs.  The first value is
  // the init priority, which we ignore.
  ConstantArray *arr = dyn_cast<ConstantArray>(gv->getInitializer());
  if (arr) {
    for (unsigned i=0; i<arr->getNumOperands(); i++) {
      ConstantStruct *cs = cast<ConstantStruct>(arr->getOperand(i));
      // There is a third *optional* element in global_ctor elements (``i8 // @data``).
      assert((cs->getNumOperands() == 2 || cs->getNumOperands() == 3) && "unexpected element in ctor initializer list");
      Constant *fp = cs->getOperand(1);      
      if (!fp->isNullValue()) {
        if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(fp))
          fp = ce->getOperand(0); 
        if (Function *f = dyn_cast<Function>(fp)) {
	  CallInst::Create(f, "", bb);
        } else {
          assert(0 && "unable to get function pointer from ctor initializer list");
        }
      }
    }
  } 
  ReturnInst::Create(getGlobalContext(), bb); 
  return fn;
}

static void injectStaticConstructorsAndDestructors(Module *m) {
  GlobalVariable *ctors = m->getNamedGlobal("llvm.global_ctors");
  GlobalVariable *dtors = m->getNamedGlobal("llvm.global_dtors"); 
  if (ctors || dtors) {
    Function *mainFn = m->getFunction("main");
    if (!mainFn)
      klee_error("Could not find main() function."); 
    if (ctors)
    CallInst::Create(getStubFunctionForCtorList(m, ctors, "klee.ctor_stub"), "", mainFn->begin()->begin());
    if (dtors) {
      Function *dtorStub = getStubFunctionForCtorList(m, dtors, "klee.dtor_stub");
      for (Function::iterator it = mainFn->begin(), ie = mainFn->end(); it != ie; ++it) {
        if (isa<ReturnInst>(it->getTerminator()))
	  CallInst::Create(dtorStub, "", it->getTerminator());
      }
    }
  }
}

void KModule::prepareModule(const Interpreter::ModuleOptions &opts, InterpreterHandler *ih) {
  // Inject checks prior to optimization... we also perform the // invariant transformations that we will end up doing later so that
  // optimize is seeing what is as close as possible to the final // module.
  legacy::PassManager pm;
  pm.add(new RaiseAsmPass());
  pm.add(new DivCheckPass());
  pm.add(new OvershiftCheckPass());
  // FIXME: This false here is to work around a bug in // IntrinsicLowering which caches values which may eventually be
  // deleted (via RAUW). This can be removed once LLVM fixes this // issue.
  pm.add(new IntrinsicCleanerPass(*targetData, false));
printf("[%s:%d] before run newstufffffff\n", __FUNCTION__, __LINE__);
  pm.run(*module);
printf("[%s:%d] after run newstufffffff\n", __FUNCTION__, __LINE__);

  if (opts.Optimize)
    Optimize(module);
  // FIXME: Missing force import for various math functions.

  // FIXME: Find a way that we can test programs without requiring
  // this to be linked in, it makes low level debugging much more
  // annoying.

#if 0 //jca
  SmallString<128> LibPath(opts.LibraryDir);
  llvm::sys::path::append(LibPath, "kleeRuntimeIntrinsic.bc");
  module = linkWithLibrary(module, LibPath.str());
#endif

  // Add internal functions which are not used to check if instructions
  // have been already visited
    addInternalFunction("klee_div_zero_check");
    addInternalFunction("klee_overshift_check");


  // Needs to happen after linking (since ctors/dtors can be modified)
  // and optimization (since global optimization can rewrite lists).
  injectStaticConstructorsAndDestructors(module);

  // Finally, run the passes that maintain invariants we expect during
  // interpretation. We run the intrinsic cleaner just in case we
  // linked in something with intrinsics but any external calls are
  // going to be unresolved. We really need to handle the intrinsics
  // directly I think?
  legacy::PassManager pm3;
  pm3.add(createCFGSimplificationPass());
  switch(m_SwitchType) {
  case eSwitchTypeInternal: break;
  case eSwitchTypeSimple: pm3.add(new LowerSwitchPass()); break;
  case eSwitchTypeLLVM:  pm3.add(createLowerSwitchPass()); break;
  default: klee_error("invalid --switch-type");
  }
  pm3.add(new IntrinsicCleanerPass(*targetData));
  pm3.add(new PhiCleanerPass());
  pm3.run(*module);

  // Write out the .ll assembly file. We truncate long lines to work
  // around a kcachegrind parsing bug (it puts them on new lines), so
  // that source browsing works.
  {
printf("[%s:%d] openassemblyll\n", __FUNCTION__, __LINE__);
    llvm::raw_fd_ostream *os = ih->openOutputFile("assembly.ll");
    assert(os && !os->has_error() && "unable to open source output");
    *os << *module;
    delete os;
  } 
  kleeMergeFn = module->getFunction("klee_merge"); 
  /* Build shadow structures */ 
  infos = new InstructionInfoTable(module);  
  for (Module::iterator it = module->begin(), ie = module->end(); it != ie; ++it) {
    if (it->isDeclaration())
      continue; 
    KFunction *kf = new KFunction(it, this); 
    for (unsigned i=0; i<kf->numInstructions; ++i) {
      KInstruction *ki = kf->instructions[i];
      ki->info = &infos->getInfo(ki->inst);
    } 
    functions.push_back(kf);
    functionMap.insert(std::make_pair(it, kf));
  } 
  /* Compute various interesting properties */ 
  for (std::vector<KFunction*>::iterator it = functions.begin(), ie = functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    if (functionEscapes(kf->function))
      escapingFunctions.insert(kf->function);
  }

  if (!escapingFunctions.empty()) {
    llvm::errs() << "KLEE: escaping functions: [";
    for (std::set<Function*>::iterator it = escapingFunctions.begin(), ie = escapingFunctions.end(); it != ie; ++it) {
      llvm::errs() << (*it)->getName() << ", ";
    }
    llvm::errs() << "]\n";
  }
}

KConstant* KModule::getKConstant(Constant *c) {
  std::map<llvm::Constant*, KConstant*>::iterator it = constantMap.find(c);
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
  for (llvm::Function::iterator bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = bbit;
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  } 
  instructions = new KInstruction*[numInstructions]; 
  std::map<Instruction*, unsigned> registerMap; 
  // The first arg_size() registers are reserved for formals.
  unsigned rnum = numArgs;
  for (llvm::Function::iterator bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit)
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end(); it != ie; ++it)
      registerMap[it] = rnum++;
  numRegisters = rnum; 
  unsigned i = 0;
  for (llvm::Function::iterator bbit = function->begin(), bbie = function->end(); bbit != bbie; ++bbit)
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end(); it != ie; ++it) {
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
