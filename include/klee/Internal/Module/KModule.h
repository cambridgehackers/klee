//===-- KModule.h -----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#ifndef KLEE_KMODULE_H
#define KLEE_KMODULE_H
#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include <map>
#include <set>
#include <vector>

namespace llvm {
  class BasicBlock;
  class Constant;
  class Function;
  class Instruction;
  class Module;
  class DataLayout;
}

namespace klee {
  struct Cell;
  class Executor;
  class Expr;
  class InstructionInfoTable;
  struct KInstruction;
  struct KFunction;

  class KConstant {
  public:
    /// Actual LLVM constant this represents.
    llvm::Constant* ct; 
    /// The constant ID.
    unsigned id; 
    /// First instruction where this constant was encountered, or NULL /// if not applicable/unavailable.
    KInstruction *ki; 
    KConstant(llvm::Constant*, unsigned, KInstruction*);
  }; 

  class KModule {
  public:
    enum SwitchImplType { eSwitchTypeSimple, eSwitchTypeLLVM, eSwitchTypeInternal }; 
    llvm::Module *module;
    llvm::DataLayout *targetData;
    llvm::Function *kleeMergeFn; 
    // Functions which escape (may be called indirectly) // XXX change to KFunction
    std::set<llvm::Function*> escapingFunctions; 
    InstructionInfoTable *infos; 
    std::vector<llvm::Constant*> constants;
    std::map<llvm::Constant*, KConstant*> constantMap;
    KConstant* getKConstant(llvm::Constant *c);
    // Functions which are part of KLEE runtime
    std::set<const llvm::Function*> internalFunctions; 
    // Mark function with functionName as part of the KLEE runtime
    void addInternalFunction(const char* functionName); 
    SwitchImplType m_SwitchType;
  public:
    KModule(llvm::Module *_module);
    ~KModule(); 
    /// Return an id for the given constant, creating a new one if necessary.
    unsigned getConstantID(llvm::Constant *c, KInstruction* ki);
  };
} // End klee namespace

#endif
