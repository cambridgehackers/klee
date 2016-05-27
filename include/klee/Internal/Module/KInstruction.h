//===-- KInstruction.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#ifndef KLEE_KINSTRUCTION_H
#define KLEE_KINSTRUCTION_H
#include "klee/Config/Version.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/IR/Instructions.h"
#include <vector>

namespace klee {
  /// KInstruction - Intermediate instruction representation used /// during execution.
  struct KInstruction {
    llvm::Instruction *inst;    
    /// Value numbers for each operand. -1 is an invalid value,
    /// otherwise negative numbers are indices (negated and offset by
    /// 2) into the module constant table and positive numbers are /// register indices.
    int *operands;
    /// Destination register index.
    unsigned dest; 
    /// indices - The list of variable sized adjustments to add to the pointer
    /// operand to execute the instruction. The first element is the operand
    /// index into the GetElementPtr instruction, and the second element is the
    /// element size to multiple that index by.
    std::vector< std::pair<unsigned, uint64_t> > indices;
    /// offset - A constant offset to add to the pointer operand to execute the /// instruction.
    uint64_t offset;
    KInstruction(llvm::Instruction *_inst, unsigned _dest)
        : inst(_inst), operands(new int[inst->getNumOperands()]), dest(_dest), offset(-1) {}
  public:
    virtual ~KInstruction(); 
  }; 
}
#endif
