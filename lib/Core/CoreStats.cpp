//===-- CoreStats.cpp -----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "CoreStats.h"

using namespace klee;

uint64_t stats::allocations;
uint64_t stats::coveredInstructions;
uint64_t stats::falseBranches;
uint64_t stats::forkTime;
uint64_t stats::forks;
uint64_t stats::instructionRealTime;
uint64_t stats::instructionTime;
uint64_t stats::instructions;
uint64_t stats::minDistToReturn;
uint64_t stats::minDistToUncovered;
uint64_t stats::reachableUncovered;
uint64_t stats::resolveTime;
uint64_t stats::solverTime;
uint64_t stats::states;
uint64_t stats::trueBranches;
uint64_t stats::uncoveredInstructions;
