//===-- CoreStats.h ---------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CORESTATS_H
#define KLEE_CORESTATS_H

#include "klee/Statistic.h"

namespace klee {
namespace stats {

  extern uint64_t allocations;
  extern uint64_t resolveTime;
  extern uint64_t instructions;
  extern uint64_t instructionTime;
  extern uint64_t instructionRealTime;
  extern uint64_t coveredInstructions;
  extern uint64_t uncoveredInstructions;  
  extern uint64_t trueBranches;
  extern uint64_t falseBranches;
  extern uint64_t forkTime;
  extern uint64_t solverTime;

  /// The number of process forks.
  extern uint64_t forks;

  /// Number of states, this is a "fake" statistic used by istats, it
  /// isn't normally up-to-date.
  extern uint64_t states;

  /// Instruction level statistic for tracking number of reachable
  /// uncovered instructions.
  extern uint64_t reachableUncovered;

  /// Instruction level statistic tracking the minimum intraprocedural
  /// distance to an uncovered instruction; this is only periodically
  /// updated.
  extern uint64_t minDistToUncovered;

  /// Instruction level statistic tracking the minimum intraprocedural
  /// distance to a function return.
  extern uint64_t minDistToReturn;

}
}

#endif
