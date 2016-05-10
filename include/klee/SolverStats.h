//===-- SolverStats.h -------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SOLVERSTATS_H
#define KLEE_SOLVERSTATS_H

#include "klee/Config/Version.h"
#include "llvm/Support/DataTypes.h"

namespace klee {
namespace stats {

  extern uint64_t cexCacheTime;
  extern uint64_t queries;
  extern uint64_t queriesInvalid;
  extern uint64_t queriesValid;
  extern uint64_t queryCacheHits;
  extern uint64_t queryCacheMisses;
  extern uint64_t queryCexCacheHits;
  extern uint64_t queryCexCacheMisses;
  extern uint64_t queryConstructTime;
  extern uint64_t queryConstructs;
  extern uint64_t queryCounterexamples;
  extern uint64_t queryTime;
  
#ifdef DEBUG
  extern uint64_t arrayHashTime;
#endif

}
}

#endif
