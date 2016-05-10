//===-- SolverStats.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/SolverStats.h"

using namespace klee;

uint64_t stats::cexCacheTime;
uint64_t stats::queries;
uint64_t stats::queriesInvalid;
uint64_t stats::queriesValid;
uint64_t stats::queryCacheHits;
uint64_t stats::queryCacheMisses;
uint64_t stats::queryCexCacheHits;
uint64_t stats::queryCexCacheMisses;
uint64_t stats::queryConstructTime;
uint64_t stats::queryConstructs;
uint64_t stats::queryCounterexamples;
uint64_t stats::queryTime;

#ifdef DEBUG
uint64_t stats::arrayHashTime;
#endif
