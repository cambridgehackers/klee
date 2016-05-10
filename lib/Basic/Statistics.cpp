//===-- Statistics.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Statistics.h"

#include <vector>

using namespace klee;

StatisticManager::StatisticManager()
  : globalStats(0),
    indexedStats(0),
    contextStats(0),
    index(0) {
}

StatisticManager::~StatisticManager() {
  if (globalStats) delete[] globalStats;
  if (indexedStats) delete[] indexedStats;
}

void StatisticManager::useIndexedStats(unsigned totalIndices) {  
  if (indexedStats) delete[] indexedStats;
  indexedStats = new uint64_t[totalIndices * stats.size()];
  memset(indexedStats, 0, sizeof(*indexedStats) * totalIndices * stats.size());
}

static StatisticManager sm;
StatisticManager *klee::theStatisticManager = &sm;

static StatisticManager &getStatisticManager() {
  //theStatisticManager = &sm;
  return sm;
}

Statistic::Statistic(const std::string &_name, const std::string &_shortName) 
  : name(_name), shortName(_shortName) { }

Statistic::~Statistic() { }
