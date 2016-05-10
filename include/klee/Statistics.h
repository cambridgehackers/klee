//===-- Statistics.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_STATISTICS_H
#define KLEE_STATISTICS_H

#include "Statistic.h"

#include <vector>
#include <string>
#include <string.h>

namespace klee {
  class Statistic;
  class StatisticRecord {
    friend class StatisticManager;
  public:    
    StatisticRecord() {}
  };

  class StatisticManager {
  private:
    std::vector<Statistic*> stats;
    uint64_t *globalStats;
    uint64_t *indexedStats;
    StatisticRecord *contextStats;
    unsigned index;

  public:
    StatisticManager();
    ~StatisticManager(); 
    void useIndexedStats(unsigned totalIndices); 
    StatisticRecord *getContext();
    void setContext(StatisticRecord *sr); /* null to reset */ 
    void setIndex(unsigned i) { index = i; }
    unsigned getIndex() { return index; }
    unsigned getNumStatistics() { return stats.size(); }
    void incrementIndexedValue(const uint64_t &s, unsigned index, uint64_t addend) const;
    uint64_t getIndexedValue(const uint64_t &s, unsigned index) const;
    void setIndexedValue(const uint64_t &s, unsigned index, uint64_t value);
  };

  extern StatisticManager *theStatisticManager;

  inline StatisticRecord *StatisticManager::getContext() {
    return contextStats;
  }
  inline void StatisticManager::setContext(StatisticRecord *sr) {
    contextStats = sr;
  }

  inline void StatisticManager::incrementIndexedValue(const uint64_t &s, unsigned index, uint64_t addend) const {
    //indexedStats[index*stats.size() + s.id] += addend;
  }

  inline uint64_t StatisticManager::getIndexedValue(const uint64_t &s, unsigned index) const {
    return 0; //indexedStats[index*stats.size() + s.id];
  }

  inline void StatisticManager::setIndexedValue(const uint64_t &s, unsigned index, uint64_t value) {
    //indexedStats[index*stats.size() + s.id] = value;
  }
}

#endif
