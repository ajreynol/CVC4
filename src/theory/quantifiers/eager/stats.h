/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifiers statistics class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__STATS_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__STATS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * Statistics class for quantifiers, which contains all statistics that need
 * to be tracked globally within the quantifiers theory.
 */
class Stats
{
 public:
  Stats(StatisticsRegistry& sr);
  IntStat d_ntriggers;
  IntStat d_ntriggersUnique;
  IntStat d_ntriggersActivated;
  IntStat d_nquant;
  IntStat d_nquantNoTrigger;
  IntStat d_nquantActivated;
  IntStat d_nterms;
  IntStat d_ntermsMatched;
  IntStat d_ntermsAdded;
  IntStat d_ntermsAddedCongruent;
  IntStat d_matches;
  IntStat d_matchesAll;
  IntStat d_matchesSuccess;
  IntStat d_matchesSuccessConflict;
  IntStat d_inst;
  IntStat d_instSuccess;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__STATS_H */
