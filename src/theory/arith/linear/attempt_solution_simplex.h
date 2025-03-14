/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This is an implementation of the Simplex Module for the Simplex for
 * DPLL(T) decision procedure.
 *
 * This implements the Simplex module for the Simpelx for DPLL(T) decision
 * procedure.
 * See the Simplex for DPLL(T) technical report for more background.(citation?)
 * This shares with the theory a Tableau, and a PartialModel that:
 *  - satisfies the equalities in the Tableau, and
 *  - the assignment for the non-basic variables satisfies their bounds.
 * This is required to either produce a conflict or satisifying PartialModel.
 * Further, we require being told when a basic variable updates its value.
 *
 * During the Simplex search we maintain a queue of variables.
 * The queue is required to contain all of the basic variables that voilate
 * their bounds.
 * As elimination from the queue is more efficient to be done lazily,
 * we do not maintain that the queue of variables needs to be only basic
 * variables or only variables that satisfy their bounds.
 *
 * The simplex procedure roughly follows Alberto's thesis. (citation?)
 * There is one round of selecting using a heuristic pivoting rule.
 * (See PreferenceFunction Documentation for the available options.)
 * The non-basic variable is the one that appears in the fewest pivots.
 * (Bruno says that Leonardo invented this first.)
 * After this, Bland's pivot rule is invoked.
 *
 * During this process, we periodically inspect the queue of variables to
 * 1) remove now extraneous extries,
 * 2) detect conflicts that are "waiting" on the queue but may not be detected
 *    by the current queue heuristics, and
 * 3) detect multiple conflicts.
 *
 * Conflicts are greedily slackened to use the weakest bounds that still
 * produce the conflict.
 *
 * Extra things tracked atm: (Subject to change at Tim's whims)
 * - A superset of all of the newly pivoted variables.
 * - A queue of additional conflicts that were discovered by Simplex.
 *   These are theory valid and are currently turned into lemmas
 */

#include "cvc5_private.h"

#pragma once

#include "theory/arith/linear/approx_simplex.h"
#include "theory/arith/linear/simplex.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class AttemptSolutionSDP : public SimplexDecisionProcedure {
public:
 AttemptSolutionSDP(Env& env,
                    LinearEqualityModule& linEq,
                    ErrorSet& errors,
                    RaiseConflict conflictChannel,
                    TempVarMalloc tvmalloc);

 Result::Status attempt(const ApproximateSimplex::Solution& sol);

 Result::Status findModel(bool exactResult) override { Unreachable(); }

private:
 bool matchesNewValue(const DenseMap<DeltaRational>& nv, ArithVar v) const;

 bool processSignals()
 {
   TimerStat& timer = d_statistics.d_queueTime;
   IntStat& conflictStat = d_statistics.d_conflicts;
   return standardProcessSignals(timer, conflictStat);
  }
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    TimerStat d_searchTime;
    TimerStat d_queueTime;
    IntStat d_conflicts;

    Statistics(StatisticsRegistry& sr);
  } d_statistics;
};/* class AttemptSolutionSDP */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
