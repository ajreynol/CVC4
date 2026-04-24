/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A conservative filter for excluding quantified formulas from E-matching.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H
#define CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H

#include <map>
#include <vector>

#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * A conservative estimate of quantified formulas for which it is not useful to
 * run E-matching. Quantified formulas excluded by this class should not produce
 * instantiations when E-matching is run on them.
 *
 * The exclusion criteria are intentionally left empty for now so that this
 * class can be wired into the quantifiers pipeline without changing behavior.
 */
class EmatchingFilter : public QuantifiersModule
{
 public:
  EmatchingFilter(Env& env,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);

  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  void registerQuantifier(Node q) override;
  /** Returns true if quantified formula q should be excluded from E-matching. */
  bool exclude(Node q) const;
  /** Identify this module. */
  std::string identify() const override;

 private:
  /** Snapshot current master equality engine events and compute their delta. */
  void updateMasterEqEvents();
  /** Print the current round master equality engine event delta. */
  void traceMasterEqEventDiff(size_t previousSize) const;
  /** Compute whether quantified formula q should be excluded. */
  bool shouldExclude(Node q) const;
  /** Cached exclusion decision per quantified formula. */
  std::map<Node, bool> d_excluded;
  /** Whether we already have a master equality event snapshot. */
  bool d_hasMasterEqEventSnapshot;
  /** The most recent master equality engine event snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventSnapshot;
  /** Events removed from the previous snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventsRemoved;
  /** Events added since the previous snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventsAdded;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H */
