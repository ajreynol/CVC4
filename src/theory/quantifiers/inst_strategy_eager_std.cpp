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
 * All eager quantifier instantiation
 */

#include "theory/quantifiers/inst_strategy_eager_std.h"

#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyEagerStd::InstStrategyEagerStd(Env& env,
                                           QuantifiersState& qs,
                                           QuantifiersInferenceManager& qim,
                                           QuantifiersRegistry& qr,
                                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr), d_tde(tr.getTermDatabaseEager())
{
  Assert(d_tde != nullptr);
}

void InstStrategyEagerStd::reset_round(Theory::Effort e) {}

bool InstStrategyEagerStd::needsCheck(Theory::Effort e)
{
  return !d_qstate.isInConflict();
}

void InstStrategyEagerStd::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  // just refresh
  //size_t lastWaiting = d_qim.numPendingLemmas();
  Trace("eager-std-engine")
      << "---Eager std Engine Round, effort = " << e << "---" << std::endl;
  d_tde->refresh();
  Trace("eager-std-engine") << "...finished";
  /*
  if (newWaiting>lastWaiting)
  {
    Trace("eager-std-engine") << ", #lemmas=" << (newWaiting-lastWaiting);
  }
  */
  Trace("eager-std-engine") << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
