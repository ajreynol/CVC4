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

#include "theory/quantifiers/inst_strategy_all_eager.h"

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyAllEager::InstStrategyAllEager(Env& env,
                                           QuantifiersState& qs,
                                           QuantifiersInferenceManager& qim,
                                           QuantifiersRegistry& qr,
                                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr), d_tde(tr.getTermDatabaseEager())
{
  Assert(d_tde != nullptr);
}

void InstStrategyAllEager::reset_round(Theory::Effort e) {}

bool InstStrategyAllEager::needsCheck(Theory::Effort e)
{
  return !d_qstate.isInConflict() && (e == Theory::EFFORT_FULL);
}

void InstStrategyAllEager::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  double clSet = 0;
  size_t lastWaiting = 0;
  if (TraceIsOn("all-eager-engine"))
  {
    lastWaiting = d_qim.numPendingLemmas();
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("all-eager-engine")
        << "---All eager Engine Round, effort = " << e << "---" << std::endl;
  }
  std::unordered_set<eager::TriggerInfo*> processed;
  // get all remaining instantiations from term database eager
  FirstOrderModel* fm = d_treg.getModel();
  size_t nquant = fm->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    eager::QuantInfo* qi = d_tde->getQuantInfo(q);
    if (qi == nullptr)
    {
      continue;
    }
    eager::TriggerInfo* ti = qi->getActiveTrigger();
    if (ti == nullptr)
    {
      continue;
    }
    if (processed.find(ti) != processed.end())
    {
      continue;
    }
    processed.insert(ti);
    // do all matching with ti
    if (ti->doMatchingAll())
    {
      Assert(d_qstate.isInConflict());
      break;
    }
  }
  Trace("all-eager-engine-debug")
      << "Processed " << processed.size() << " / " << nquant
      << " quantified formulas" << std::endl;
  if (TraceIsOn("all-eager-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    size_t addedLemmas = (d_qim.numPendingLemmas() - lastWaiting);
    Trace("all-eager-engine")
        << "Finished all eager engine, time = " << (clSet2 - clSet);
    if (addedLemmas > 0)
    {
      Trace("all-eager-engine") << ", addedLemmas = " << addedLemmas;
    }
    if (d_qstate.isInConflict())
    {
      Trace("all-eager-engine") << ", conflict";
    }
    Trace("all-eager-engine") << std::endl;
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
