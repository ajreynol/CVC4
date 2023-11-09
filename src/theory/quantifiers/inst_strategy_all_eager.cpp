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
  Assert (d_tde!=nullptr);
}

void InstStrategyAllEager::reset_round(Theory::Effort e) 
{
  
}

bool InstStrategyAllEager::needsCheck(Theory::Effort e) 
{
  return !d_tde->inConflict() && (e == Theory::EFFORT_FULL);
}

void InstStrategyAllEager::check(Theory::Effort e, QEffort quant_e) 
{
  // get all remaining instantiations from term database eager
  
}


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

