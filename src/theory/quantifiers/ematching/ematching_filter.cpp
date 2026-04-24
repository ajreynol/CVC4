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

#include "theory/quantifiers/ematching/ematching_filter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EmatchingFilter::EmatchingFilter(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

bool EmatchingFilter::needsCheck(CVC5_UNUSED Theory::Effort e) { return false; }

void EmatchingFilter::check(CVC5_UNUSED Theory::Effort e,
                            CVC5_UNUSED QEffort quant_e)
{
}

void EmatchingFilter::registerQuantifier(Node q)
{
  d_excluded[q] = shouldExclude(q);
}

bool EmatchingFilter::exclude(Node q) const
{
  std::map<Node, bool>::const_iterator it = d_excluded.find(q);
  return it != d_excluded.end() && it->second;
}

std::string EmatchingFilter::identify() const { return "ematching-filter"; }

bool EmatchingFilter::shouldExclude(CVC5_UNUSED Node q) const
{
  // Criteria will be added incrementally. Exclude nothing until then.
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
