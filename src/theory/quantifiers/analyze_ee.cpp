/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevant domain class.
 */

#include "theory/quantifiers/analyze_ee.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

AnalyzeEqualityEngine::AnalyzeEqualityEngine(Env& env,
                QuantifiersState& qs,
                QuantifiersRegistry& qr,
                TermRegistry& tr);
AnalyzeEqualityEngine::~AnalyzeEqualityEngine() {}

bool AnalyzeEqualityEngine::reset(Theory::Effort e)
{
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
