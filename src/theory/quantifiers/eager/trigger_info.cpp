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
 * Quantifier info for eager instantiation
 */

#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(context::Context* c) {}

void TriggerInfo::initialize(TermDbEager& tde, const Node& t)
{
  d_pattern = t;
  for (size_t i=0, nargs = t.getNumChildren(); i<nargs; i++)
  {
    if (expr::hasBoundVar(t[i]))
    {
      if (t[i].getKind()==Kind::BOUND_VARIABLE)
      {
        d_vargs.emplace_back(i);
      }
      else
      {
        d_oargs.emplace_back(i);
      }
    }
    else
    {
      d_gargs.emplace_back(i);
    }
  }
}

void TriggerInfo::doMatching(TermDbEager& tde, TNode t) {}

void TriggerInfo::doMatchingEqc(TermDbEager& tde, TNode eqc) {}

void TriggerInfo::doMatchingAll(TermDbEager& tde) {}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
