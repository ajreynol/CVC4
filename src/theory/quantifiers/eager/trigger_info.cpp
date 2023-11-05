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

#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(context::Context* c) {}

void TriggerInfo::initialize(TermDbEager& tde, const Node& t, const Node& f)
{
  d_pattern = t;
  d_op = f;
  for (size_t i = 0, nargs = t.getNumChildren(); i < nargs; i++)
  {
    if (expr::hasBoundVar(t[i]))
    {
      if (t[i].getKind() == Kind::BOUND_VARIABLE)
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

void TriggerInfo::doMatching(TermDbEager& tde, TNode t)
{
  // ground arguments must match
  for (size_t g : d_gargs)
  {
  }
  // assign variables
}

void TriggerInfo::doMatchingEqc(TermDbEager& tde, TNode r)
{
  // enumerate terms from the equivalence class with the same operator
  TermDb& tdb = tde.getTermDb();
  eq::EqualityEngine* ee = tde.getState().getEqualityEngine();
  Assert(ee->hasTerm(r));
  eq::EqClassIterator eqi(r, ee);
  while (!eqi.isFinished())
  {
    Node n = *eqi;
    ++eqi;
    if (tdb.getMatchOperator(n) == d_op)
    {
      doMatching(tde, n);
    }
  }
}

void TriggerInfo::doMatchingAll(TermDbEager& tde)
{
  // all ground terms must be in relevant domain
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
