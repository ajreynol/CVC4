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
 * Function info for eager instantiation
 */

#include "theory/quantifiers/eager/fun_info.h"

#include "theory/quantifiers/eager/trigger_info.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

FunInfo::FunInfo(context::Context* c)
    : d_trie(c), d_count(c, 0), d_active(c, false), d_terms(c)
{
}

void FunInfo::addTerm(TermDbEager& tde, TNode t)
{
  if (!d_active.get())
  {
    d_terms.push_back(t);
    return;
  }
  QuantifiersState& qs = tde.getState();
  std::vector<TNode> reps;
  for (TNode tc : t)
  {
    reps.emplace_back(qs.getRepresentative(tc));
  }
  // add and refactor the trie
  if (!d_trie.add(tde.getCdtAlloc(), qs, reps, t))
  {
    // congruent
    return;
  }
  d_count = d_count + 1;
  for (size_t i = 0, nchildren = reps.size(); i < nchildren; i++)
  {
    // add relevant domains
    addRelevantDomain(i, reps[i]);
  }
  // try matching?
  /*
  for (TriggerInfo* tr : d_triggers)
  {
    tr->doMatching(tde, t);
    // TODO: break?
  }
  */
}

void FunInfo::addRelevantDomain(size_t i, TNode r)
{
  // TODO
}

bool FunInfo::inRelevantDomain(size_t i, TNode r) const { return false; }

void FunInfo::setActive(TermDbEager& tde, bool active)
{
  if (d_active.get() == active)
  {
    return;
  }
  d_active = active;
  if (active)
  {
    // if activated, add terms now
    std::vector<TNode> next;
    d_terms.get(next);
    for (TNode n : next)
    {
      addTerm(tde, n);
    }
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
