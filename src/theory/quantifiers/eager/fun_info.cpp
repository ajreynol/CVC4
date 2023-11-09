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

#if 0
RelDomInfo::RelDomInfo(context::Context* c) : d_dom(c) {}

bool RelDomInfo::hasTerm(QuantifiersState& qs, TNode r)
{
  if (d_dom.find(r) != d_dom.end())
  {
    return true;
  }
  // TODO: check if any have become equal?
  return false;
}
#endif

FunInfo::FunInfo(TermDbEager& tde)
    : d_tde(tde),
      d_trie(tde.getSatContext()),
      d_count(tde.getSatContext(), 0),
      d_active(tde.getSatContext(), false),
      d_terms(tde.getSatContext())
{
}

void FunInfo::initialize(TNode f, size_t nchild)
{
#if 0
  // initialize the relevant domain
  for (size_t i = 0; i < nchild; i++)
  {
    d_rinfo.emplace_back(new RelDomInfo(d_tde.getSatContext()));
  }
#endif
}

bool FunInfo::addTerm(TNode t)
{
  if (!d_active.get())
  {
    // If we are not active, then ignore for now.
    // This is the case if there are no non-ground terms for this function.
    d_terms.push_back(t);
    return false;
  }
  ++(d_tde.getStats().d_ntermsAdded);
  QuantifiersState& qs = d_tde.getState();
  std::vector<TNode> reps;
  for (TNode tc : t)
  {
    reps.emplace_back(qs.getRepresentative(tc));
  }
  // add and refactor the trie
  if (!d_trie.add(d_tde.getCdtAlloc(), qs, reps, t))
  {
    ++(d_tde.getStats().d_ntermsAddedCongruent);
    // congruent
    return false;
  }
  d_count = d_count + 1;
#if 0
  for (size_t i = 0, nchildren = reps.size(); i < nchildren; i++)
  {
    // add relevant domains
    d_rinfo[i]->d_dom.insert(reps[i]);
  }
#endif
  return true;
}

bool FunInfo::inRelevantDomain(size_t i, TNode r)
{
  // TODO: maybe use the trie?

#if 0
  Assert(i < d_rinfo.size());
  Assert(d_tde.getState().getRepresentative(r) == r);
  // must be active
  setActive(true);
  return d_rinfo[i]->hasTerm(d_tde.getState(), r);
#endif
  return true;
}

void FunInfo::setActive(bool active)
{
  if (d_active.get() == active)
  {
    return;
  }
  d_active = active;
  if (active)
  {
    // if activated, add terms now
    refresh();
  }
}

void FunInfo::refresh()
{
  // get and add all terms from the wait list
  std::vector<TNode> next;
  d_terms.get(next);
  for (TNode n : next)
  {
    addTerm(n);
  }
}

CDTNodeTrie* FunInfo::getTrie()
{
  // if someone asks for the trie, we are active
  setActive(true);
  return &d_trie;
}

size_t FunInfo::getNumTerms() const
{
  return d_count.get() + d_terms.getWaitSize();
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
