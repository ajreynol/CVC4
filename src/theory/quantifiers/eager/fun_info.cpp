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

FunInfo::FunInfo(TermDbEager& tde)
    : d_tde(tde),
      d_arity(0),
      d_trie(tde.getSatContext()),
      d_count(tde.getSatContext(), 0),
      d_active(tde.getSatContext(), false),
      d_terms(tde.getSatContext())
{
}

void FunInfo::initialize(TNode f, size_t nchild)
{
  d_op = f;
  d_arity = nchild;
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
  return true;
}

bool FunInfo::notifyTriggers(TNode t, bool isAsserted)
{
  if (!d_active.get() || d_triggers.empty())
  {
    return false;
  }
  // take stats on whether the
  if (isAsserted && d_tde.isStatsEnabled())
  {
    size_t nmatches = 0;
    for (eager::TriggerInfo* tr : d_triggers)
    {
      if (tr->getStatus() == eager::TriggerStatus::ACTIVE)
      {
        nmatches++;
      }
    }
    if (nmatches > 0)
    {
      ++(d_tde.getStats().d_ntermsMatched);
    }
  }
  // notify the triggers with the same top symbol
  for (eager::TriggerInfo* tr : d_triggers)
  {
    Trace("eager-inst-debug")
        << "...notify " << tr->getPattern() << std::endl;
    if (tr->notifyTerm(t, isAsserted))
    {
      Trace("eager-inst")
          << "......conflict " << tr->getPattern() << std::endl;
      return true;
    }
  }
  return false;
}

bool FunInfo::inRelevantDomain(size_t i, TNode r)
{
  // use the trie
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), d_tde.getState(), getTrie(), d_arity);
  size_t level=0;
  while (level<i)
  {
    TNode rc = itt.pushNextChild();
    if (rc.isNull())
    {
      if (level==0)
      {
        return false;
      }
      level--;
    }
    else
    {
      level++;
    }
  }
  return itt.push(r);
}

bool FunInfo::setActive(bool active)
{
  if (d_active.get() == active)
  {
    return false;
  }
  Trace("eager-inst-debug") << "...activate function " << d_op << std::endl;
  d_active = active;
  if (active)
  {
    // if activated, add terms now
    return refresh();
  }
  return false;
}

bool FunInfo::refresh()
{
  // get and add all terms from the wait list
  std::vector<TNode> next;
  d_terms.get(next);
  Trace("eager-inst-debug") << "...lazy add " << next.size() << " terms" << std::endl;
  for (TNode n : next)
  {
    if (!addTerm(n))
    {
      continue;
    }
    // now, notify the triggers, which depends on if n has been asserted in the meantime
    if (notifyTriggers(n, d_tde.isAsserted(n)))
    {
      return true;
    }
  }
  return false;
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

void FunInfo::addTrigger(TriggerInfo* tinfo)
{
  d_triggers.emplace_back(tinfo);
  setActive(true);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
