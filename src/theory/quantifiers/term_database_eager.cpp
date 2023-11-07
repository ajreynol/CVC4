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
 * Eager term database
 */

#include "theory/quantifiers/term_database_eager.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermDbEager::TermDbEager(Env& env,
                         QuantifiersState& qs,
                         QuantifiersRegistry& qr,
                         TermDb& tdb)
    : EnvObj(env),
      d_qs(qs),
      d_qreg(qr),
      d_tdb(tdb),
      d_cdalloc(context()),
      d_stats(statisticsRegistry())
{
}

void TermDbEager::assertQuantifier(TNode q)
{
  eager::QuantInfo* qinfo = getQuantInfo(q);
  qinfo->notifyAsserted();
}

void TermDbEager::eqNotifyNewClass(TNode t)
{
  // add to the eager trie
  TNode f = d_tdb.getMatchOperator(t);
  if (!f.isNull())
  {
    eager::FunInfo* finfo = getFunInfo(f);
    if (finfo==nullptr)
    {
      finfo = getOrMkFunInfo(f, t.getNumChildren());
    }
    finfo->addTerm(t);
  }
}

void TermDbEager::eqNotifyMerge(TNode t1, TNode t2) {}

bool TermDbEager::inRelevantDomain(TNode f, size_t i, TNode r)
{
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo==nullptr)
  {
    return false;
  }
  return finfo->inRelevantDomain(i, r);
}

TNode TermDbEager::getCongruentTerm(TNode f, const std::vector<TNode>& args)
{
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo==nullptr)
  {
    return d_null;
  }
  // add using the iterator
  CDTNodeTrieIterator itt(&d_cdalloc, d_qs, &finfo->d_trie, args.size());
  for (TNode a : args)
  {
    if (!itt.push(a))
    {
      // failed
      return d_null;
    }
  }
  return itt.getCurrentData();
}

bool TermDbEager::isCongruent(TNode t) const
{
  return d_cdalloc.isCongruent(t);
}

eager::TriggerInfo* TermDbEager::getTriggerInfo(const Node& t)
{
  std::map<TNode, eager::TriggerInfo>::iterator it = d_tinfo.find(t);
  if (it == d_tinfo.end())
  {
    d_tinfo.emplace(t, *this);
    it = d_tinfo.find(t);
    TNode f = d_tdb.getMatchOperator(t);
    it->second.initialize(t, f);
    // add to triggers for the function
    Assert(!f.isNull());
    ++(d_stats.d_ntriggersUnique);
    eager::FunInfo* finfo = getFunInfo(f);
    finfo->d_triggers.emplace_back(&it->second);
  }
  return &it->second;
}

eager::FunInfo* TermDbEager::getFunInfo(TNode f)
{
  Assert(!f.isNull());
  std::map<TNode, eager::FunInfo>::iterator it = d_finfo.find(f);
  if (it == d_finfo.end())
  {
    return nullptr;
  }
  return &it->second;
}

eager::FunInfo* TermDbEager::getOrMkFunInfo(TNode f, size_t nchild)
{
  Assert(!f.isNull());
  std::map<TNode, eager::FunInfo>::iterator it = d_finfo.find(f);
  if (it == d_finfo.end())
  {
    d_finfo.emplace(f, *this);
    it = d_finfo.find(f);
    it->second.initialize(f, nchild);
  }
  return &it->second;
}

eager::QuantInfo* TermDbEager::getQuantInfo(TNode q)
{
  std::map<TNode, eager::QuantInfo>::iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    d_qinfo.emplace(q, *this);
    it = d_qinfo.find(q);
    it->second.initialize(d_qreg, q);
  }
  return &it->second;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
