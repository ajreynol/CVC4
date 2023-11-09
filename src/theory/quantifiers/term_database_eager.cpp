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

#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
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
      d_qim(nullptr),
      d_tdb(tdb),
      d_cdalloc(context()),
      d_conflict(context()),
      d_stats(statisticsRegistry())
{
}

void TermDbEager::finishInit(QuantifiersInferenceManager* qim) { d_qim = qim; }

void TermDbEager::assertQuantifier(TNode q)
{
  if (d_conflict.get())
  {
    // already in conflict
    return;
  }
  Trace("eager-inst-notify") << "assertQuantifier: " << q << std::endl;
  eager::QuantInfo* qinfo = getQuantInfo(q);
  if (qinfo->notifyAsserted())
  {
    // trigger initialized which generated conflicting instantiation
    d_conflict = true;
  }
  Trace("eager-inst-notify") << "...finished" << std::endl;
}

void TermDbEager::eqNotifyNewClass(TNode t)
{
  if (d_conflict.get())
  {
    // already in conflict
    return;
  }
  Trace("eager-inst-notify") << "eqNotifyNewClass: " << t << std::endl;
  // add to the eager trie
  TNode f = d_tdb.getMatchOperator(t);
  if (!f.isNull())
  {
    eager::FunInfo* finfo = getFunInfo(f);
    if (finfo == nullptr)
    {
      finfo = getOrMkFunInfo(f, t.getNumChildren());
    }
    if (finfo->addTerm(t))
    {
      std::vector<eager::TriggerInfo*>& ts = finfo->d_triggers;
      // notify the triggers with the same top symbol
      for (eager::TriggerInfo* tr : ts)
      {
        Trace("eager-inst-debug")
            << "...notify " << tr->getPattern() << std::endl;
        if (tr->eqNotifyNewClass(t))
        {
          Trace("eager-inst")
              << "......conflict " << tr->getPattern() << std::endl;
          d_conflict = true;
          break;
        }
      }
    }
  }
  Trace("eager-inst-notify") << "...finished" << std::endl;
}

void TermDbEager::eqNotifyMerge(TNode t1, TNode t2) {
  //Trace("eager-inst-notify") << "eqNotifyMerge: " << t1 << " " << t2 << std::endl;
  //Trace("eager-inst-notify") << "...finished" << std::endl;
}

bool TermDbEager::inRelevantDomain(TNode f, size_t i, TNode r)
{
  return true;
  // relevant domain is likely not worthwhile?
#if 0
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo == nullptr)
  {
    return false;
  }
  return finfo->inRelevantDomain(i, r);
#endif
}

TNode TermDbEager::getCongruentTerm(TNode f, const std::vector<TNode>& args)
{
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo == nullptr)
  {
    return d_null;
  }
  // add using the iterator
  CDTNodeTrieIterator itt(&d_cdalloc, d_qs, finfo->getTrie(), args.size());
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
    Trace("eager-inst-db") << "mkTriggerInfo: " << t << std::endl;
    d_tinfo.emplace(t, *this);
    it = d_tinfo.find(t);
    it->second.initialize(t);
    // add to triggers for the function
    TNode f = d_tdb.getMatchOperator(t);
    Assert(!f.isNull());
    ++(d_stats.d_ntriggersUnique);
    eager::FunInfo* finfo = getOrMkFunInfo(f, t.getNumChildren());
    finfo->d_triggers.emplace_back(&it->second);
    // the initial status of the trigger is determined by whether f has
    // ground terms
    if (finfo->getNumTerms() > 0)
    {
      it->second.setStatus(eager::TriggerStatus::WAIT);
    }
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
    Trace("eager-inst-db") << "mkFunInfo: " << f << std::endl;
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
    Trace("eager-inst-db") << "mkQuantInfo: " << q << std::endl;
    d_qinfo.emplace(q, *this);
    it = d_qinfo.find(q);
    it->second.initialize(d_qreg, q);
  }
  return &it->second;
}

bool TermDbEager::addInstantiation(Node q, std::vector<Node>& terms)
{
  Trace("eager-inst")
      << "addInstantiation: " << q << ", " << terms << std::endl;
  bool ret = d_qim->getInstantiate()->addInstantiation(
      q, terms, InferenceId::QUANTIFIERS_INST_EAGER);
  d_qim->doPending();
  if (!ret)
  {
    Trace("eager-inst") << "...failed!" << std::endl;
    Trace("eager-inst-warn") << "Bad instantiation: " << q << std::endl;
  }
  return ret;
}
//

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
