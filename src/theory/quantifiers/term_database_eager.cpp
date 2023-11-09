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

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

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
      // we canonize ground subterms if the option is set
      d_tcanon(nullptr, false, true, options().quantifiers.eagerInstMergeTriggers),
      d_stats(statisticsRegistry()),
      d_statsEnabled(options().base.statistics)
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
    Trace("eager-inst-notify") << "...conflict" << std::endl;
  }
  else
  {
    Trace("eager-inst-notify") << "...finished" << std::endl;
  }
}

void TermDbEager::eqNotifyNewClass(TNode t)
{
  if (d_conflict.get())
  {
    // already in conflict
    return;
  }
  if (TermUtil::hasInstConstAttr(t))
  {
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
    ++(d_stats.d_nterms);
    if (finfo->addTerm(t))
    {
      std::vector<eager::TriggerInfo*>& ts = finfo->d_triggers;
      // take stats on whether the
      if (d_statsEnabled)
      {
        size_t nmatches = 0;
        for (eager::TriggerInfo* tr : ts)
        {
          if (tr->getStatus() == eager::TriggerStatus::ACTIVE)
          {
            nmatches++;
          }
        }
        if (nmatches > 0)
        {
          ++(d_stats.d_ntermsMatched);
        }
      }
      // notify the triggers with the same top symbol
      for (eager::TriggerInfo* tr : ts)
      {
        Trace("eager-inst-debug")
            << "...notify " << tr->getPattern() << std::endl;
        if (tr->eqNotifyNewClass(t))
        {
          Trace("eager-inst")
              << "......conflict " << tr->getPattern() << std::endl;
          break;
        }
      }
    }
  }
  Trace("eager-inst-notify") << "...finished" << std::endl;
}

void TermDbEager::eqNotifyMerge(TNode t1, TNode t2)
{
  Trace("eager-inst-notify")
      << "eqNotifyMerge: " << t1 << " " << t2 << std::endl;
  Trace("eager-inst-notify") << "...finished" << std::endl;
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

bool TermDbEager::addInstantiation(Node q,
                                   std::vector<Node>& terms,
                                   bool isConflict)
{
  Trace("eager-inst-debug")
      << "addInstantiation: " << q << ", " << terms << std::endl;
#if 0
  Node inst = d_qim->getInstantiate()->getInstantiation(q, terms);
  if (!isPropagatingInstance(inst))
  {
    AlwaysAssert(false);
  }
#endif
  ++(d_stats.d_inst);
  InferenceId iid = InferenceId::QUANTIFIERS_INST_EAGER;
  if (isConflict)
  {
    d_conflict = true;
    iid = InferenceId::QUANTIFIERS_INST_EAGER_CONFLICT;
  }
  bool ret = d_qim->getInstantiate()->addInstantiation(q, terms, iid);
  if (!ret)
  {
    Assert(!isConflict);
    Trace("eager-inst-debug") << "...failed!" << std::endl;
    Trace("eager-inst-warn") << "Bad instantiation: " << q << std::endl;
  }
  else
  {
    ++(d_stats.d_instSuccess);
    Trace("eager-inst-debug") << "...success!" << std::endl;
    Trace("eager-inst") << "EagerInst: added instantiation " << q << " "
                        << terms << std::endl;
    d_qim->doPending();
  }
  return ret;
}

bool TermDbEager::isPropagatingInstance(Node n)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      if (ck == Kind::FORALL)
      {
        // do nothing
      }
      else if (TermUtil::isBoolConnective(ck))
      {
        for (TNode cc : cur)
        {
          visit.push_back(cc);
        }
      }
      else if (!isPropagatingTerm(cur))
      {
        Trace("eager-inst-warn") << "Not prop due to " << cur << std::endl;
        return false;
      }
    }
  } while (!visit.empty());
  return true;
}

bool TermDbEager::isPropagatingTerm(Node n)
{
  std::unordered_map<TNode, TNode> visited;
  std::unordered_map<TNode, TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  eq::EqualityEngine* ee = d_qs.getEqualityEngine();
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      Node op = d_tdb.getMatchOperator(cur);
      if (op.isNull())
      {
        if (!ee->hasTerm(cur))
        {
          return false;
        }
      }
      else
      {
        // otherwise visit children
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
    }
    else if (it->second.isNull())
    {
      std::vector<TNode> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        children.emplace_back(it->second);
      }
      Node op = d_tdb.getMatchOperator(cur);
      Assert(!op.isNull());
      Node ret = getCongruentTerm(op, children);
      if (ret.isNull())
      {
        return false;
      }
      Assert(ee->hasTerm(ret));
      ret = ee->getRepresentative(ret);
      visited[cur] = ret;
    }
    visit.pop_back();
  } while (!visit.empty());
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
