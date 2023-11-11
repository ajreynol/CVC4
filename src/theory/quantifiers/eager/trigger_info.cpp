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
#include "expr/subs.h"
#include "theory/quantifiers/eager/quant_info.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(TermDbEager& tde)
    : d_tde(tde),
      d_arity(0),
      d_root{nullptr, nullptr},
      d_status(tde.getSatContext(), TriggerStatus::INACTIVE),
      d_hasActivated(false)
{
}

void TriggerInfo::watch(QuantInfo* qi, const std::vector<Node>& vlist)
{
  if (d_ieval == nullptr)
  {
    // initialize the evaluator if not already done so
    d_ieval.reset(new ieval::InstEvaluator(d_tde.getEnv(),
                                           d_tde.getState(),
                                           d_tde.getTermDb(),
                                           ieval::TermEvaluatorMode::PROP,
                                           false,
                                           false,
                                           false,
                                           true));
  }
  else
  {
    // otherwise, ensure we are reset
    d_ieval->resetAll(false);
  }
  Node q = qi->getQuant();
  Assert(q.getKind() == Kind::FORALL);
  Assert(vlist.size() == q[0].getNumChildren());
  Subs s;
  for (size_t i = 0, nvars = vlist.size(); i < nvars; i++)
  {
    s.add(q[0][i], vlist[i]);
  }
  // rename quantified formula based on the variable list
  Node qs = s.apply(q);
  // this should probably always hold, or else we have a duplicate trigger
  // for the same quantified formula.
  if (d_quantMap.find(qs) == d_quantMap.end())
  {
    d_ieval->watch(qs);
    d_quantMap[qs] = q;
    d_quantRMap[q] = qs;
  }
  // a quantified formula may be signed up to watch the same term from
  // different vars, e.g. P(v1,v2) for forall xy. P(x,y) V P(y,x) V Q(x,y).
  if (std::find(d_qinfos.begin(), d_qinfos.end(), qi) == d_qinfos.end())
  {
    d_qinfos.emplace_back(qi);
  }
}

void TriggerInfo::initialize(const Node& t)
{
  d_pattern = t;
  d_op = d_tde.getTermDb().getMatchOperator(t);
  d_arity = t.getNumChildren();
  for (size_t i = 0; i < 2; i++)
  {
    bool bindOrder = (i == 0);
    PatTermInfo* pi = getPatTermInfo(t, bindOrder);
    std::unordered_set<Node> fvs;
    pi->initialize(this, d_pattern, fvs, bindOrder, true);
    d_root[i] = pi;
    if (i == 0 && pi->d_oargs.empty() && pi->d_gpargs.empty())
    {
      // if simple trigger, doesn't make a difference
      d_root[1] = pi;
      break;
    }
  }
}

bool TriggerInfo::doMatching(TNode t)
{
  Stats& stats = d_tde.getStats();
  ++(stats.d_matches);
  Trace("eager-inst-matching")
      << "doMatching " << d_pattern << " " << t << std::endl;
  Assert(d_ieval != nullptr);
  Assert(t.getNumChildren() == d_pattern.getNumChildren());
  Assert(t.getOperator() == d_pattern.getOperator());
  if (!resetMatching())
  {
    Trace("eager-inst-matching-debug") << "...failed reset" << std::endl;
    return false;
  }
  if (!d_root[1]->doMatching(d_ieval.get(), t))
  {
    Trace("eager-inst-matching-debug") << "...failed matching" << std::endl;
    return false;
  }
  // add instantiation(s)
  bool isConflict = false;
  std::vector<Node> qinsts = d_ieval->getActiveQuants(isConflict);
  Trace("eager-inst-matching-debug")
      << "...success, #quant=" << qinsts.size() << ", conflict=" << isConflict
      << std::endl;
  if (qinsts.empty())
  {
    return false;
  }
  ++(stats.d_matchesSuccess);
  if (isConflict)
  {
    ++(stats.d_matchesSuccessConflict);
  }
  std::map<Node, Node>::iterator itq;
  for (const Node& q : qinsts)
  {
    itq = d_quantMap.find(q);
    Assert(itq != d_quantMap.end());
    std::vector<Node> inst = d_ieval->getInstantiationFor(q);
    d_tde.addInstantiation(itq->second, inst, isConflict);
  }
  return isConflict;
}

bool TriggerInfo::doMatchingAll()
{
  Stats& stats = d_tde.getStats();
  ++(stats.d_matchesAll);
  ++(stats.d_matches);
  Trace("eager-inst-matching") << "doMatchingAll " << d_pattern << std::endl;
  Assert(d_ieval != nullptr);
  if (!resetMatching())
  {
    Trace("eager-inst-matching-debug") << "...failed reset" << std::endl;
    return false;
  }
  FunInfo* finfo = d_tde.getFunInfo(d_op);
  QuantifiersState& qs = d_tde.getState();
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, finfo->getTrie(), d_arity);
  PatTermInfo* root = d_root[0];
  // found an instantiation, we will sanitize it based on the actual term,
  // to ensure the match post-instantiation is syntactic.
  TNode data = root->doMatchingAll(d_ieval.get(), itt);
  if (data.isNull())
  {
    return false;
  }
  Assert(data.getNumChildren() == d_pattern.getNumChildren());
  bool isConflict = false;
  std::vector<Node> qinsts = d_ieval->getActiveQuants(isConflict);
  if (qinsts.empty())
  {
    Assert(false);
    return false;
  }
  ++(stats.d_matchesSuccess);
  if (isConflict)
  {
    ++(stats.d_matchesSuccessConflict);
  }
  Trace("eager-inst-matching-debug")
      << "...success, #quant=" << qinsts.size() << ", conflict=" << isConflict
      << std::endl;
  // compute the backwards map
  std::map<Node, Node> varToTerm;
  std::vector<size_t>& vargs = root->d_vargs;
  for (size_t v : vargs)
  {
    Assert(v < d_pattern.getNumChildren());
    varToTerm[d_pattern[v]] = data[v];
  }
  std::map<Node, Node>::iterator it;
  for (const Node& qi : qinsts)
  {
    it = d_quantMap.find(qi);
    Assert(it != d_quantMap.end());
    Node q = it->second;
    std::vector<Node> inst;
    for (const Node& v : qi[0])
    {
      it = varToTerm.find(v);
      if (it != varToTerm.end())
      {
        inst.emplace_back(it->second);
      }
      else
      {
        inst.emplace_back(d_ieval->get(v));
      }
    }
    d_tde.addInstantiation(q, inst, isConflict);
  }
  if (isConflict)
  {
    return true;
  }
  // pop the leaf
  itt.pop();
  return false;
}

PatTermInfo* TriggerInfo::getPatTermInfo(TNode p, bool bindOrder)
{
  std::map<TNode, PatTermInfo>& pi = d_pinfo[bindOrder ? 1 : 0];
  std::map<TNode, PatTermInfo>::iterator it = pi.find(p);
  if (it == pi.end())
  {
    pi.emplace(p, d_tde);
    it = pi.find(p);
  }
  return &it->second;
}

bool TriggerInfo::resetMatching()
{
  // reset the assignment completely
  d_ieval->resetAll(false);
  // now, ensure we don't watch quantified formulas that are no longer asserted
  bool success = false;
  for (QuantInfo* qi : d_qinfos)
  {
    if (!qi->isAsserted())
    {
      Node q = qi->getQuant();
      Assert(d_quantRMap.find(q) != d_quantRMap.end());
      d_ieval->deactivate(d_quantRMap[q]);
    }
    else
    {
      success = true;
    }
  }
  // success if at least one is asserted
  return success;
}

bool TriggerInfo::notifyTerm(TNode t, bool isAsserted)
{
  switch (d_status.get())
  {
    case TriggerStatus::ACTIVE:
      // Do the matching against term t, only if it is marked as asserted.
      // This may be notified when
      // (1) t is a new eqc and eagerInstWhenAsserted is false.
      // (2) t appears as a (subterm of a) term in a merge and eagerInstWhenAsserted is true.
      if (isAsserted)
      {
        return doMatching(t);
      }
      break;
    case TriggerStatus::INACTIVE:
      // we are now waiting to be activated
      return setStatus(TriggerStatus::WAIT);
    default: break;
  }
  return false;
}

bool TriggerInfo::setStatus(TriggerStatus s)
{
  bool isEmpty = d_statusToProc.empty();
  d_statusToProc.emplace_back(s);
  // avoid reentry
  if (!isEmpty)
  {
    return false;
  }
  size_t i = 0;
  while (i < d_statusToProc.size())
  {
    s = d_statusToProc[i];
    i++;
    if (d_status == s)
    {
      // no change in status
      continue;
    }
    d_status = s;
    if (s == TriggerStatus::ACTIVE && !d_hasActivated)
    {
      d_hasActivated = true;
      ++(d_tde.getStats().d_ntriggersActivated);
    }
    i++;
    // notify that we've changed status to s
    for (QuantInfo* qi : d_qinfos)
    {
      if (qi->notifyTriggerStatus(this, s))
      {
        // conflict discovered
        d_statusToProc.clear();
        return true;
      }
    }
  }
  d_statusToProc.clear();
  return false;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
