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
      d_status(tde.getSatContext(), TriggerStatus::INACTIVE)
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
                                           ieval::TermEvaluatorMode::PROP, false, false, false, true));
  }
  else
  {
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
  for (size_t i=0; i<2; i++)
  {
    bool bindOrder = (i==0);
    PatTermInfo* pi = getPatTermInfo(t, bindOrder);
    std::unordered_set<Node> fvs;
    pi->initialize(this, d_pattern, fvs, bindOrder, true);
    d_root[i] = pi;
    if (i==0 && pi->d_oargs.empty())
    {
      // if simple trigger, doesn't make a difference
      d_root[1] = pi;
      break;
    }
  }
}

bool TriggerInfo::doMatching(TNode t)
{
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
  Assert(!qinsts.empty());
  std::map<Node, Node>::iterator itq;
  for (const Node& q : qinsts)
  {
    itq = d_quantMap.find(q);
    Assert(itq != d_quantMap.end());
    std::vector<Node> inst = d_ieval->getInstantiationFor(q);
    d_tde.addInstantiation(itq->second, inst);
  }
  return isConflict;
}

bool TriggerInfo::doMatchingAll()
{
  Trace("eager-inst-matching") << "doMatchingAll " << d_pattern << std::endl;
  Assert(d_ieval != nullptr);
  if (!resetMatching())
  {
    Trace("eager-inst-matching-debug") << "...failed reset" << std::endl;
    return false;
  }
  QuantifiersState& qs = d_tde.getState();
  // now traverse the term index
  FunInfo* finfo = d_tde.getFunInfo(d_op);
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, finfo->getTrie(), d_arity);
  size_t level = 0;
  std::vector<bool> iterAllChild;
  PatTermInfo* root = d_root[0];
  std::vector<PatTermInfo*>& children = root->d_children;
  Assert (children.size()==d_pattern.getNumChildren()) << "child mismatch " << children.size() << " " << d_pattern.getNumChildren();
  std::vector<size_t>& nbindings = root->d_bindings;
  PatTermInfo* pti;
  bool success;
  TNode pc, r, null;
  do
  {
    Assert(level < children.size());
    pti = children[level];
    success = true;
    pc = d_pattern[level];
    Assert(level <= iterAllChild.size());
    if (level == iterAllChild.size())
    {
      // determine if there is a specific child we are traversing to
      if (pti != nullptr || pc.getKind() == Kind::BOUND_VARIABLE)
      {
        // if a non-ground term, we check whether we already have a value based
        // on the evaluator utility.
        // note this will typically be null if we are a compound child, although
        // it may also be "none".
        r = d_ieval->getValue(pc);
      }
      else
      {
        // if a ground term, use the representative method directly
        r = qs.getRepresentative(pc);
      }
      Trace("eager-inst-matching-debug") << "[level " << level << "] traverse " << r << std::endl;
      // if r is null
      iterAllChild.push_back(r.isNull());
    }
    else if (iterAllChild[level])
    {
      // otherwise, if we are iterating on children, pop the previous
      // binding(s).
      d_ieval->pop(nbindings[level]);
      r = null;
    }
    else
    {
      // we are not iterating on all children, and thus are done
      success = false;
      iterAllChild.pop_back();
    }
    if (success)
    {
      if (!r.isNull())
      {
        // if we are traversing a specific child
        if (!itt.push(r))
        {
          // fail, go back a level
          success = false;
          iterAllChild.pop_back();
        }
        else
        {
          level++;
        }
        Trace("eager-inst-matching-debug") << "...success=" << success << std::endl;
        Trace("ajr-temp") << "push now " << itt.getLevel() << std::endl;
      }
      else
      {
        // we are traversing all children
        r = itt.pushNextChild();
        Trace("eager-inst-matching-debug") << "[level " << level << "] next child " << r << std::endl;
        Trace("ajr-temp") << "push now " << itt.getLevel() << std::endl;
        if (r.isNull())
        {
          // if no more children to push, go back a level
          success = false;
          iterAllChild.pop_back();
        }
        else
        {
          level++;
          if (pc.getKind() == Kind::BOUND_VARIABLE)
          {
            // if we are a bound variable, we try to bind
            success = d_ieval->push(pc, r);
          }
          else
          {
            Assert(pti != nullptr);
            // if we are a compound child, we try to match in the eqc
            success = pti->initMatchingEqc(d_ieval.get(), r);
            if (success)
            {
              // NOTE: only single term is matched, could iterate on this
              success = pti->doMatchingEqcNext(d_ieval.get());
            }
          }
        }
        Trace("eager-inst-matching-debug") << "...success=" << success << std::endl;
      }
    }
    if (!success)
    {
      // go back a level
      itt.pop();
      Trace("ajr-temp") << "pop now " << itt.getLevel() << std::endl;
      if (level==0)
      {
        Trace("eager-inst-matching-debug") << "...failed matching" << std::endl;
        return false;
      }
      level--;
    }
  } while (level < d_arity);

  // found an instantiation, we will sanitize it based on the actual term,
  // to ensure the match post-instantiation is syntactic.
  TNode data = itt.getCurrentData();
  Assert(!data.isNull());
  Assert(data.getNumChildren() == d_pattern.getNumChildren());
  bool isConflict = false;
  std::vector<Node> qinsts = d_ieval->getActiveQuants(isConflict);
  Assert(!qinsts.empty());
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
    d_tde.addInstantiation(q, inst);
  }
  return isConflict;
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

bool TriggerInfo::eqNotifyNewClass(TNode t)
{
  switch (d_status.get())
  {
    case TriggerStatus::ACTIVE:
      // do the matching against term t
      return doMatching(t);
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
