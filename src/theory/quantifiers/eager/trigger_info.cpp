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
      d_root(nullptr),
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
                                           ieval::TermEvaluatorMode::PROP));
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
  }
  Assert(std::find(d_qinfos.begin(), d_qinfos.end(), qi) == d_qinfos.end());
  d_qinfos.emplace_back(qi);
}

void TriggerInfo::initialize(const Node& t)
{
  d_pattern = t;
  d_op = d_tde.getTermDb().getMatchOperator(t);
  d_arity = t.getNumChildren();
  d_root = getPatTermInfo(t);
}

bool TriggerInfo::doMatching(TNode t, std::map<Node, std::vector<Node>>& inst)
{
  Assert(d_ieval != nullptr);
  Assert(t.getNumChildren() == d_pattern.getNumChildren());
  Assert(t.getOperator() == d_pattern.getOperator());
  resetMatching();
  if (!d_root->doMatching(d_ieval.get(), t))
  {
    return false;
  }
  // add instantiation(s)
  std::vector<Node> qinsts = getQuantsForInst();
  Assert(!qinsts.empty());
  std::map<Node, Node>::iterator itq;
  for (const Node& q : qinsts)
  {
    itq = d_quantMap.find(q);
    Assert(itq != d_quantMap.end());
    inst[itq->second] = d_ieval->getInstantiationFor(q);
  }
  return true;
}

bool TriggerInfo::doMatchingAll(std::map<Node, std::vector<Node>>& inst)
{
  Assert(d_ieval != nullptr);
  resetMatching();
  QuantifiersState& qs = d_tde.getState();
  // now traverse the term index
  FunInfo* finfo = d_tde.getFunInfo(d_op);
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, finfo->getTrie(), d_arity);
  size_t level = 1;
  std::vector<bool> iterAllChild;
  std::vector<PatTermInfo*>& children = d_root->d_children;
  std::vector<size_t>& nbindings = d_root->d_bindings;
  PatTermInfo* pti;
  bool success;
  TNode pc, r;
  do
  {
    Assert(level <= children.size());
    pti = children[level - 1];
    success = true;
    pc = d_pattern[level - 1];
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
      // if r is null
      iterAllChild.push_back(r.isNull());
    }
    else if (iterAllChild[level])
    {
      // otherwise, if we are iterating on children, pop the previous
      // binding(s).
      d_ieval->pop(nbindings[level]);
    }
    else
    {
      // we are not iterating on all children, and thus are done
      success = false;
    }
    if (success)
    {
      if (!r.isNull())
      {
        // if we are traversing a specific child
        success = itt.push(r);
      }
      else
      {
        // we are traversing all children
        r = itt.pushNextChild();
        if (r.isNull())
        {
          // if no more children to push, go back a level
          success = false;
        }
        else if (pc.getKind() == Kind::BOUND_VARIABLE)
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
            success = pti->doMatchingEqcNext(d_ieval.get());
          }
        }
      }
    }
    if (!success)
    {
      // go back a level
      iterAllChild.pop_back();
      itt.pop();
    }
    // processing a new level
    level = itt.getLevel();
    if (level == 0)
    {
      return false;
    }
  } while (level <= d_arity);

  // found an instantiation, we will sanitize it based on the actual term,
  // to ensure the match post-instantiation is syntactic.
  TNode data = itt.getCurrentData();
  Assert(!data.isNull());
  Assert(data.getNumChildren() == d_pattern.getNumChildren());
  std::vector<Node> qinsts = getQuantsForInst();
  Assert(!qinsts.empty());
  // compute the backwards map
  std::map<Node, Node> varToTerm;
  std::vector<size_t>& vargs = d_root->d_vargs;
  for (size_t v : vargs)
  {
    Assert(v < d_pattern.getNumChildren());
    varToTerm[d_pattern[v]] = data[v];
  }

  return true;
}

PatTermInfo* TriggerInfo::getPatTermInfo(TNode p)
{
  std::map<TNode, PatTermInfo>::iterator it = d_pinfo.find(p);
  if (it == d_pinfo.end())
  {
    d_pinfo.emplace(p, d_tde);
    it = d_pinfo.find(p);
  }
  return &it->second;
}

void TriggerInfo::resetMatching()
{
  // reset the assignment completely
  d_ieval->resetAll(false);
}

std::vector<Node> TriggerInfo::getQuantsForInst() const
{
  std::vector<Node> qinsts = d_ieval->getActiveQuants();
  if (qinsts.size() > 1)
  {
    // try to filter to only the ones with conflicts
    std::vector<Node> qinstsc = d_ieval->getActiveQuants(true);
    if (!qinstsc.empty() && qinstsc.size() < qinsts.size())
    {
      return qinstsc;
    }
  }
  return qinsts;
}

void TriggerInfo::eqNotifyNewClass(TNode t)
{
  if (d_status.get() == TriggerStatus::INACTIVE)
  {
    setStatus(TriggerStatus::WAIT);
  }
}

void TriggerInfo::setStatus(TriggerStatus s)
{
  if (d_status.get() == s)
  {
    return;
  }
  d_status = s;
  // notify that we've changed status
  for (QuantInfo* qi : d_qinfos)
  {
    qi->notifyTriggerStatus(this, s);
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
