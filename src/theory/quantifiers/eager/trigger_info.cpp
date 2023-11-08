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
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(TermDbEager& tde)
    : d_tde(tde), d_arity(0), d_root(nullptr), d_status(tde.getSatContext(), TriggerStatus::INACTIVE)
{
}

void TriggerInfo::watch(const Node& q, const std::vector<Node>& vlist)
{
  if (d_ieval == nullptr)
  {
    // initialize the evaluator if not already done so
    d_ieval.reset(new ieval::InstEvaluator(d_tde.getEnv(),
                                           d_tde.getState(),
                                           d_tde.getTermDb(),
                                           ieval::TermEvaluatorMode::PROP));
  }
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
  size_t npush = 0;
  if (!d_root->doMatching(d_ieval.get(), t, npush))
  {
    return false;
  }
  // add instantiation(s)
  std::vector<Node> qinsts = d_ieval->getActiveQuants();
  if (qinsts.size()>1)
  {
    // TODO: maybe try to filter to only the ones with conflicts?
  }
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
  std::map<size_t, bool> binding;
  std::map<size_t, bool>::iterator itb;
  std::vector<PatTermInfo*>& children = d_root->getChildren();
  do
  {
    Assert(level <= children.size());
    // if we are a compound subchild, push next child
    if (children[level - 1] != nullptr)
    {
      TNode next = itt.pushNextChild();
      bool isActive = false;
      if (next.isNull() || children[level - 1]->initMatchingEqc(d_ieval.get(), next, isActive))
      {
        itt.pop();
      }
      else if (isActive)
      {
        // TODO
      }
    }
    else
    {
      TNode pc = d_pattern[level - 1];
      TNode r;
      if (pc.getKind() == Kind::BOUND_VARIABLE)
      {
        itb = binding.find(level);
        if (itb == binding.end())
        {
          // if the first time, check whether we will be binding
          r = d_ieval->get(pc);
          binding[level] = (r.isNull());
        }
        else if (itb->second)
        {
          // otherwise, if we are binding, pop the previous binding.
          // we know that r will be null again
          d_ieval->pop();
        }
        else
        {
          // get its value again
          r = d_ieval->get(pc);
        }
      }
      else
      {
        r = qs.getRepresentative(pc);
      }
      if (!r.isNull())
      {
        if (!itt.push(r))
        {
          // go back a level
          itt.pop();
        }
      }
      else
      {
        r = itt.pushNextChild();
        // if no more children to push, go back a level
        // if the child we just pushed is infeasible, pop to continue on this
        // level
        if (r.isNull() || !d_ieval->push(pc, r))
        {
          // go back a level
          itt.pop();
        }
      }
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

  return true;
}

PatTermInfo* TriggerInfo::getPatTermInfo(TNode p)
{
  std::map<TNode, PatTermInfo>::iterator it = d_pinfo.find(p);
  if (it == d_pinfo.end())
  {
    d_pinfo.emplace(p, d_tde);
    it = d_pinfo.find(p);
    it->second.initialize(this, p);
  }
  return &it->second;
}

void TriggerInfo::resetMatching()
{
  // reset the assignment completely
  d_ieval->resetAll(false);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
