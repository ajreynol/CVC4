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
    : d_tde(tde), d_isAllGargs(false), d_arity(0)
{
}

void TriggerInfo::watch(const Node& q, const std::vector<Node>& vlist)
{
  if (d_ieval == nullptr)
  {
    // initialize the evaluator
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
  Node qs = s.apply(q);
  d_ieval->watch(qs);
}

void TriggerInfo::initialize(const Node& t, const Node& f)
{
  d_pattern = t;
  d_op = f;
  d_arity = t.getNumChildren();
  // classify each child of the pattern as either variable, compound or ground.
  for (size_t i = 0, nargs = t.getNumChildren(); i < nargs; i++)
  {
    if (expr::hasBoundVar(t[i]))
    {
      if (t[i].getKind() == Kind::BOUND_VARIABLE)
      {
        d_vargs.emplace_back(i);
        d_children.emplace_back(nullptr);
      }
      else
      {
        d_oargs.emplace_back(i);
        d_children.emplace_back(d_tde.getTriggerInfo(t[i]));
      }
    }
    else
    {
      d_gargs.emplace_back(i);
      d_children.emplace_back(nullptr);
    }
  }
}

bool TriggerInfo::doMatching(TNode t)
{
  Assert(d_ieval != nullptr);
  Assert(t.getNumChildren() == d_pattern.getNumChildren());
  Assert(t.getOperator() == d_pattern.getOperator());
  size_t npush = 0;
  bool ret = doMatchingInternal(d_ieval.get(), t, npush);
  if (ret)
  {
    // TODO: add instantiation(s)
    // cleanup the assignment
    d_ieval->pop(npush);
  }
  return ret;
}

bool TriggerInfo::doMatchingInternal(ieval::InstEvaluator* ie,
                                     TNode t,
                                     size_t& npush)
{
  QuantifiersState& qs = d_tde.getState();
  // ground arguments must match
  for (size_t g : d_gargs)
  {
    if (!qs.areEqual(d_pattern[g], t[g]))
    {
      // infeasible
      return false;
    }
  }
  // assign variables
  for (size_t v : d_vargs)
  {
    TNode vv = ie->get(d_pattern[v]);
    if (!vv.isNull())
    {
      // if already assigned, must be equal
      if (!qs.areEqual(vv, t[v]))
      {
        ie->pop(npush);
        return false;
      }
    }
    else
    {
      // if infeasible to push, we are done
      if (!ie->push(d_pattern[v], t[v]))
      {
        ie->pop(npush);
        return false;
      }
      // increment the number of pushes
      npush++;
    }
  }
  // initialize the children to equivalence classes, returning false if its
  // infeasible
  std::vector<size_t> activeOArgs;
  for (size_t o : d_oargs)
  {
    TNode tor = qs.getRepresentative(t[o]);
    bool isActive = false;
    if (!d_children[o]->initMatchingEqc(tor, isActive))
    {
      ie->pop(npush);
      return false;
    }
    if (isActive)
    {
      activeOArgs.emplace_back(o);
    }
  }
  size_t noargs = activeOArgs.size();
  std::vector<size_t> pushStack;
  while (pushStack.size() < noargs)
  {
    size_t cnpush = 0;
    size_t o = activeOArgs[pushStack.size()];
    if (!d_children[o]->doMatchingEqcNext(ie, cnpush))
    {
      Assert(cnpush == 0);
      if (pushStack.empty())
      {
        // finished
        ie->pop(npush);
        return false;
      }
      // pop the variables assigned last
      ie->pop(pushStack.back());
      pushStack.pop_back();
    }
    // successfully matched
    pushStack.push_back(cnpush);
  }
  // increment npush by sum
  for (size_t cnpush : pushStack)
  {
    npush += cnpush;
  }
  return true;
}

bool TriggerInfo::isLegalCandidate(TNode n) const
{
  return d_tde.getTermDb().getMatchOperator(n) == d_op && !d_tde.isCongruent(n);
}

bool TriggerInfo::initMatchingEqc(TNode r, bool& isActive)
{
  // In the rare case we are a (common) subterm, we may already have an assigned
  // eqc. If this does not match, we are infeasible. If this matches, we don't
  // set isActive and return true.
  if (!d_eqc.isNull())
  {
    return (d_eqc == r);
  }
  isActive = true;
  d_eqc = r;
  eq::EqualityEngine* ee = d_tde.getState().getEqualityEngine();
  Assert(ee->hasTerm(r));
  d_eqi = eq::EqClassIterator(r, ee);
  // find the first
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    if (isLegalCandidate(n))
    {
      // note we don't increment d_eqi, it will be ready when we get next
      return true;
    }
    ++d_eqi;
  }
  d_eqc = Node::null();
  return false;
}

bool TriggerInfo::doMatchingEqcNext(ieval::InstEvaluator* ie, size_t& npush)
{
  // enumerate terms from the equivalence class with the same operator
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    ++d_eqi;
    if (isLegalCandidate(n))
    {
      if (doMatchingInternal(ie, n, npush))
      {
        return true;
      }
    }
  }
  d_eqc = Node::null();
  return false;
}

bool TriggerInfo::doMatchingAll()
{
  QuantifiersState& qs = d_tde.getState();
  // now traverse the term index
  FunInfo* finfo = d_tde.getFunInfo(d_op);
  if (!d_isAllGargs)
  {
    // all ground terms must exist
    // NOTE: could also check relevant domain?
    for (size_t g : d_gargs)
    {
      if (!qs.hasTerm(d_pattern[g]))
      {
        return false;
      }
    }
    // note this could be context-depedendent but probably not worthwhile?
    d_isAllGargs = true;
  }
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, &finfo->d_trie, d_arity);
  size_t level = 1;
  std::map<size_t, bool> binding;
  std::map<size_t, bool>::iterator itb;
  do
  {
    Assert(level <= d_children.size());
    // if we are a compound subchild, push next child
    if (d_children[level - 1] != nullptr)
    {
      TNode next = itt.pushNextChild();
      bool isActive = false;
      if (next.isNull()
          || d_children[level - 1]->initMatchingEqc(next, isActive))
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
  // to ensure the match post-instantiation is syntactic
  TNode data = itt.getCurrentData();
  Assert(!data.isNull());

  return true;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
