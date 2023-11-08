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
 * Pattern term info for eager instantiation
 */

#include "theory/quantifiers/eager/pat_term_info.h"

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "theory/quantifiers/eager/trigger_info.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

PatTermInfo::PatTermInfo(TermDbEager& tde) : d_tde(tde) {}

void PatTermInfo::initialize(TriggerInfo* tr, const Node& t)
{
  d_pattern = t;
  d_op = d_tde.getTermDb().getMatchOperator(d_pattern);
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
        d_children.emplace_back(tr->getPatTermInfo(t[i]));
      }
    }
    else
    {
      d_gargs.emplace_back(i);
      d_children.emplace_back(nullptr);
    }
  }
}

bool PatTermInfo::doMatching(ieval::InstEvaluator* ie, TNode t, size_t& npush)
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

bool PatTermInfo::isLegalCandidate(TNode n) const
{
  return d_tde.getTermDb().getMatchOperator(n) == d_op && !d_tde.isCongruent(n);
}

bool PatTermInfo::initMatchingEqc(TNode r, bool& isActive)
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

bool PatTermInfo::doMatchingEqcNext(ieval::InstEvaluator* ie, size_t& npush)
{
  // enumerate terms from the equivalence class with the same operator
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    ++d_eqi;
    if (isLegalCandidate(n))
    {
      if (doMatching(ie, n, npush))
      {
        return true;
      }
    }
  }
  d_eqc = Node::null();
  return false;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
