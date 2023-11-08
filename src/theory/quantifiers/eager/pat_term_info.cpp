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

PatTermInfo::PatTermInfo(TermDbEager& tde) : d_tde(tde), d_nbind(0) {}

void PatTermInfo::initialize(TriggerInfo* tr,
                             const Node& t,
                             std::unordered_set<Node>& fvs)
{
  Assert(d_pattern.isNull());
  d_pattern = t;
  d_op = d_tde.getTermDb().getMatchOperator(d_pattern);
  size_t nvarInit = fvs.size();
  // classify each child of the pattern as either variable, compound or ground.
  for (size_t i = 0, nargs = t.getNumChildren(); i < nargs; i++)
  {
    if (expr::hasBoundVar(t[i]))
    {
      bool processed = false;
      if (t[i].getKind() == Kind::BOUND_VARIABLE)
      {
        // if we haven't seen this variable yet
        if (fvs.find(t[i]) == fvs.end())
        {
          processed = true;
          fvs.insert(t[i]);
          d_vargs.emplace_back(i);
          d_children.emplace_back(nullptr);
          d_bindings.emplace_back(1);
        }
      }
      else
      {
        std::unordered_set<Node> fvsTmp = fvs;
        expr::getFreeVariables(t[i], fvsTmp);
        // check if this will bind new variables
        size_t newFvSize = fvsTmp.size() - fvs.size();
        if (newFvSize > 0)
        {
          processed = true;
          d_oargs.emplace_back(i);
          d_children.emplace_back(tr->getPatTermInfo(t[i]));
          // initialize and add to the free variables
          d_children.back()->initialize(tr, t, fvs);
          Assert(fvs.size() == fvsTmp.size());
          d_bindings.emplace_back(newFvSize);
        }
      }
      if (!processed)
      {
        d_gpargs.emplace_back(i);
        d_children.emplace_back(nullptr);
        d_bindings.emplace_back(0);
      }
    }
    else
    {
      d_gargs.emplace_back(i);
      d_children.emplace_back(nullptr);
      d_bindings.emplace_back(0);
    }
  }
  d_nbind = fvs.size() - nvarInit;
  // TODO: as an optimization, could pre-compute the arguments that are expected
  // to already be bound after binding variables. this would catch cases like
  // f(x, a, x) or f(x, g(b, x)).
}

bool PatTermInfo::doMatching(ieval::InstEvaluator* ie, TNode t)
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
  for (size_t i = 0, nvars = d_vargs.size(); i < nvars; i++)
  {
    size_t v = d_vargs[i];
    Assert(ie->get(d_pattern[v]).isNull());
    // if infeasible to assign, we are done
    if (!ie->push(d_pattern[v], t[v]))
    {
      ie->pop(i);
      return false;
    }
  }
  // now, check the terms that are now bound
  for (size_t g : d_gpargs)
  {
    TNode gv = ie->getValue(d_pattern[g]);
    Assert(!gv.isNull());
    // note that gv may be none or some, areEqual should be robust
    if (!qs.areEqual(d_pattern[g], gv))
    {
      ie->pop(d_vargs.size());
      return false;
    }
  }
  // initialize the children to equivalence classes, returning false if its
  // infeasible
  for (size_t o : d_oargs)
  {
    TNode tor = qs.getRepresentative(t[o]);
    if (!d_children[o]->initMatchingEqc(ie, tor))
    {
      ie->pop(d_vargs.size());
      return false;
    }
  }
  size_t noargs = d_oargs.size();
  size_t i = 0;
  while (i < noargs)
  {
    size_t o = d_oargs[i];
    if (!d_children[o]->doMatchingEqcNext(ie))
    {
      if (i == 0)
      {
        // failed
        return false;
      }
      // pop the variables assigned last
      i--;
      ie->pop(d_children[d_oargs[i]]->getNumBindings());
    }
    else
    {
      // successfully matched
      i++;
    }
  }
  return true;
}

bool PatTermInfo::isLegalCandidate(TNode n) const
{
  return d_tde.getTermDb().getMatchOperator(n) == d_op && !d_tde.isCongruent(n);
}

bool PatTermInfo::initMatchingEqc(ieval::InstEvaluator* ie, TNode r)
{
  // otherwise we will match in this equivalence class
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
  return false;
}

bool PatTermInfo::doMatchingEqcNext(ieval::InstEvaluator* ie)
{
  // enumerate terms from the equivalence class with the same operator
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    ++d_eqi;
    if (isLegalCandidate(n))
    {
      if (doMatching(ie, n))
      {
        return true;
      }
    }
  }
  return false;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
