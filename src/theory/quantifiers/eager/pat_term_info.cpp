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
#include "theory/uf/theory_uf_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

PatTermInfo::PatTermInfo(TermDbEager& tde) : d_tde(tde), d_nbind(0) {}

void PatTermInfo::initialize(TriggerInfo* tr,
                             const Node& t,
                             std::unordered_set<Node>& fvs,
                             bool bindOrder,
                             bool isTop)
{
  // haven't initialized this yet
  Assert(d_pattern.isNull());
  Assert (t.hasOperator());
  if (expr::hasBoundVar(t.getOperator()))
  {
    // in the rare case we have a free variable in the operator, convert to
    // HO_APPLY.
    d_pattern = uf::TheoryUfRewriter::getHoApplyForApplyUf(t);
  }
  else
  {
    d_pattern = t;
  }
  d_op = d_tde.getTermDb().getMatchOperator(d_pattern);
  size_t nvarInit = fvs.size();
  // Classify each child of the pattern as either variable, compound, ground
  // or ground post-bind.
  // For the latter classification, we pre-compute the arguments that are
  // expected to already be bound after binding variables. This catches cases
  // like f(x, a, x) or f(x, a, g(b, x)) where the 3rd argument in each case
  // is ground post-bind.
  std::vector<size_t> compoundChildren;
  bool useBindOrder = bindOrder && isTop;
  for (size_t i = 0, nargs = d_pattern.getNumChildren(); i < nargs; i++)
  {
    if (expr::hasBoundVar(d_pattern[i]))
    {
      bool processed = false;
      if (d_pattern[i].getKind() == Kind::BOUND_VARIABLE)
      {
        // if we haven't seen this variable yet
        if (fvs.find(d_pattern[i]) == fvs.end())
        {
          processed = true;
          fvs.insert(d_pattern[i]);
          d_vargs.emplace_back(i);
          d_children.emplace_back(nullptr);
          d_bindings.emplace_back(1);
        }
      }
      else if (useBindOrder)
      {
        // if binding in order
        std::unordered_set<Node> fvsTmp = fvs;
        expr::getFreeVariables(d_pattern[i], fvsTmp);
        // check if this will bind new variables
        size_t newFvSize = fvsTmp.size() - fvs.size();
        if (newFvSize > 0)
        {
          processed = true;
          d_oargs.emplace_back(i);
          // note we get the bindOrder version of the trigger, but initialize it
          // with bindOrder false, since we will never use the subpattern for
          // doMatchingAll.
          d_children.emplace_back(tr->getPatTermInfo(d_pattern[i], bindOrder));
          // Initialize the child trigger now. We know this is a new trigger
          // since d_pattern[i] contains new variables we haven't seen before, and thus
          // it is safe to initialize it here.
          d_children.back()->initialize(tr, d_pattern[i], fvs, bindOrder, false);
          Assert(fvs.size() == fvsTmp.size());
          d_bindings.emplace_back(newFvSize);
        }
      }
      else
      {
        processed = true;
        compoundChildren.emplace_back(i);
        // add dummy information for now
        d_children.emplace_back(nullptr);
        d_bindings.emplace_back(0);
      }
      // if does not have a new variable, it is ground post-bind.
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
  if (!useBindOrder)
  {
    // if not binding in order, we go back and compute the compound children now
    std::unordered_set<Node> fvso = fvs;
    for (size_t o : compoundChildren)
    {
      std::unordered_set<Node> fvsCur;
      expr::getFreeVariables(d_pattern[o], fvsCur);
      // check if this will bind new variables, or if it is easy to check
      // post-binding.
      size_t newFvSize = 0;
      bool gpbind = true;
      for (const Node& v : fvsCur)
      {
        if (gpbind && fvso.find(v) == fvso.end())
        {
          // it is not bound after processing the bindings for variables at the
          // current level
          gpbind = false;
        }
        if (fvs.find(v) == fvs.end())
        {
          // it has a new variable that is not bound by any child at this point
          newFvSize++;
        }
      }
      d_bindings[o] = newFvSize;
      if (newFvSize > 0)
      {
        d_oargs.emplace_back(o);
        PatTermInfo* pi = tr->getPatTermInfo(d_pattern[o], bindOrder);
        // Same as above, we will never use this for doMatchingAll, so we set
        // bindOrder to false Initialize the child trigger now, where again
        // we know this is a new pattern term since it contains new variables.
        pi->initialize(tr, d_pattern[o], fvs, bindOrder, false);
        // go back and set the child
        d_children[o] = pi;
      }
      else if (gpbind)
      {
        // add to ground post-bind list
        d_gpargs.emplace_back(o);
      }
      // Note that if gpbind is false, we don't do anything with this child.
      // It will be the case that the instantiation evaluator will evaluate
      // it but we don't do any special checks during matching.
    }
  }
  d_nbind = fvs.size() - nvarInit;
}

bool PatTermInfo::doMatching(ieval::InstEvaluator* ie, TNode t)
{
  // TODO: could set "targets" in the inst evaluator eagerly for compound
  // children
  Trace("eager-inst-matching-debug")
      << "[pat match] " << d_pattern << " " << t << std::endl;
  QuantifiersState& qs = d_tde.getState();
  // ground arguments must match
  for (size_t g : d_gargs)
  {
    if (!qs.areEqual(d_pattern[g], t[g]))
    {
      // infeasible
      Trace("eager-inst-matching-debug")
          << "...failed garg " << d_pattern[g] << " = " << t[g] << std::endl;
      return false;
    }
  }
  // assign variables
  for (size_t i = 0, nvars = d_vargs.size(); i < nvars; i++)
  {
    size_t v = d_vargs[i];
    // should not have assigned it yet
    Assert(ie->get(d_pattern[v]).isNull());
    // if infeasible to assign, we are done
    if (!ie->push(d_pattern[v], t[v]))
    {
      Trace("eager-inst-matching-debug")
          << "...failed assign " << d_pattern[v] << " = " << t[v] << std::endl;
      // clean up
      ie->pop(i);
      return false;
    }
    Trace("eager-inst-matching-debug")
        << "   " << d_pattern[v] << " := " << t[v] << std::endl;
  }
  // now, check the terms that are now bound
  for (size_t g : d_gpargs)
  {
    TNode gv = ie->getValue(d_pattern[g]);
    Assert(!gv.isNull()) << "Subterm " << d_pattern[g]
                         << " expected to be bound at this point";
    // note that gv may be none or some, areEqual should be robust
    if (!qs.areEqual(d_pattern[g], gv))
    {
      Trace("eager-inst-matching-debug")
          << "...failed ground post-bind " << d_pattern[g] << " = " << gv
          << std::endl;
      // clean up
      ie->pop(d_vargs.size());
      return false;
    }
  }
  if (d_oargs.empty())
  {
    return true;
  }
  // initialize the children to equivalence classes, returning false if its
  // infeasible
  for (size_t o : d_oargs)
  {
    TNode tor = qs.getRepresentative(t[o]);
    if (!d_children[o]->initMatchingEqc(ie, tor))
    {
      Trace("eager-inst-matching-debug")
          << "...failed init eqc " << d_pattern[o] << " = " << tor << std::endl;
      // clean up
      ie->pop(d_vargs.size());
      return false;
    }
  }
  size_t noargs = d_oargs.size();
  size_t i = 0;
  size_t o = d_oargs[i];
  while (i < noargs)
  {
    if (!d_children[o]->doMatchingEqcNext(ie))
    {
      if (i == 0)
      {
        // failed, clean up
        ie->pop(d_vargs.size());
        Trace("eager-inst-matching-debug")
            << "...failed compound child" << std::endl;
        return false;
      }
      // pop the variables assigned last
      i--;
      o = d_oargs[i];
      ie->pop(d_children[o]->getNumBindings());
    }
    else
    {
      // successfully matched
      i++;
      o = d_oargs[i];
    }
  }
  Trace("eager-inst-matching-debug") << "...success" << std::endl;
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
