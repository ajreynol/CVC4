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
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(TermDbEager& tde) : d_tde(tde), d_isAllGargs(false), d_arity(0) {}

void TriggerInfo::initialize(const Node& t, const Node& f)
{
  d_pattern = t;
  d_op = f;
  d_arity = t.getNumChildren();
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
  Assert (d_ieval!=nullptr);
  Assert (t.getNumChildren()==d_pattern.getNumChildren());
  Assert (t.getOperator()==d_pattern.getOperator());
  size_t npush = 0;
  bool ret = doMatchingInternal(d_ieval.get(), t, npush);
  if (ret)
  {
    // TODO: add instantiation(s)
  }
  // cleanup the assignment
  d_ieval->pop(npush);
  return ret;
}

bool TriggerInfo::doMatchingInternal(ieval::InstEvaluator* ie, TNode t, size_t& npush)
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
    TNode tv = qs.getRepresentative(t[v]);
    TNode vv = ie->get(d_pattern[v]);
    if (!vv.isNull())
    {
      if (vv!=tv)
      {
        return false;
      }
    }
    else
    {
      // if infeasible to push, we are done
      if (!ie->push(d_pattern[v], tv))
      {
        return false;
      }
      npush++;
      // TODO: remember tv?
    }
  }
  // initialize the children to equivalence classes, returning false if its infeasible
  std::vector<size_t> activeOArgs;
  for (size_t o : d_oargs)
  {
    TNode tor = qs.getRepresentative(t[o]);
    TNode oeqc = d_children[o]->d_eqc;
    // In the rare case we are a (common) subterm, we may already have an assigned eqc.
    // If this does not match, we are infeasible. If this matches, we skip.
    if (!oeqc.isNull())
    {
      if (oeqc!=tor)
      {
        return false;
      }
      continue;
    }
    activeOArgs.emplace_back(o);
    if (!d_children[o]->initMatchingEqc(tor))
    {
      return false;
    }
  }
  size_t noargs = activeOArgs.size();
  std::vector<size_t> pushStack;
  while (pushStack.size()<noargs)
  {
    size_t cnpush = 0;
    size_t o = activeOArgs[pushStack.size()];
    if (!d_children[o]->doMatchingEqcNext(ie, cnpush))
    {
      Assert (cnpush==0);
      if (pushStack.empty())
      {
        return false;
      }
      // pop the variables assigned last
      ie->pop(pushStack.back());
      pushStack.pop_back();
    }
    // matched
    pushStack.push_back(cnpush);
  }
  return true;
}

bool TriggerInfo::initMatchingEqc(TNode r)
{
  // we may be using this trigger in multiple contexts
  if (!d_eqc.isNull())
  {
    // FIXME: distinguish this case!
    return d_eqc==r;
  }
  d_eqc = r;
  TermDb& tdb = d_tde.getTermDb();
  eq::EqualityEngine* ee = d_tde.getState().getEqualityEngine();
  Assert(ee->hasTerm(r));
  d_eqi = eq::EqClassIterator(r, ee);
  // find the first
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    if (tdb.getMatchOperator(n) == d_op)
    {
      // note we don't increment d_eqi, it will be ready when we get next
      return true;
    }
    ++d_eqi;
  }
  return false;
}

bool TriggerInfo::doMatchingEqcNext(ieval::InstEvaluator* ie, size_t& npush)
{
  // enumerate terms from the equivalence class with the same operator
  TermDb& tdb = d_tde.getTermDb();
  while (!d_eqi.isFinished())
  {
    Node n = *d_eqi;
    ++d_eqi;
    if (tdb.getMatchOperator(n) == d_op)
    {
      if (doMatchingInternal(ie, n, npush))
      {
        return true;
      }
    }
  }
  return false;
}

bool TriggerInfo::doMatchingAll()
{
  QuantifiersState& qs = d_tde.getState();
  // now traverse the term index
  FunInfo& finfo = d_tde.getFunInfo(d_op);
  if (!d_isAllGargs)
  {
    // all ground terms must exist
    // NOTE: could also check relevant domain?
    for (size_t g : d_gargs)
    {
      if (!qs.hasTerm(d_pattern[g]))
      {
        return true;
      }
    }
    // note this could be context-depedendent but probably not worthwhile?
    d_isAllGargs = true;
  }
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, &finfo.d_trie, d_arity);
  size_t level = 1;
  std::vector<TNode> matched;
  std::map<size_t, bool> binding;
  std::map<size_t, bool>::iterator itb;
  while (true)
  {
    do
    {
      Assert (level<=d_children.size());
      // if we are a subchild, push next child
      if (d_children[level-1]!=nullptr)
      {
        TNode next = itt.pushNextChild();
        if (next.isNull() || d_children[level-1]->initMatchingEqc(next))
        {
          itt.pop();
        }
        else
        {
          matched.push_back(next);
        }
      }
      else
      {
        TNode pc = d_pattern[level-1];
        TNode r;
        if (pc.getKind()==Kind::BOUND_VARIABLE)
        {
          itb = binding.find(level);
          if (itb==binding.end())
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
          else
          {
            matched.push_back(r);
          }
        }
        else
        {
          r = itt.pushNextChild();
          // if no more children to push, go back a level
          // if the child we just pushed is infeasible, pop to continue on this level
          if (r.isNull() || !d_ieval->push(pc, r))
          {
            // go back a level
            itt.pop();
          }
          else
          {
            matched.push_back(r);
          }
        }
      }
      // processing a new level
      level = itt.getLevel();
      if (level==0)
      {
        return true;
      }
    }while (level<=d_arity);

    // now, match children for the current match
    // FIXME: maybe move up?
    for (size_t o : d_oargs)
    {
      size_t cnpush = 0;
      d_children[o]->doMatchingEqcNext(d_ieval.get(), cnpush);
    }
    // if successful, go back
  }

  return true;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
