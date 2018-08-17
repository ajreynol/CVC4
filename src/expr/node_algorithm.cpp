/*********************                                                        */
/*! \file node_algorithm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable.
 **/

#include "expr/node_algorithm.h"

#include "expr/attribute.h"

namespace CVC4 {
namespace expr {

bool hasSubterm(TNode n, TNode t, bool strict)
{
  if (!strict && n == t)
  {
    return true;
  }

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(n);

  for (unsigned i = 0; i < toProcess.size(); ++i)
  {
    TNode current = toProcess[i];
    if (current.hasOperator() && current.getOperator() == t)
    {
      return true;
    }
    for (unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++j)
    {
      TNode child = current[j];
      if (child == t)
      {
        return true;
      }
      if (visited.find(child) != visited.end())
      {
        continue;
      }
      else
      {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
}

struct HasBoundVarTag
{
};
struct HasBoundVarComputedTag
{
};
/** Attribute true for expressions with bound variables in them */
typedef expr::Attribute<HasBoundVarTag, bool> HasBoundVarAttr;
typedef expr::Attribute<HasBoundVarComputedTag, bool> HasBoundVarComputedAttr;

bool hasBoundVar(TNode n)
{
  if (!n.getAttribute(HasBoundVarComputedAttr()))
  {
    bool hasBv = false;
    if (n.getKind() == kind::BOUND_VARIABLE)
    {
      hasBv = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end() && !hasBv; ++i)
      {
        hasBv = hasBoundVar(*i);
      }
    }
    if (!hasBv && n.hasOperator())
    {
      hasBv = hasBoundVar(n.getOperator());
    }
    n.setAttribute(HasBoundVarAttr(), hasBv);
    n.setAttribute(HasBoundVarComputedAttr(), true);
    Debug("bva") << n << " has bva : " << n.getAttribute(HasBoundVarAttr())
                 << std::endl;
    return hasBv;
  }
  return n.getAttribute(HasBoundVarAttr());
}

bool hasFreeVar(TNode n)
{
  std::unordered_set<TNode, TNodeHashFunction> bound_var;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // can skip if it doesn't have a bound variable
    if (!hasBoundVar(cur))
    {
      continue;
    }
    Kind k = cur.getKind();
    bool isQuant = k == kind::FORALL || k == kind::EXISTS || k == kind::LAMBDA
                   || k == kind::CHOICE;
    std::unordered_map<TNode, bool, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (k == kind::BOUND_VARIABLE)
      {
        if (bound_var.find(cur) == bound_var.end())
        {
          return true;
        }
      }
      else if (isQuant)
      {
        for (const TNode& cn : cur[0])
        {
          // should not shadow
          Assert(bound_var.find(cn) == bound_var.end());
          bound_var.insert(cn);
        }
        visit.push_back(cur);
      }
      // must visit quantifiers again to clean up below
      visited[cur] = !isQuant;
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      for (const TNode& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (!itv->second)
    {
      Assert(isQuant);
      for (const TNode& cn : cur[0])
      {
        bound_var.erase(cn);
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

}  // namespace expr
}  // namespace CVC4
