/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ArrayConstElim preprocessing pass.
 */

#include "preprocessing/passes/array_const_elim.h"

#include "expr/array_store_all.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"

#include <unordered_set>

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ArrayConstElim::ArrayConstElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "array-const-elim"),
      d_defined(userContext())
{
}

PreprocessingPassResult ArrayConstElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  std::vector<Node> newAsserts;
  std::unordered_map<Node, Node> visited;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node next = eliminate(prev, visited, newAsserts);
    if (next != prev)
    {
      assertionsToPreprocess->replace(
          i, next, nullptr, TrustId::PREPROCESS_ARRAY_CONST_ELIM);
      assertionsToPreprocess->ensureRewritten(i);
      Trace("array-const-elim")
          << "*** Preprocess ArrayConstElim " << prev << std::endl;
      Trace("array-const-elim")
          << "   ...got " << (*assertionsToPreprocess)[i] << std::endl;
      if (assertionsToPreprocess->isInConflict())
      {
        return PreprocessingPassResult::CONFLICT;
      }
    }
  }
  for (const Node& na : newAsserts)
  {
    assertionsToPreprocess->push_back(
        na, false, nullptr, TrustId::PREPROCESS_ARRAY_CONST_ELIM_LEMMA, true);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node ArrayConstElim::eliminate(TNode n,
                               std::unordered_map<Node, Node>& visited,
                               std::vector<Node>& newAsserts)
{
  struct ArrayConstInfo
  {
    std::vector<Node> d_indices;
    std::vector<Node> d_values;
    Node d_defaultValue;
  };

  if (visited.find(n) != visited.end())
  {
    return visited[n];
  }

  NodeManager* nm = nodeManager();
  std::unordered_map<Node, ArrayConstInfo> acInfo;
  std::unordered_set<Node> onStack;
  std::vector<TNode> visit;
  visit.push_back(n);
  while (!visit.empty())
  {
    TNode cur = visit.back();
    if (visited.find(cur) != visited.end())
    {
      visit.pop_back();
      continue;
    }
    if (onStack.insert(cur).second)
    {
      ArrayConstInfo aci;
      if (getArrayConstantDef(cur, aci.d_indices, aci.d_values, aci.d_defaultValue))
      {
        acInfo.emplace(cur, std::move(aci));
        visit.push_back(acInfo[cur].d_defaultValue);
        for (const Node& idx : acInfo[cur].d_indices)
        {
          visit.push_back(idx);
        }
        for (const Node& val : acInfo[cur].d_values)
        {
          visit.push_back(val);
        }
        continue;
      }
      if (cur.getNumChildren() == 0)
      {
        visited[cur] = cur;
        visit.pop_back();
        onStack.erase(cur);
        continue;
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
      continue;
    }

    Node ret = cur;
    std::unordered_map<Node, ArrayConstInfo>::const_iterator ita =
        acInfo.find(cur);
    if (ita != acInfo.end())
    {
      Node sk = SkolemManager::mkPurifySkolem(cur);
      if (d_defined.find(cur) == d_defined.end())
      {
        d_defined.insert(cur);
        Node bvar = NodeManager::mkBoundVar(cur.getType().getArrayIndexType());
        Node body = visited[ita->second.d_defaultValue];
        for (size_t i = ita->second.d_indices.size(); i > 0; --i)
        {
          Node idx = visited[ita->second.d_indices[i - 1]];
          Node val = visited[ita->second.d_values[i - 1]];
          body = nm->mkNode(Kind::ITE, bvar.eqNode(idx), val, body);
        }
        Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvar);
        Node sel = nm->mkNode(Kind::SELECT, sk, bvar);
        newAsserts.push_back(nm->mkNode(Kind::FORALL, bvl, sel.eqNode(body)));
        Trace("array-const-elim")
            << "- introduced " << sk << " for " << cur << std::endl;
      }
      ret = sk;
    }
    else
    {
      std::vector<Node> children;
      bool childChanged = false;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        Node nc = visited[cn];
        childChanged = childChanged || nc != cn;
        children.push_back(nc);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
    }
    visited[cur] = ret;
    visit.pop_back();
    onStack.erase(cur);
  }
  return visited[n];
}

bool ArrayConstElim::getArrayConstantDef(TNode n,
                                         std::vector<Node>& indices,
                                         std::vector<Node>& values,
                                         Node& defaultValue) const
{
  if (!n.getType().isArray())
  {
    return false;
  }
  TNode curr = n;
  while (curr.getKind() == Kind::STORE)
  {
    if (!curr[1].isConst() || !curr[2].isConst())
    {
      return false;
    }
    indices.push_back(curr[1]);
    values.push_back(curr[2]);
    curr = curr[0];
  }
  if (curr.getKind() != Kind::STORE_ALL)
  {
    return false;
  }
  defaultValue = curr.getConst<ArrayStoreAll>().getValue();
  return true;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
