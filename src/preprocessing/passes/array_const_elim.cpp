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
  std::unordered_map<Node, Node>::const_iterator it = visited.find(n);
  if (it != visited.end())
  {
    return it->second;
  }

  std::vector<Node> indices;
  std::vector<Node> values;
  Node defaultValue;
  if (getArrayConstantDef(n, indices, values, defaultValue))
  {
    NodeManager* nm = nodeManager();
    Node sk = SkolemManager::mkPurifySkolem(n);
    if (d_defined.find(n) == d_defined.end())
    {
      d_defined.insert(n);
      Node bvar = NodeManager::mkBoundVar(n.getType().getArrayIndexType());
      Node body = eliminate(defaultValue, visited, newAsserts);
      for (size_t i = indices.size(); i > 0; --i)
      {
        Node idx = eliminate(indices[i - 1], visited, newAsserts);
        Node val = eliminate(values[i - 1], visited, newAsserts);
        body = nm->mkNode(Kind::ITE, bvar.eqNode(idx), val, body);
      }
      Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvar);
      Node sel = nm->mkNode(Kind::SELECT, sk, bvar);
      newAsserts.push_back(
          nm->mkNode(Kind::FORALL, bvl, sel.eqNode(body)));
      Trace("array-const-elim")
          << "- introduced " << sk << " for " << n << std::endl;
    }
    visited[n] = sk;
    return sk;
  }

  Node ret = n;
  if (n.getNumChildren() > 0)
  {
    std::vector<Node> children;
    bool childChanged = false;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    for (const Node& cn : n)
    {
      Node nc = eliminate(cn, visited, newAsserts);
      childChanged = childChanged || nc != cn;
      children.push_back(nc);
    }
    if (childChanged)
    {
      ret = nodeManager()->mkNode(n.getKind(), children);
    }
  }
  visited[n] = ret;
  return ret;
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
