/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager quantifiers matching
 */

#include "preprocessing/passes/eager_qmatching.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

EagerQMatching::EagerQMatching(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "eager-qmatching")
{
}

PreprocessingPassResult EagerQMatching::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    if (a.getKind() == Kind::FORALL)
    {
      d_tlQuant.push_back(a);
    }
    processInternal(a);
  }
  // process instantiations
  std::vector<Node> newInst;
  std::map<Node, std::vector<Node> >::iterator itu;
  do
  {
    newInst.clear();
    for (std::pair<const Node, PatInfo>& p : d_pinfo)
    {
      Node pat = p.first;
      itu = d_ufTerms.find(p.getOperator());
      if (itu == d_ufTerms.end())
      {
        continue;
      }
      size_t nuf = itu->second.size();
      for (size_t i = p.second.d_ufIndex; i < nuf; i++)
      {
        std::unordered_map<Node, Node> subs;
        if (expr::match(pat, itu->second[i], subs))
        {
          // new instantiation
        }
      }
      p.second.d_ufIndex = nuf;
    }
    // add new instantiations, collect terms in them
    for (const Node& ni : newInst)
    {
      assertionsToPreprocess->push_back(
          ni, false, nullptr, TrustId::PREPROCESS_EAGER_QMATCHING, true);
      processInternal(ni);
    }
  } while (!newInst.empty());
  return PreprocessingPassResult::NO_CONFLICT;
}

void EagerQMatching::processInternal(const Node& a) {}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
