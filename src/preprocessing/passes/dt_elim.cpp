/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Caleb Donovick, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewrite preprocessing pass.
 *
 * Calls the rewriter on every assertion.
 */

#include "preprocessing/passes/dt_elim.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

DtElim::DtElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "dt-elim")
{
}

Node DtElim::processInternal(const Node& n, std::unordered_set<Node>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end()) {
      visited.insert(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
      Kind k = n.getKind();
      TypeNode tn;
      if (k==Kind::APPLY_CONSTRUCTOR)
      {
        tn = n.getType();
      }
      else if(k==Kind::APPLY_SELECTOR || k==Kind::APPLY_TESTER)
      {
        tn = n[0].getType();
      }
      if (!tn.isNull())
      {
        
      }
    }
  } while (!visit.empty());
  return n;
}
  
PreprocessingPassResult DtElim::applyInternal(
  AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_set<Node> visited;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    const Node& a = (*assertionsToPreprocess)[i];
    Node ar = processInternal(a,visited);
    assertionsToPreprocess->replace(i, ar);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
