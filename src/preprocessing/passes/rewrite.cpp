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

#include "preprocessing/passes/rewrite.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

Rewrite::Rewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "rewrite"),
      d_proof(options().smt.produceProofs ? new RewriteProofGenerator(d_env)
                                          : nullptr)
{
}

PreprocessingPassResult Rewrite::applyInternal(
  AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    const Node& a = (*assertionsToPreprocess)[i];
    Node ar = rewrite(a);
    assertionsToPreprocess->replace(i, ar, d_proof.get());
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
