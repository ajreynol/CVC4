/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The strings eager preprocess utility.
 */

#include "preprocessing/passes/strings_eager_pp.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

StringsEagerPp::StringsEagerPp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "strings-eager-pp"){};

PreprocessingPassResult StringsEagerPp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  theory::strings::SkolemCache skc(nm, nullptr);
  theory::strings::StringsPreprocess pp(d_env, &skc);
  size_t i = 0;
  size_t nasserts = assertionsToPreprocess->size();
  while (i < nasserts)
  {
    Node prev = (*assertionsToPreprocess)[i];
    prev = rewrite(prev);
    assertionsToPreprocess->replace(i, prev);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
    std::vector<TrustNode> asserts;
    TrustNode trn = pp.simplifyTrusted(prev, asserts);
    if (trn.isNull())
    {
      Assert(asserts.empty());
      i++;
      continue;
    }
    assertionsToPreprocess->replaceTrusted(i, trn);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
    for (const TrustNode& ta : asserts)
    {
      assertionsToPreprocess->pushBackTrusted(ta);
    }
    nasserts = assertionsToPreprocess->size();
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
