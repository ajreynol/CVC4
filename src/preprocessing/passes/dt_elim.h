/******************************************************************************
 * Top contributors (to current version):
 *   Caleb Donovick, Aina Niemetz, Andrew Reynolds
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

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__DT_ELIM_H
#define CVC5__PREPROCESSING__PASSES__DT_ELIM_H

#include "preprocessing/preprocessing_pass.h"
#include "proof/rewrite_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class DtElim : public PreprocessingPass
{
 public:
  DtElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** process internal */
  Node processInternal(const Node& n, std::unordered_set<Node>& visited);
  /** */
  std::unordered_set<TypeNode> d_processed;
  std::vector<TypeNode> d_candidateDt;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DT_ELIM_H */
