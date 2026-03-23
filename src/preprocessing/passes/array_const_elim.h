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
 *
 * Eliminates constant arrays by replacing them with purification skolems and
 * introducing quantified axioms that define all of their select applications.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ARRAY_CONST_ELIM_H
#define CVC5__PREPROCESSING__PASSES__ARRAY_CONST_ELIM_H

#include <unordered_map>
#include <vector>

#include "context/cdhashset.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ArrayConstElim : public PreprocessingPass
{
 public:
  ArrayConstElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /**
   * Eliminate array constants from n, appending any newly introduced axioms to
   * newAsserts.
   */
  Node eliminate(TNode n,
                 std::unordered_map<Node, Node>& visited,
                 std::vector<Node>& newAsserts);
  /**
   * If n is an almost-constant array, collect its default value and store
   * updates and return true.
   *
   * The collected indices and values are in outermost-store-first order.
   */
  bool getArrayConstantDef(TNode n,
                           std::vector<Node>& indices,
                           std::vector<Node>& values,
                           Node& defaultValue) const;

  /** Terms whose defining axioms have already been introduced. */
  context::CDHashSet<Node> d_defined;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__ARRAY_CONST_ELIM_H */
