/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ElimArith preprocessing pass.
 *
 * Converts real operations into integer operations.
 */

#include "preprocessing/passes/elim_arith.h"

#include <string>

#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ElimArithConverter : public NodeConverter
{
 public:
  ElimArithConverter(NodeManager* nm) : NodeConverter(nm) {}

  Node postConvertUntyped(Node orig,
                          const std::vector<Node>& terms,
                          bool termsChanged) override
  {
    return orig;
  }
};

ElimArith::ElimArith(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "elim-arith")
{
}

PreprocessingPassResult ElimArith::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  ElimArithConverter eac(nodeManager());
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node ac = eac.convert(a, false);
    Trace("elim-arith") << "Converted " << a << " to " << ac << std::endl;
    assertionsToPreprocess->replace(i, rewrite(ac));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
