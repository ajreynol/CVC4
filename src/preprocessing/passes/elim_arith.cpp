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
#include "theory/theory.h"
#include "theory/uf/opaque_value.h"
#include "theory/uf/theory_uf_rewriter.h"

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
    TypeNode tn = orig.getType();
    if (orig.isVar())
    {
      TypeNode ctn = convertType(tn);
      if (ctn != tn)
      {
        if (orig.getKind() == Kind::BOUND_VARIABLE)
        {
          return d_nm->mkBoundVar(ctn);
        }
        else
        {
          SkolemManager* sm = d_nm->getSkolemManager();
          return sm->mkInternalSkolemFunction(
              InternalSkolemId::PURIFY_OPAQUE, ctn, {orig});
        }
      }
      return orig;
    }
    else if (orig.isConst() && tn.isRealOrInt())
    {
      return d_nm->mkConst(OpaqueValue(orig));
    }
    else if (!Theory::isLeafOf(orig, THEORY_ARITH))
    {
      TypeNode ctn = convertType(tn);
      std::vector<TypeNode> argTypes;
      for (const Node& t : terms)
      {
        argTypes.push_back(t.getType());
      }
      TypeNode ftype = d_nm->mkFunctionType(argTypes, ctn);
      Node oop = theory::uf::TheoryUfRewriter::getOpaqueOperator(orig, ftype);
      std::vector<Node> oterms;
      oterms.push_back(oop);
      oterms.insert(oterms.end(), terms.begin(), terms.end());
      return d_nm->mkNode(Kind::APPLY_OPAQUE, oterms);
    }
    return orig;
  }
  TypeNode postConvertType(TypeNode tn) override
  {
    if (tn.isRealOrInt())
    {
      return d_nm->mkOpaqueType(tn);
    }
    return tn;
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
