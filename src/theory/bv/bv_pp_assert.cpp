/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Method for handling cases of TheoryBv::ppAssert.
 */

#include "theory/bv/bv_pp_assert.h"

#include "expr/skolem_manager.h"
#include "proof/proof.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

BvPpAssert::BvPpAssert(Env& env, Valuation val) : EnvObj(env), d_valuation(val)
{
}
BvPpAssert::~BvPpAssert() {}
bool BvPpAssert::ppAssert(TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  /**
   * Eliminate extract over bit-vector variables.
   *
   * Given x[h:l] = c, where c is a constant and x is a variable.
   *
   * We rewrite to:
   *
   * x = sk1::c       if l == 0, where bw(sk1) = bw(x)-1-h
   * x = c::sk2       if h == bw(x)-1, where bw(sk2) = l
   * x = sk1::c::sk2  otherwise, where bw(sk1) = bw(x)-1-h and bw(sk2) = l
   */
  Node node = rewrite(tin.getNode());
  if ((node[0].getKind() == Kind::BITVECTOR_EXTRACT && node[1].isConst())
      || (node[1].getKind() == Kind::BITVECTOR_EXTRACT && node[0].isConst()))
  {
    Node extract = node[0].isConst() ? node[1] : node[0];
    if (extract[0].isVar())
    {
      Node c = node[0].isConst() ? node[0] : node[1];

      uint32_t high = utils::getExtractHigh(extract);
      uint32_t low = utils::getExtractLow(extract);
      uint32_t var_bw = utils::getSize(extract[0]);
      std::vector<Node> children;

      SkolemManager* sm = nodeManager()->getSkolemManager();
      // create sk1 with size bw(x)-1-h
      if (low == 0 || high != var_bw - 1)
      {
        Assert(high != var_bw - 1);
        Node ext = utils::mkExtract(extract[0], var_bw - 1, high + 1);
        Node skolem = sm->mkPurifySkolem(ext);
        children.push_back(skolem);
      }

      children.push_back(c);

      // create sk2 with size l
      if (high == var_bw - 1 || low != 0)
      {
        Assert(low != 0);
        Node ext = utils::mkExtract(extract[0], low - 1, 0);
        Node skolem = sm->mkPurifySkolem(ext);
        children.push_back(skolem);
      }

      Node concat = utils::mkConcat(children);
      Assert(utils::getSize(concat) == utils::getSize(extract[0]));
      if (d_valuation.isLegalElimination(extract[0], concat))
      {
        outSubstitutions.addSubstitutionSolved(extract[0], concat, tin);
        return true;
      }
    }
  }
  return false;
}
std::shared_ptr<ProofNode> BvPpAssert::getProofFor(Node fact)
{
  return nullptr;
}

std::string BvPpAssert::identify() const { return "BvPpAssert"; }

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
