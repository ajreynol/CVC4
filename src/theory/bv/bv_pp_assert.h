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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_PP_ASSERT_H
#define CVC5__THEORY__BV__BV_PP_ASSERT_H

#include "smt/env_obj.h"
#include "theory/valuation.h"
#include "proof/trust_node.h"
#include "proof/proof_generator.h"

namespace cvc5::internal {
namespace theory {
  
class TrustSubstitutionMap;

namespace bv {

class BvPpAssert : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * Constructor.
   */
  BvPpAssert(Env& env,
              Valuation val);
  ~BvPpAssert();
  /**
   */
  bool ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions);
  /**
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
private:
  /** The valuation proxy. */
  Valuation d_valuation;
};

}
}
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BV_PP_ASSERT_H */
