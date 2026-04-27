/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::internal::SolverEngine.
 */

#include "expr/subtype_elim_node_converter.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "options/options.h"
#include "test_smt.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestMainBlackSolverEngine : public TestSmtNoFinishInit
{
};

TEST_F(TestMainBlackSolverEngine, internal_subsolver_assert_elim_subtypes)
{
  Options opts;
  opts.write_smt().produceProofs = true;
  opts.write_proof().proofElimSubtypes = true;

  d_slvEngine.reset(new SolverEngine(d_nodeManager.get(), &opts));
  d_slvEngine->setIsInternalSubsolver();
  d_slvEngine->setLogic(std::string("ALL"));
  d_slvEngine->finishInit();

  Node x = NodeManager::mkDummySkolem("x", d_nodeManager->integerType());
  Node half = d_nodeManager->mkConstReal(Rational(1, 2));
  Node assertion = d_nodeManager->mkNode(Kind::GT, x, half);

  SubtypeElimNodeConverter senc(d_nodeManager.get());
  Node expected = senc.convert(assertion);
  ASSERT_NE(assertion, expected);

  d_slvEngine->assertFormula(assertion);
  std::vector<Node> assertions = d_slvEngine->getAssertions();
  ASSERT_EQ(assertions.size(), 1);
  EXPECT_EQ(assertions[0], expected);
}

}  // namespace test
}  // namespace cvc5::internal
