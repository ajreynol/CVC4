/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for symbolic regular expression operations.
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "test_smt.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_entail.h"
#include "util/string.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::strings;

namespace test {

class TestTheoryBlackRegexpOperation : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
  }

  void includes(Node r1, Node r2)
  {
    Rewriter* rr = d_slvEngine->getEnv().getRewriter();
    r1 = rr->rewrite(r1);
    r2 = rr->rewrite(r2);
    std::cout << r1 << " includes " << r2 << std::endl;
    ASSERT_TRUE(RegExpEntail::regExpIncludes(r1, r2));
  }

  void doesNotInclude(Node r1, Node r2)
  {
    Rewriter* rr = d_slvEngine->getEnv().getRewriter();
    r1 = rr->rewrite(r1);
    r2 = rr->rewrite(r2);
    std::cout << r1 << " does not include " << r2 << std::endl;
    ASSERT_FALSE(RegExpEntail::regExpIncludes(r1, r2));
  }
};

TEST_F(TestTheoryBlackRegexpOperation, basic)
{
  Node sigma = d_nodeManager->mkNode(Kind::REGEXP_ALLCHAR);
  Node sigmaStar = d_nodeManager->mkNode(Kind::REGEXP_STAR, sigma);
  Node a = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("a")));
  Node c = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("c")));
  Node abc = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                   d_nodeManager->mkConst(String("abc")));
  Node sigma3 = d_nodeManager->mkNode(Kind::REGEXP_CONCAT, sigma, sigma, sigma);
  Node asc = d_nodeManager->mkNode(Kind::REGEXP_CONCAT, a, sigma, c);
  Node asw = d_nodeManager->mkNode(Kind::REGEXP_CONCAT, a, sigma, sigmaStar);

  includes(sigma3, abc);
  doesNotInclude(abc, sigma3);

  includes(sigma3, asc);
  doesNotInclude(asc, sigma3);

  includes(asc, abc);
  doesNotInclude(abc, asc);

  includes(asw, asc);
  doesNotInclude(asc, asw);
}

TEST_F(TestTheoryBlackRegexpOperation, star_wildcards)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node sigma = d_nodeManager->mkNode(Kind::REGEXP_ALLCHAR);
  Node sigmaStar = d_nodeManager->mkNode(Kind::REGEXP_STAR, sigma);
  Node a = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("a")));
  Node c = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("c")));
  Node abc = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                   d_nodeManager->mkConst(String("abc")));

  Node _abc_ =
      d_nodeManager->mkNode(Kind::REGEXP_CONCAT, sigmaStar, abc, sigmaStar);
  Node _asc_ = d_nodeManager->mkNode(Kind::REGEXP_CONCAT,
                                     {sigmaStar, a, sigma, c, sigmaStar});
  Node _sc_ = rr->rewrite(d_nodeManager->mkNode(
      Kind::REGEXP_CONCAT, {sigmaStar, sigma, c, sigmaStar}));
  Node _as_ = rr->rewrite(d_nodeManager->mkNode(
      Kind::REGEXP_CONCAT, {sigmaStar, a, sigma, sigmaStar}));
  Node _assc_ = d_nodeManager->mkNode(
      Kind::REGEXP_CONCAT,
      std::vector<Node>{sigmaStar, a, sigma, sigma, c, sigmaStar});
  Node _csa_ = d_nodeManager->mkNode(Kind::REGEXP_CONCAT,
                                     {sigmaStar, c, sigma, a, sigmaStar});
  Node _c_a_ = d_nodeManager->mkNode(Kind::REGEXP_CONCAT,
                                     {sigmaStar, c, sigmaStar, a, sigmaStar});
  Node _s_s_ = rr->rewrite(d_nodeManager->mkNode(
      Kind::REGEXP_CONCAT, {sigmaStar, sigma, sigmaStar, sigma, sigmaStar}));
  Node _a_abc_ = rr->rewrite(d_nodeManager->mkNode(
      Kind::REGEXP_CONCAT, {sigmaStar, a, sigmaStar, abc, sigmaStar}));

  includes(_asc_, _abc_);
  doesNotInclude(_abc_, _asc_);
  doesNotInclude(_csa_, _abc_);
  doesNotInclude(_assc_, _asc_);
  doesNotInclude(_asc_, _assc_);
  includes(_sc_, abc);
  includes(_sc_, _abc_);
  includes(_sc_, _asc_);
  includes(_sc_, _assc_);
  doesNotInclude(_sc_, _csa_);
  includes(_as_, abc);
  includes(_as_, _abc_);
  includes(_as_, _asc_);
  includes(_as_, _assc_);
  doesNotInclude(_sc_, _csa_);
  includes(_s_s_, _c_a_);
  doesNotInclude(_c_a_, _s_s_);
  includes(_abc_, _a_abc_);
  doesNotInclude(_a_abc_, _abc_);
}

TEST_F(TestTheoryBlackRegexpOperation, generalizedRegExp)
{
  RegExpEntail re(d_nodeManager.get(), nullptr);

  TypeNode strType = d_nodeManager->stringType();
  TypeNode intType = d_nodeManager->integerType();

  Node abc = d_nodeManager->mkConst(String("abc"));
  Node a = d_nodeManager->mkDummySkolem("a", intType);
  Node s = d_nodeManager->mkDummySkolem("s", strType);
  Node fia = d_nodeManager->mkNode(Kind::STRING_ITOS, a);
  Node fils = d_nodeManager->mkNode(
      Kind::STRING_ITOS, d_nodeManager->mkNode(Kind::STRING_LENGTH, s));

  Node sigma = d_nodeManager->mkNode(Kind::REGEXP_ALLCHAR);
  Node sigmaStar = d_nodeManager->mkNode(Kind::REGEXP_STAR, sigma);
  Node rabc = d_nodeManager->mkNode(Kind::STRING_TO_REGEXP,
                                    d_nodeManager->mkConst(String("abc")));
  Node digRange = d_nodeManager->mkNode(Kind::REGEXP_RANGE,
                                        d_nodeManager->mkConst(String("0")),
                                        d_nodeManager->mkConst(String("9")));
  Node digRangeStar = d_nodeManager->mkNode(Kind::REGEXP_STAR, digRange);
  Node digRangePlus =
      d_nodeManager->mkNode(Kind::REGEXP_CONCAT, digRange, digRangeStar);

  ASSERT_TRUE(re.getGeneralizedConstRegExp(s).isNull());
  ASSERT_EQ(re.getGeneralizedConstRegExp(fia), digRangeStar);
  ASSERT_EQ(re.getGeneralizedConstRegExp(fils), digRangePlus);
  ASSERT_EQ(re.getGeneralizedConstRegExp(abc), rabc);

  Node ss = d_nodeManager->mkNode(Kind::STRING_CONCAT, s, s);
  ASSERT_TRUE(re.getGeneralizedConstRegExp(ss).isNull());
}

}  // namespace test
}  // namespace cvc5::internal
