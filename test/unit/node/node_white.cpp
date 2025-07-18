/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::Node.
 */

#include <string>

#include "base/check.h"
#include "expr/node_builder.h"
#include "test_node.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace expr;

namespace test {

class TestNodeWhiteNode : public TestNode
{
};

TEST_F(TestNodeWhiteNode, null) { ASSERT_EQ(Node::null(), Node::s_null); }

TEST_F(TestNodeWhiteNode, copy_ctor) { Node e(Node::s_null); }

TEST_F(TestNodeWhiteNode, builder)
{
  NodeBuilder b(d_nodeManager.get());
  ASSERT_TRUE(b.d_nv->getId() == 0);
  ASSERT_TRUE(b.d_nv->getKind() == Kind::UNDEFINED_KIND);
  ASSERT_EQ(b.d_nv->d_nchildren, 0u);
  /* etc. */
}

TEST_F(TestNodeWhiteNode, iterators)
{
  Node x = d_nodeManager->mkVar("x", d_nodeManager->integerType());
  Node y = d_nodeManager->mkVar("y", d_nodeManager->integerType());
  Node x_plus_y = d_nodeManager->mkNode(Kind::ADD, x, y);
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node x_times_2 = d_nodeManager->mkNode(Kind::MULT, x, two);

  Node n = d_nodeManager->mkNode(Kind::ADD, x_times_2, x_plus_y, y);

  Node::iterator i;

  i = std::find(n.begin(), n.end(), x_plus_y);
  ASSERT_TRUE(i != n.end());
  ASSERT_TRUE(*i == x_plus_y);

  i = std::find(n.begin(), n.end(), x);
  ASSERT_TRUE(i == n.end());

  i = std::find(x_times_2.begin(), x_times_2.end(), two);
  ASSERT_TRUE(i != x_times_2.end());
  ASSERT_TRUE(*i == two);

  i = std::find(n.begin(), n.end(), y);
  ASSERT_TRUE(i != n.end());
  ASSERT_TRUE(*i == y);

  std::vector<Node> v;
  copy(n.begin(), n.end(), back_inserter(v));
  ASSERT_EQ(n.getNumChildren(), v.size());
  ASSERT_EQ(3, v.size());
  ASSERT_EQ(v[0], x_times_2);
  ASSERT_EQ(v[1], x_plus_y);
  ASSERT_EQ(v[2], y);
}
}  // namespace test
}  // namespace cvc5::internal
