/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple, commonly-used routines for Boolean simplification.
 */

#include "preprocessing/util/boolean_simplification.h"

namespace cvc5::internal {
namespace preprocessing {

bool BooleanSimplification::push_back_associative_commute_recursive(
    Node n, std::vector<Node>& buffer, Kind k, Kind notK, bool negateNode)
{
  Node::iterator i = n.begin(), end = n.end();
  for (; i != end; ++i)
  {
    Node child = *i;
    if (child.getKind() == k)
    {
      if (!push_back_associative_commute_recursive(
              child, buffer, k, notK, negateNode))
      {
        return false;
      }
    }
    else if (child.getKind() == Kind::NOT && child[0].getKind() == notK)
    {
      if (!push_back_associative_commute_recursive(
              child[0], buffer, notK, k, !negateNode))
      {
        return false;
      }
    }
    else
    {
      if (negateNode)
      {
        if (child.isConst())
        {
          if ((k == Kind::AND && child.getConst<bool>())
              || (k == Kind::OR && !child.getConst<bool>()))
          {
            buffer.clear();
            buffer.push_back(negate(child));
            return false;
          }
        }
        else
        {
          buffer.push_back(negate(child));
        }
      }
      else
      {
        if (child.isConst())
        {
          if ((k == Kind::OR && child.getConst<bool>())
              || (k == Kind::AND && !child.getConst<bool>()))
          {
            buffer.clear();
            buffer.push_back(child);
            return false;
          }
        }
        else
        {
          buffer.push_back(child);
        }
      }
    }
  }
  return true;
} /* BooleanSimplification::push_back_associative_commute_recursive() */

}  // namespace preprocessing
}  // namespace cvc5::internal
