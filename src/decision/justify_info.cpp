/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification info.
 */

#include "decision/justify_info.h"

#include <random>

namespace cvc5::internal {
namespace decision {

JustifyInfo::JustifyInfo(context::Context* c)
    : d_node(c),
      d_desiredVal(c, prop::SAT_VALUE_UNKNOWN),
      d_childIndex(c, 0),
      d_childPermSeed(0)
{
}

JustifyInfo::~JustifyInfo() {}

JustifyNode JustifyInfo::getNode() const
{
  return JustifyNode(d_node.get(), d_desiredVal.get());
}

size_t JustifyInfo::getNextChildIndex()
{
  size_t i = d_childIndex.get();
  d_childIndex = d_childIndex + 1;
  return i;
}
void JustifyInfo::revertChildIndex()
{
  Assert(d_childIndex.get() > 0);
  d_childIndex = d_childIndex - 1;
}
void JustifyInfo::ensureChildPermutation(size_t n, uint64_t seed)
{
  if (d_childPerm.size() == n && d_childPermSeed == seed)
  {
    // already have a permutation for this seed and number of children
    return;
  }
  d_childPermSeed = seed;
  // Build a permutation of [0, n) deterministically from the seed, using a
  // local PRNG so that the result depends only on the seed (and hence on the
  // node) and not on any global random state. We use Fisher-Yates shuffle.
  d_childPerm.resize(n);
  for (size_t i = 0; i < n; i++)
  {
    d_childPerm[i] = i;
  }
  std::mt19937_64 rng(seed);
  for (size_t i = n; i > 1;)
  {
    i--;
    std::uniform_int_distribution<size_t> dist(0, i);
    size_t j = dist(rng);
    std::swap(d_childPerm[i], d_childPerm[j]);
  }
}
size_t JustifyInfo::mapChildIndex(size_t i) const
{
  if (d_childPerm.empty() || i >= d_childPerm.size())
  {
    return i;
  }
  return d_childPerm[i];
}
void JustifyInfo::set(TNode n, prop::SatValue desiredVal)
{
  d_node = n;
  d_desiredVal = desiredVal;
  d_childIndex = 0;
  // reset any permutation from a previous use of this object
  d_childPerm.clear();
}

}  // namespace decision
}  // namespace cvc5::internal
