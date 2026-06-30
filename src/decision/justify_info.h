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

#include "cvc5_private.h"

#ifndef CVC5__DECISION__JUSTIFY_INFO_H
#define CVC5__DECISION__JUSTIFY_INFO_H

#include <vector>

#include "context/cdo.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace decision {

/** A pair indicating a node and its desired value */
using JustifyNode = std::pair<TNode, prop::SatValue>;

/**
 * Information concerning a single formula in the justification strategy.
 */
class JustifyInfo
{
 public:
  JustifyInfo(context::Context* c);
  ~JustifyInfo();
  /** set */
  void set(TNode n, prop::SatValue desiredVal);
  /** get node */
  JustifyNode getNode() const;
  /** get next child index, and increment */
  size_t getNextChildIndex();
  /** revert child index */
  void revertChildIndex();
  /**
   * Ensure a permutation of child indices [0, n) is set, which is used when
   * mapping logical child indices to actual child positions. This is used by
   * the randomized justification heuristic to explore the children of
   * symmetric connectives (AND/OR) in a random order.
   *
   * The permutation is built deterministically from the given seed (which the
   * caller derives from the node we are justifying). This determinism is
   * essential for correctness: this object is reused across justify stack
   * slots and the permutation is *not* restored on backtracking (unlike the
   * node, which is context dependent). Hence the same logical child index must
   * always map to the same actual child for a given node, even after the
   * permutation has been overwritten by another node and we backtrack. Keying
   * the permutation on the node (via seed) guarantees this. If a permutation
   * for this seed and size is already set, this is a no-op.
   */
  void ensureChildPermutation(size_t n, uint64_t seed);
  /**
   * Map a logical child index to an actual child position. If a permutation
   * was set via ensureChildPermutation, returns the permuted index; otherwise
   * returns i unchanged.
   */
  size_t mapChildIndex(size_t i) const;

 private:
  /** The node we are considering */
  context::CDO<TNode> d_node;
  /** Desired value */
  context::CDO<prop::SatValue> d_desiredVal;
  /** The child index we are considering */
  context::CDO<size_t> d_childIndex;
  /**
   * An optional permutation of the child indices, used by the randomized
   * justification heuristic. Empty if no permutation is in use, in which case
   * mapChildIndex is the identity. This is a context-independent member: it is
   * reset on each call to set and (re)built deterministically (keyed by the
   * seed of the node) when processing the children of a node, so that it need
   * not be restored on backtracking.
   */
  std::vector<size_t> d_childPerm;
  /** The seed the current d_childPerm was built from. */
  uint64_t d_childPermSeed;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__JUSTIFY_INFO_H */
