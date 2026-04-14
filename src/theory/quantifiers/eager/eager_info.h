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
 * Eager instantiation helper types.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_INFO_H

#include <cstdint>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/** A simple atomic pattern term we may eventually match eagerly. */
struct PatternInfo
{
  /** The pattern in instantiation-constant form. */
  Node d_pattern;
  /** The match operator of the pattern. */
  Node d_op;
  /** Instantiation constants occurring in the pattern. */
  std::vector<Node> d_vars;
  /** Nested match operators whose equivalence classes can affect matching. */
  std::vector<Node> d_mergeOps;
  /** Ground subterms whose equivalence classes can affect matching. */
  std::vector<Node> d_groundTerms;
  /** Whether the pattern repeats one of its instantiation constants. */
  bool d_hasRepeatedVar = false;
};

/** A multi-pattern / trigger candidate comprising one or more pattern terms. */
struct TriggerInfo
{
  /** The pattern terms comprising the trigger. */
  std::vector<PatternInfo> d_patterns;
  /** The proof argument describing this trigger. */
  Node d_pfArg;
  /** A stable identifier for this trigger. */
  uint64_t d_id = 0;
  /** The operators watched for this trigger. */
  std::vector<Node> d_watchedOps;
  /** All instantiation constants covered by the trigger. */
  std::vector<Node> d_vars;
  /** Nested match operators watched for equality merges. */
  std::vector<Node> d_mergeOps;
  /** Ground subterms watched for equality merges. */
  std::vector<Node> d_groundTerms;
  /** Whether any equality merge can affect this trigger. */
  bool d_needsAnyMerge = false;
};

/** Quantifier-local eager-inst metadata. */
struct QuantInfo
{
  /** Trigger candidates extracted from its user patterns. */
  std::vector<TriggerInfo> d_triggers;
  /** Operators watched by any trigger candidate. */
  std::vector<Node> d_watchedOps;
  bool empty() const { return d_triggers.empty(); }
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
