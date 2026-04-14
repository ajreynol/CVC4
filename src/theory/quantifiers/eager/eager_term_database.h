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
 * Eager instantiation term database.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TERM_DATABASE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TERM_DATABASE_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * A small incremental term database used by eager instantiation.
 */
class TermDatabase
{
 public:
  /** Clear the database. */
  void clear();
  /**
   * Add term t to the database.
   * Returns true if t was newly added.
   */
  bool addTerm(Node t, Node op);
  /** Return the ground terms for operator op, if any. */
  const std::vector<Node>* getGroundTerms(Node op) const;
  /** Return the number of ground terms for operator op. */
  size_t getNumGroundTerms(Node op) const;

 private:
  /** Terms we have already indexed from notifications. */
  std::map<Node, bool> d_terms;
  /** Indexed ground terms by match operator. */
  std::map<Node, std::vector<Node>> d_opTerms;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
