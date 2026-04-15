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

#include <memory>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/** Context-dependent list of nodes. */
class NodeList
{
 public:
  NodeList(context::Context* c) : d_list(c) {}
  /** The list. */
  context::CDList<Node> d_list;
};

/**
 * A small incremental term database used by eager instantiation.
 */
class TermDatabase
{
  using NodeSet = context::CDHashSet<Node>;
  using NodeListMap = context::CDHashMap<Node, std::shared_ptr<NodeList>>;

 public:
  TermDatabase(context::Context* c);
  /**
   * Add term t to the database.
   * Returns true if t was newly added.
   */
  bool addTerm(Node t, Node op);
  /** Return the ground terms for operator op, if any. */
  const NodeList* getGroundTerms(Node op) const;
  /** Return the number of ground terms for operator op. */
  size_t getNumGroundTerms(Node op) const;
  /** Add parent operator op for term t. */
  void addParentOperator(Node t, Node op);
  /** Return the parent operators for term t, if any. */
  const NodeList* getParentOperators(Node t) const;

 private:
  /** Get or make the list in map for key. */
  NodeList* getOrMkList(NodeListMap& map, Node key);
  /** Terms we have already indexed from notifications. */
  NodeSet d_terms;
  /** Indexed ground terms by match operator. */
  NodeListMap d_opTerms;
  /** Reverse index from a term to parent operators that contain it. */
  NodeListMap d_parentOps;
  /** SAT context. */
  context::Context* d_context;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
