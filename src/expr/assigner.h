/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An assigner
 */

#include "cvc5_public.h"

#ifndef CVC5__ASSIGNER_H
#define CVC5__ASSIGNER_H

#include <iosfwd>
#include <memory>

#include "expr/node.h"

namespace cvc5::internal {

class Assigner
{
 public:
  /** */
  Assigner(const Node& n);
  ~Assigner() {}
  bool isValid() const;
  const Node& getNode() const;
  const Node& getSatLiteral() const;
  const std::vector<Node>& getVariables() const;
  size_t variableIndexOf(const Node& v) const;
  const std::vector<Node>& getAssignments(const Node& v) const;
  const std::map<Node, std::vector<size_t>>& getAssignmentMap() const;
  std::map<Node, std::vector<size_t>> getAssignmentMapProjection(
      const std::vector<size_t>& cols) const;
  const std::vector<Node>& getLiterals() const;
  bool hasVariable(const Node& v) const;
  static bool isAssigner(const Node& n);
  static bool isLiteralCube(const Node& n, std::vector<Node>& cc);
  static bool isLiteralCube(const Node& n);
  static Node getSatLiteral(const Node& n);
  static bool isAssignEq(const Node& n, Node& v, Node& c);
  static bool isVarElimEq(const Node& n, Node& v, Node& s);

 private:
  bool init(const Node& n);
  static bool initInternal(const Node& n,
                           std::vector<Node>& vars,
                           std::map<Node, std::vector<Node>>& assignments,
                           std::vector<Node>& literals);
  bool d_valid;
  Node d_node;
  Node d_satLiteral;
  std::vector<Node> d_vars;
  std::map<Node, std::vector<Node>> d_assignments;
  std::vector<Node> d_literals;
  /**
   * For
   */
  std::map<Node, std::vector<size_t>> d_assignMap;
};

class AssignerDb
{
 public:
  AssignerDb();
  ~AssignerDb() {}
  Assigner* registerAssigner(const Node& n);
  bool hasAssigners() const;
  const std::vector<Assigner*>& getAssignersFor(const Node& lit) const;

 private:
  void registerLitsForAssigner(const Node& n, Assigner* a);
  std::map<Node, std::unique_ptr<Assigner>> d_db;
  /** literals to assigners */
  std::map<Node, std::vector<Assigner*>> d_litsToAssigners;
  /** Empty vec */
  std::vector<Assigner*> d_emptyVec;
};

}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
