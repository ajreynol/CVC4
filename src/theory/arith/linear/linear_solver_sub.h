/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper on linear solver
 */

#pragma once

#include "context/cdhashmap.h"
#include "smt/env_obj.h"
#include "theory/arith/linear/linear_solver.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

namespace arith {

class BranchAndBound;

namespace linear {

/**
 * A wrapper of the linear arithmetic solver.
 */
class LinearSolverSub : protected LinearSolver
{
 public:
  LinearSolverSub(Env& env,
               TheoryState& ts,
               InferenceManager& im);
  /** finish initialize */
  void finishInit(eq::EqualityEngine* ee) override;
  /** Does non-context dependent setup for a node connected to a theory. */
  void preRegisterTerm(TNode n) override;
  /** Propagate at the given effort level */
  void propagate(Theory::Effort e) override;
  /** Explain propagated literal n */
  TrustNode explain(TNode n) override;
  /** Collect model values. */
  void collectModelValues(const std::set<Node>& termSet,
                          std::map<Node, Node>& arithModel,
                          std::map<Node, Node>& arithModelIllTyped) override;
  /** Presolve */
  void presolve() override;
  /** Notify restart */
  void notifyRestart() override;
  /** Preprocess assert */
  Theory::PPAssertStatus ppAssert(TrustNode tin,
                                  TrustSubstitutionMap& outSubstitutions) override;
  /** Preprocess static learn */
  void ppStaticLearn(TNode in, NodeBuilder& learned) override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  /** Called when n is notified as being a shared term with TheoryArith. */
  void notifySharedTerm(TNode n) override;
  /** Get candidate model value */
  Node getCandidateModelValue(TNode var) override;
  /** Do entailment check */
  std::pair<bool, Node> entailmentCheck(TNode lit) override;
  //--------------------------------- standard check
  /** Pre-check, called before the fact queue of the theory is processed. */
  bool preCheck(Theory::Effort level, bool newFacts) override;
  /** Pre-notify fact. */
  void preNotifyFact(TNode fact) override;
  /** Post-check */
  bool postCheck(Theory::Effort level) override;
  //--------------------------------- end standard check
  /** Found non-linear */
  bool foundNonlinear() const override;
  /** get the congruence manager, if we are using one */
  ArithCongruenceManager* getCongruenceManager() override;

 private:
  /** The inference manager */
  InferenceManager& d_im;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace linear
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal