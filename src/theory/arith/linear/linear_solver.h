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
#include "theory/arith/linear/theory_arith_private.h"
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
class LinearSolver : protected EnvObj
{
 public:
  LinearSolver(Env& env);
  /** finish initialize */
  virtual void finishInit(eq::EqualityEngine* ee) = 0;
  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  virtual void preRegisterTerm(TNode n) = 0;
  /** Propagate at the given effort level */
  virtual void propagate(Theory::Effort e) = 0;
  /** Explain propagated literal n */
  virtual TrustNode explain(TNode n) = 0;
  /**
   * Collect model values. This is the main method for extracting information
   * about how to construct the model. This method relies on the caller for
   * processing the map, which is done so that other modules (e.g. the
   * non-linear extension) can modify arithModel before it is sent to the model.
   *
   * @param termSet The set of relevant terms
   * @param arithModel Mapping from terms (of int/real type) to their values.
   * The caller should assert equalities to the model for each entry in this
   * map.
   * @param arithModelIllTyped Mapping from terms (of int type) to real values.
   * This is used for catching cases where this solver mistakenly set an
   * integer variable to a real.
   */
  virtual void collectModelValues(const std::set<Node>& termSet,
                          std::map<Node, Node>& arithModel,
                          std::map<Node, Node>& arithModelIllTyped) = 0;
  /** Presolve */
  virtual void presolve() = 0;
  /** Notify restart */
  virtual void notifyRestart() = 0;
  /** Preprocess assert */
  virtual Theory::PPAssertStatus ppAssert(TrustNode tin,
                                  TrustSubstitutionMap& outSubstitutions) = 0;
  /** Preprocess static learn */
  virtual void ppStaticLearn(TNode in, NodeBuilder& learned) = 0;

  virtual EqualityStatus getEqualityStatus(TNode a, TNode b) = 0;

  /** Called when n is notified as being a shared term with TheoryArith. */
  virtual void notifySharedTerm(TNode n) = 0;
  /** Get candidate model value */
  virtual Node getCandidateModelValue(TNode var) = 0;
  /** Do entailment check */
  virtual std::pair<bool, Node> entailmentCheck(TNode lit) = 0;
  //--------------------------------- standard check
  /** Pre-check, called before the fact queue of the theory is processed. */
  virtual bool preCheck(Theory::Effort level, bool newFacts) = 0;
  /** Pre-notify fact. */
  virtual void preNotifyFact(TNode fact) = 0;
  /**
   * Post-check, called after the fact queue of the theory is processed. Returns
   * true if a conflict or lemma was emitted.
   */
  virtual bool postCheck(Theory::Effort level) = 0;
  //--------------------------------- end standard check
  /**
   * Found non-linear? This returns true if this solver ever encountered
   * any non-linear terms that were unhandled. Note that this class is not
   * responsible for handling non-linear arithmetic. If the owner of this
   * class does not handle non-linear arithmetic in another way, then
   * setModelUnsound should be called on the output channel of TheoryArith.
   */
  virtual bool foundNonlinear() const = 0;

  /** get the congruence manager, if we are using one */
  virtual ArithCongruenceManager* getCongruenceManager() = 0;
};


/**
 * A wrapper of the linear arithmetic solver.
 */
class LinearSolverLegacy : public LinearSolver
{
 public:
  LinearSolverLegacy(Env& env,
               TheoryState& ts,
               InferenceManager& im,
               BranchAndBound& bab);
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

  //======================
  bool outputTrustedLemma(TrustNode lemma, InferenceId id);
  void outputTrustedConflict(TrustNode conf, InferenceId id);
  void outputPropagate(TNode lit);
  void spendResource(Resource r);

 private:
  /** The inference manager */
  InferenceManager& d_im;
  /** The solver */
  TheoryArithPrivate d_internal;
};


}  // namespace linear
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
