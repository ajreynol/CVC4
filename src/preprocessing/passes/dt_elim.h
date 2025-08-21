/******************************************************************************
 * Top contributors (to current version):
 *   Caleb Donovick, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewrite preprocessing pass.
 *
 * Calls the rewriter on every assertion.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__DT_ELIM_H
#define CVC5__PREPROCESSING__PASSES__DT_ELIM_H

#include "expr/node_converter.h"
#include "preprocessing/preprocessing_pass.h"
#include "proof/rewrite_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

enum class DtElimPolicy
{
  /** Not processing this datatype */
  NONE,
  /** 1 cons, 0 fields */
  UNIT,
  /** 1 cons, 1+ fields */
  UNARY,
  /** 2 cons, 0 fields */
  BINARY_ENUM,
  /** 2 cons, 1+ fields, no recursion */
  BINARY,
  /** 1+ cons, 0 fields */
  ABSTRACT_ENUM,
  /** 1+ cons, 1+ fields, no recursion */
  ABSTRACT,
};
bool isUnaryPolicy(DtElimPolicy policy);
bool isBinaryTestPolicy(DtElimPolicy policy);
bool isAbstractPolicy(DtElimPolicy policy);
/** Converts a dt-elim policy identifier to a string. */
const char* toString(DtElimPolicy policy);
/** Writes a dt-elim policy identifier to a stream. */
std::ostream& operator<<(std::ostream& out, DtElimPolicy policy);

class DtElimConverter : protected EnvObj, public NodeConverter
{
 public:
  DtElimConverter(Env& env, const std::vector<Node>& assertions);
  ~DtElimConverter();
  /**
   * Compute the policies for each datatype
   */
  void computePolicies(const std::vector<Node>& assertions);
  /**
   */
  Node postConvert(Node n) override;
  /**
   * Get the new lemmas
   */
  const std::vector<Node>& getNewLemmas() const { return d_newLemmas; }
  /**
   * Get the model substitutions
   */
  const std::vector<Node>& getModelSubstitutions() const { return d_modelSubs; }
 private:
  /**
   * For t : D where D is a datatype, this returns the abstraction of t.
   * For example, if D is (Option Bool), this returns
   *  (ite ((_ is some) t) U_some U_none)),
   * where U is getTypeAbstraction(D) and U_some, U_none : U.
   */
  Node getDtAbstraction(const Node& v);
  /**
   * if an apply UF, we get the predicate that is true when the function
   * f is that tester. For instance, for f : Int -> (Option Bool), we
   * introduce a predicate f-is-none : Int -> Bool that is equivalent to
   * (lambda ((x Int)) ((_ is none) (f x))). The tester for (f a) is
   * (f-is-none a).
   * Analoguously if we are doing abstraction policy, then we introduce
   * f-get-cons : Int -> U, where f-get-cons is equivalent to
   * (lambda ((x Int)) (ite ((_ is some) (f x)) U_some U_none)), where
   * U is an uninterpreted sort and U_some, U_none : U.
   */
  Node getTesterFunctionInternal(const Node& v, DtElimPolicy policy);
  Node getTesterInternal(const Node& v, DtElimPolicy policy);
  Node getTester(const Node& v, DtElimPolicy policy, size_t i);
  const std::vector<Node>& getSelectorVecInternal(const Node& v, size_t i);
  const std::vector<Node>& getSelectorVec(const Node& v, DtElimPolicy policy, size_t i);
  TypeNode getTypeAbstraction(const TypeNode& dt);
  const std::vector<Node>& getConstructorVec(const TypeNode& tn);
  /** The new lemmas */
  std::vector<Node> d_newLemmas;
  /** The eliminations */
  std::vector<Node> d_modelSubs;
  /** */
  std::unordered_set<Node> d_modelElim;
  /** The policy */
  std::map<TypeNode, DtElimPolicy> d_dtep;
  /** Used for getTester and getAbstractConsKind */
  std::map<Node, Node> d_tester;
  /** */
  std::map<std::pair<Node, size_t>, std::vector<Node>> d_selectors;
  std::map<std::pair<Node, size_t>, Node> d_selectorsElim;
  /** */
  std::map<TypeNode, std::vector<Node>> d_constructors;
  /** */
  TypeNode d_dtElimSc;
};

class DtElim : public PreprocessingPass
{
 public:
  DtElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** process internal */
  Node processInternal(const Node& n, std::unordered_set<TNode>& visited);
  /** */
  std::unordered_set<TypeNode> d_processed;
  std::vector<TypeNode> d_candidateDt;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DT_ELIM_H */
