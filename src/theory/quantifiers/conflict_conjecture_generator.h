/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict-based conjecture generation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 */
class ConflictConjectureGenerator : public QuantifiersModule
{
 public:
  ConflictConjectureGenerator(Env& env,
                              QuantifiersState& qs,
                              QuantifiersInferenceManager& qim,
                              QuantifiersRegistry& qr,
                              TermRegistry& tr);
  ~ConflictConjectureGenerator() {}
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Needs model. */
  QEffort needsModel(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Check ownership for q */
  void checkOwnership(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override;

 private:
  Node d_false;
  Node d_null;
  /** */
  eq::EqualityEngine* d_ee;

  std::map<Node, Node> d_bv;
  std::map<Node, Node> d_bvToEqc;
  Node getOrMkVarForEqc(const Node& e);
  std::map<Node, std::vector<Node>> d_eqcGen;
  const std::vector<Node>& getGenForEqc(const Node& e);
  void checkDisequality(const Node& eq);

  std::map<Node, std::vector<Node>> d_eqcGenRec;
  std::map<Node, std::vector<Node>> d_genToFv;

  class GenTrie
  {
   public:
    std::map<Node, GenTrie> d_children;
    std::vector<std::pair<Node, Node>> d_gens;
    void clear();
  };
  GenTrie d_gtrie;
  FunDefEvaluator d_funDefEvaluator;

  void getGeneralizations(const Node& e);
  void getGeneralizationsInternal(const Node& e);
  /**
   * g is an expansion of v.
   */
  void addGeneralizationTerm(const Node& g,
                             const Node& v,
                             size_t depth,
                             const std::vector<Node>& fvs);

  enum class State
  {
    UNKNOWN,
    SUPERSET,
    SUBSET
  };
  void findCompatible(const Node& g,
                      const std::vector<Node>& fvs,
                      const Node& vlhs,
                      GenTrie* gt,
                      State state,
                      size_t fvindex);
  
  /**
   * Called when FV(a) is a superset of FV(b).
   */
  void candidateConjecture(const Node& a, const Node& b);
  bool filterEmatching(const Node& a, const Node& b);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
