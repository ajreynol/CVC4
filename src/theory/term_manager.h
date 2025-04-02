/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__TERM_MANAGER__H
#define CVC5__THEORY__TERM_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/theory_engine_module.h"

namespace cvc5::internal {
namespace theory {

/**
 */
class TermDbManager : public TheoryEngineModule
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  TermDbManager(Env& env, TheoryEngine* engine);
  /**
   * Notify (preprocessed) assertions.
   * @param assertions The assertions
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /** Notify lemma */
  void notifyLemma(TNode n,
                   InferenceId id,
                   LemmaProperty p,
                   const std::vector<Node>& skAsserts,
                   const std::vector<Node>& sks) override;
  /** Can we instantiation q with term n based on its origin information? */
  bool canInstantiate(const Node& q, const Node& n);
 private:
  class TermOrigin
  {
   public:
    TermOrigin(context::Context* c);
    void addOrigin(InferenceId id, const Node& arg);

   private:
    context::CDList<std::pair<InferenceId, Node>> d_origin;
    context::CDHashMap<Node, size_t> d_quantDepth;
  };
  /** Mapping */
  context::CDHashMap<Node, std::shared_ptr<TermOrigin>> d_omap;
  /** Mapping quantified formulas to their explicitly given inst nested level */
  std::map<Node, int64_t> d_qinLevel;
  /**
   * If id is InferenceId::NONE, the term was from the input formulas.
   * If args is provided, it is of the form (Q t_1 ... t_n),
   * where quantified formula Q was instantiated with t_1 ... t_n to generate
   * n.
   * @param n The term we saw in an input formula or lemma.
   * @param id The identifier indicating the lemma (if applicable) that
   * generated this term.
   * @param args The arguments.
   */
  void addOrigin(const Node& n, InferenceId id, const std::vector<Node>& args);
  /**
   * Do any term-specific initialization, called once when the term n is first
   * seen in the user context.
   */
  void initializeTerm(const Node& n);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
