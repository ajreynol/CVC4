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
 * Relevance manager.
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
class TermManager : public TheoryEngineModule
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  TermManager(Env& env, TheoryEngine* engine);
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

 private:
   class TermOrigin
   {
   public:
     TermOrigin(context::Context* c) : d_args(c){}
     void addOrigin(InferenceId id, const Node& arg);
   private:
     context::CDList<std::pair<InferenceId, Node>> d_args;
   };
   context::CDHashMap<Node, std::shared_ptr<TermOrigin>> d_origins;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
