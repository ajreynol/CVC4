/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Deferred blocker module
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DEFERRED_BLOCKER_H
#define CVC5__THEORY__DEFERRED_BLOCKER_H

#include "theory/theory.h"
#include "theory/theory_engine_module.h"
#include "theory/valuation.h"

namespace cvc5::internal {

namespace prop {
class PropEngine;
}

namespace theory {

class DeferredBlocker : public TheoryEngineModule
{
 public:
  DeferredBlocker(Env& env,
                  TheoryEngine* theoryEngine,
                  prop::PropEngine* propEngine);

  /**
   * postsolve, attempts to solve
   */
  void postsolve(prop::SatValue result) override;

  /**
   * ?
   */
  void check(Theory::Effort e) override;

  /**
   * May block the lemma
   */
  bool filterLemma(TNode n, InferenceId id, LemmaProperty p) override;
  /** Needs candidate model, return true if the method below requires calling */
  bool needsCandidateModel() override;

 private:
  /** Current propEngine. */
  prop::PropEngine* d_propEngine;
  /** The list of blockers we have considered */
  context::CDList<Node> d_blockers;
  /** Have we filtered a lemma? */
  context::CDO<bool> d_filtered;
  /** Lemmas we have blocked in the current context */
  context::CDList<Node> d_filteredLems;
  /** The index of lemmas we have added */
  context::CDO<size_t> d_filterIndex;
  /** Lemmas we have blocked in the current context */
  context::CDHashSet<Node> d_bbSplit;
  /** All lemmas we have sent in the user context */
  context::CDHashSet<Node> d_cache;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DEFERRED_BLOCKER_H */
