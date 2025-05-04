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

#include "theory/deferred_blocker.h"

namespace cvc5::internal {


namespace theory {

DeferredBlocker::DeferredBlocker(Env& env,
                    TheoryEngine* theoryEngine,
                    prop::PropEngine* propEngine) : TheoryEngineModule(env, theoryEngine, "DeferredBlocker"), d_propEngine(propEngine), d_blockers(userContext()), d_filtered(userContext(), false){}

void DeferredBlocker::postsolve(prop::SatValue result)
{}

void DeferredBlocker::check(Theory::Effort e)
{

}

bool DeferredBlocker::filterLemma(TNode n,
                  InferenceId id,
                  LemmaProperty p)
{
  return false;
}

void DeferredBlocker::notifyCandidateModel(TheoryModel* m)
{
  if (d_valuation.needCheck())
  {
    return;
  }
  std::vector<Node> assertions;
  std::unordered_set<Node> quants;
  const LogicInfo& logicInfo = d_env.getLogicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!logicInfo.isTheoryEnabled(tid))
    {
      continue;
    }
    // collect all assertions from theory
    for (context::CDList<Assertion>::const_iterator
             it = d_valuation.factsBegin(tid),
             itEnd = d_valuation.factsEnd(tid);
         it != itEnd;
         ++it)
    {
      Node a = (*it).d_assertion;
      assertions.push_back(a);
    }
  }
}

}  // namespace theory
}  // namespace cvc5::internal

