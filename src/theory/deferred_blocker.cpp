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
                    prop::PropEngine* propEngine) : TheoryEngineModule(env, theoryEngine, "DeferredBlocker"), d_propEngine(propEngine){}

void DeferredBlocker::postsolve(prop::SatValue result)
{}

void DeferredBlocker::check(Theory::Effort e)
{

}

void DeferredBlocker::notifyLemma(TNode n,
                  InferenceId id,
                  LemmaProperty p,
                  const std::vector<Node>& skAsserts,
                  const std::vector<Node>& sks)
{

}

void DeferredBlocker::notifyCandidateModel(TheoryModel* m)
{

}

}  // namespace theory
}  // namespace cvc5::internal

