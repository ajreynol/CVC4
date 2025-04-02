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

#include "theory/term_manager.h"

namespace cvc5::internal {
namespace theory {

TermManager::TermManager(Env& env, TheoryEngine* engine) : TheoryEngineModule(env, engine, "TermManager"){}

void TermManager::notifyPreprocessedAssertions(const std::vector<Node>& assertions)
{
  
}

void TermManager::notifyLemma(TNode n,
                  InferenceId id,
                  LemmaProperty p,
                  const std::vector<Node>& skAsserts,
                  const std::vector<Node>& sks)
{
  
}

}  // namespace theory
}  // namespace cvc5::internal

