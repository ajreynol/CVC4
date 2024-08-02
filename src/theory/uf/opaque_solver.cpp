/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of opaque solver.
 */

#include "theory/uf/opaque_solver.h"

#include "options/uf_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

OpaqueSolver::OpaqueSolver(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im)
{
}

OpaqueSolver::~OpaqueSolver() {}

void OpaqueSolver::preRegisterTerm(TNode term)
{
}

void OpaqueSolver::check()
{
}

void OpaqueSolver::notifyFact(const Node& atom, bool pol)
{
  
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
