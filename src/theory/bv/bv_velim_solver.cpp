/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A solver based on variable elimination.
 */

#include "theory/bv/bv_velim_solver.h"

namespace cvc5::internal {
namespace theory {

namespace bv {

BvVElimSolver::BvVElimSolver(Env& env) : EnvObj(env) {}
BvVElimSolver::~BvVElimSolver() {}

TrustNode BvVElimSolver::check(const std::vector<Node>& asserts)
{
  return TrustNode::null();
}

std::shared_ptr<ProofNode> BvVElimSolver::getProofFor(Node fact)
{
  return nullptr;
}

std::string BvVElimSolver::identify() const
{
  return "BvVElimSolver";
}


}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
