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
 * Wrapper on linear solver
 */

#include "theory/arith/linear/linear_solver.h"

#include "expr/attribute.h"
#include "theory/arith/arith_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

LinearSolver::LinearSolver(Env& env) : EnvObj(env){}
                                       
LinearSolverLegacy::LinearSolverLegacy(Env& env,
                           TheoryState& ts,
                           InferenceManager& im,
                           BranchAndBound& bab)
    : LinearSolver(env), d_im(im), d_internal(env, *this, ts, bab)
{
}

void LinearSolverLegacy::finishInit(eq::EqualityEngine* ee)
{
  d_internal.finishInit(ee);
}
void LinearSolverLegacy::preRegisterTerm(TNode n) { d_internal.preRegisterTerm(n); }
void LinearSolverLegacy::propagate(Theory::Effort e) { d_internal.propagate(e); }

TrustNode LinearSolverLegacy::explain(TNode n) { return d_internal.explain(n); }

void LinearSolverLegacy::collectModelValues(const std::set<Node>& termSet,
                                      std::map<Node, Node>& arithModel,
                                      std::map<Node, Node>& arithModelIllTyped)
{
  d_internal.collectModelValues(termSet, arithModel, arithModelIllTyped);
}

void LinearSolverLegacy::presolve() { d_internal.presolve(); }

void LinearSolverLegacy::notifyRestart() { d_internal.notifyRestart(); }

Theory::PPAssertStatus LinearSolverLegacy::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal.ppAssert(tin, outSubstitutions);
}
void LinearSolverLegacy::ppStaticLearn(TNode in, NodeBuilder& learned)
{
  d_internal.ppStaticLearn(in, learned);
}
EqualityStatus LinearSolverLegacy::getEqualityStatus(TNode a, TNode b)
{
  return d_internal.getEqualityStatus(a, b);
}
void LinearSolverLegacy::notifySharedTerm(TNode n) { d_internal.notifySharedTerm(n); }
Node LinearSolverLegacy::getCandidateModelValue(TNode var)
{
  return d_internal.getCandidateModelValue(var);
}
std::pair<bool, Node> LinearSolverLegacy::entailmentCheck(TNode lit)
{
  return d_internal.entailmentCheck(lit);
}
bool LinearSolverLegacy::preCheck(Theory::Effort level, bool newFacts)
{
  return d_internal.preCheck(level, newFacts);
}
void LinearSolverLegacy::preNotifyFact(TNode fact) { d_internal.preNotifyFact(fact); }
bool LinearSolverLegacy::postCheck(Theory::Effort level)
{
  return d_internal.postCheck(level);
}
bool LinearSolverLegacy::foundNonlinear() const
{
  return d_internal.foundNonlinear();
}
ArithCongruenceManager* LinearSolverLegacy::getCongruenceManager()
{
  return d_internal.getCongruenceManager();
}

bool LinearSolverLegacy::outputTrustedLemma(TrustNode lemma, InferenceId id)
{
  return d_im.trustedLemma(lemma, id);
}

void LinearSolverLegacy::outputTrustedConflict(TrustNode conf, InferenceId id)
{
  d_im.trustedConflict(conf, id);
}

void LinearSolverLegacy::outputPropagate(TNode lit) { d_im.propagateLit(lit); }

void LinearSolverLegacy::spendResource(Resource r) { d_im.spendResource(r); }

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
