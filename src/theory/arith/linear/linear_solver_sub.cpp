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

#include "theory/arith/linear/linear_solver_sub.h"

#include "expr/attribute.h"
#include "theory/arith/arith_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

LinearSolverSub::LinearSolverSub(Env& env,
                           TheoryState& ts,
                           InferenceManager& im)
    : LinearSolver(env), d_im(im)
{
}
void LinearSolver::finishInit(eq::EqualityEngine* ee)
{
  // d_internal.finishInit(ee);
}
void LinearSolver::preRegisterTerm(TNode n)
{  // d_internal.preRegisterTerm(n);
}
void LinearSolver::propagate(Theory::Effort e)
{  // d_internal.propagate(e);
}

TrustNode LinearSolver::explain(TNode n)
{
  return TrustNode::null();  // d_internal.explain(n);
}

void LinearSolver::collectModelValues(const std::set<Node>& termSet,
                                      std::map<Node, Node>& arithModel,
                                      std::map<Node, Node>& arithModelIllTyped)
{

}

void LinearSolver::presolve()
{
}

void LinearSolver::notifyRestart()
{
}

Theory::PPAssertStatus LinearSolver::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}
void LinearSolver::ppStaticLearn(TNode in, NodeBuilder& learned)
{
}
EqualityStatus LinearSolver::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_UNKNOWN;
}
void LinearSolver::notifySharedTerm(TNode n)
{
}
Node LinearSolver::getCandidateModelValue(TNode var)
{
  return Node::null();
}
std::pair<bool, Node> LinearSolver::entailmentCheck(TNode lit)
{
  return std::pair<bool, Node>(
      false, Node::null());
}
bool LinearSolver::preCheck(Theory::Effort level, bool newFacts)
{
  return false;
}
void LinearSolver::preNotifyFact(TNode fact)
{
}
bool LinearSolver::postCheck(Theory::Effort level)
{

  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> findConflict;
  initializeSubsolver(findConflict, ssi, false);
  // assert and check-sat
  Trace("opaque-solver") << "Check opaque with " << d_asserts.size()
                         << " assertions..." << std::endl;
  for (const std::pair<Node, bool>& a : d_asserts)
  {
    Node lit = a.second ? a.first : a.first.notNode();
    Trace("opaque-assert") << "- " << lit << std::endl;
    findConflict->assertFormula(lit);
  }
  Result r = findConflict->checkSat();
  Trace("opaque-solver") << "<<< ...result is " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    UnsatCore uc = findConflict->getUnsatCore();
    std::vector<Node> opaqueCore;
    OpaqueFormAttribute ofa;
    for (const Node& a : uc)
    {
      bool pol = a.getKind() != Kind::NOT;
      Node oa = pol ? a : a[0];
      oa = oa.getAttribute(ofa);
      Assert(!oa.isNull());
      opaqueCore.push_back(pol ? oa : oa.notNode());
    }
    Node ucc = nodeManager()->mkAnd(opaqueCore);
    Trace("opaque-solver") << "Unsat core is " << ucc << std::endl;
    Trace("opaque-solver") << "Core size = " << uc.getCore().size()
                           << std::endl;
    d_im.lemma(ucc.notNode(), InferenceId::ARITH_LINEAR_SUB_UC);
  }
  return false;
}
bool LinearSolver::foundNonlinear() const
{
  return false;
}
ArithCongruenceManager* LinearSolver::getCongruenceManager()
{
  return nullptr;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
