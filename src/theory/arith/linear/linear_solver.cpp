/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper on linear solver
 */

#include "theory/arith/linear/linear_solver.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith:: linear {

LinearSolver::LinearSolver(TheoryArith& containing, Env& env, BranchAndBound& bab) : EnvObj(env), d_containing(containing), d_internal(containing, env, bab) {}

void LinearSolver::finishInit()
{
  d_internal.finishInit();
}
void LinearSolver::preRegisterTerm(TNode n){
d_internal.preRegisterTerm(n);
}
void LinearSolver::propagate(Theory::Effort e){
d_internal.propagate(e);
}
TrustNode LinearSolver::explain(TNode n){
return d_internal.explain(n);
}
void LinearSolver::collectModelValues(const std::set<Node>& termSet,
                        std::map<Node, Node>& arithModel,
                        std::map<Node, Node>& arithModelIllTyped){
d_internal.collectModelValues(termSet, arithModel, arithModelIllTyped);
}
void LinearSolver::presolve(){
d_internal.presolve();
}
void LinearSolver::notifyRestart(){
d_internal.notifyRestart();
}
Theory::PPAssertStatus LinearSolver::ppAssert(TrustNode tin,
                                TrustSubstitutionMap& outSubstitutions){
return d_internal.ppAssert(tin, outSubstitutions);
}
void LinearSolver::ppStaticLearn(TNode in, NodeBuilder& learned){
d_internal.ppStaticLearn(in, learned);
}
EqualityStatus LinearSolver::getEqualityStatus(TNode a, TNode b){
return d_internal.getEqualityStatus(a, b);
}
void LinearSolver::notifySharedTerm(TNode n){
d_internal.notifySharedTerm(n);
}
Node LinearSolver::getCandidateModelValue(TNode var){
return d_internal.getCandidateModelValue(var);
}
std::pair<bool, Node> LinearSolver::entailmentCheck(TNode lit){
return d_internal.entailmentCheck(lit);
}
bool LinearSolver::preCheck(Theory::Effort level){
return d_internal.preCheck(level);
}
void LinearSolver::preNotifyFact(TNode atom, bool pol, TNode fact){
d_internal.preNotifyFact(atom, pol, fact);
}
bool LinearSolver::postCheck(Theory::Effort level){
return d_internal.postCheck(level);
}
bool LinearSolver::foundNonlinear() const{
return d_internal.foundNonlinear();
}
ArithCongruenceManager* LinearSolver::getCongruenceManager(){
return d_internal.getCongruenceManager();
}

  
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
