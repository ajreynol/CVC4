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

#include "options/theory_options.h"
#include "options/smt_options.h"
#include "smt/set_defaults.h"
#include "theory/smt_engine_subsolver.h"
#include "proof/unsat_core.h"

namespace cvc5::internal {

namespace theory {

DeferredBlocker::DeferredBlocker(Env& env,
                                 TheoryEngine* theoryEngine,
                                 prop::PropEngine* propEngine)
    : TheoryEngineModule(env, theoryEngine, "DeferredBlocker"),
      d_propEngine(propEngine),
      d_blockers(userContext()),
      d_filtered(userContext(), false)
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // disable checking first
  smt::SetDefaults::disableChecking(d_subOptions);
  // requires full proofs
  d_subOptions.write_smt().produceUnsatCores = true;
  // don't do simplification, to ensure core is small?
  d_subOptions.write_smt().simplificationMode =
      options::SimplificationMode::NONE;
  // requires unsat cores
  d_subOptions.write_theory().deferBlock = false;
}

void DeferredBlocker::postsolve(prop::SatValue result) {}

void DeferredBlocker::check(Theory::Effort e) {}

bool DeferredBlocker::filterLemma(TNode n, InferenceId id, LemmaProperty p)
{
  if (id==InferenceId::ARITH_BB_LEMMA || id==InferenceId::ARITH_NL_TANGENT_PLANE)
  {
    d_filtered = true;
    return true;
  }
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
  // do subsolver check
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> deferChecker;
  uint64_t timeout = 0;
  initializeSubsolver(nodeManager(), deferChecker, ssi, timeout != 0, timeout);
  // assert and check-sat
  for (const Node& a : assertions)
  {
    deferChecker->assertFormula(a);
  }
  Trace("qscf-engine") << ">>> Check subsolver..." << std::endl;
  Result r = deferChecker->checkSat();
  if (r.getStatus() == Result::UNSAT)
  {
    // Add the computed unsat core as a conflict, which will cause a backtrack.
    UnsatCore uc = deferChecker->getUnsatCore();
    Node ucc = nodeManager()->mkAnd(uc.getCore());
    Trace("qscf-engine-debug") << "Unsat core is " << ucc << std::endl;
    Trace("qscf-engine") << "Core size = " << uc.getCore().size() << std::endl;
    TrustNode trn = TrustNode::mkTrustLemma(ucc.notNode(), nullptr);
    d_out.trustedLemma(trn, InferenceId::DEFER_BLOCK_UC);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
