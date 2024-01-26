/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of relevance manager.
 */

#include "theory/sub_conflict_find.h"

#include "options/theory_options.h"
#include "options/smt_options.h"
#include "theory/smt_engine_subsolver.h"
#include "proof/unsat_core.h"
#include "smt/set_defaults.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

SubConflictFind::SubConflictFind(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "SubConflictFind")
{

  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // TODO: if we are getting theory lemmas
#if 0
  if (options().quantifiers.quantSubCbqiinst)
  {
    d_subOptions.writeSmt().produceProofs = true;
    // don't do simplification, which can preprocess quantifiers to those not
    // occurring in the main solver
    d_subOptions.writeSmt().simplificationMode =
        options::SimplificationMode::NONE;
  }
#endif
  d_subOptions.writeSmt().produceUnsatCores = true;
  // don't do this strategy
  d_subOptions.writeQuantifiers().subConflictFind = false;
}


void SubConflictFind::check(Theory::Effort effort)
{
  if (effort!=Theory::EFFORT_FULL)
  {
    return;
  }
  
  double clSet = 0;
  if (TraceIsOn("scf"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("scf") << "---Subconflict Find Engine Round---" << std::endl;
  }
  std::vector<Node> assertions;
  const LogicInfo& logicInfo = logicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!logicInfo.isTheoryEnabled(tid))
    {
      continue;
    }
    // collect all assertions from theory
    for (context::CDList<Assertion>::const_iterator
             it = d_qstate.factsBegin(tid),
             itEnd = d_qstate.factsEnd(tid);
         it != itEnd;
         ++it)
    {
      Node a = (*it).d_assertion;
      assertions.push_back(a);
    }
  }
  // do subsolver check
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> findConflict;
  uint64_t timeout = options().theory.subConflictTimeout;
  initializeSubsolver(findConflict, ssi, timeout != 0, timeout);
  // assert and check-sat
  for (const Node& a : assertions)
  {
    findConflict->assertFormula(a);
  }
  Trace("scf") << ">>> Check subsolver..." << std::endl;
  Result r = findConflict->checkSat();
  Trace("scf") << "<<< ...result is " << r << std::endl;
  size_t addedLemmas = 0;
  if (r.getStatus() == Result::UNSAT)
  {
    // Add the computed unsat core as a conflict, which will cause a backtrack.
    UnsatCore uc = findConflict->getUnsatCore();
    Node ucc = NodeManager::currentNM()->mkAnd(uc.getCore());
    Trace("scf-debug") << "Unsat core is " << ucc << std::endl;
    Trace("scf") << "Core size = " << uc.getCore().size() << std::endl;
    d_out.lemma(ucc.notNode(), InferenceId::SUB_CONFLICT_UC);
  }

  if (TraceIsOn("scf"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("scf") << "Finished subconflict find engine, time = "
                         << (clSet2 - clSet);
    Trace("scf") << ", result = " << r;
    if (addedLemmas > 0)
    {
      Trace("scf") << ", addedLemmas = " << addedLemmas;
    }
    Trace("scf") << std::endl;
  }
}

}  // namespace theory
}  // namespace cvc5::internal
