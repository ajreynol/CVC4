/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference manager.
 */

#include "theory/datatypes/inference_manager.h"

#include "expr/dtype.h"
#include "options/datatypes_options.h"
#include "proof/eager_proof_generator.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

InferenceManager::InferenceManager(Env& env, Theory& t, TheoryState& state)
    : InferenceManagerBuffered(env, t, state, "theory::datatypes::"),
      d_ipc(isProofEnabled() ? new InferProofCons(env, context()) : nullptr),
      d_lemPg(isProofEnabled() ? new EagerProofGenerator(
                                     env, userContext(), "datatypes::lemPg")
                               : nullptr)
{
  d_false = nodeManager()->mkConst(false);
}

InferenceManager::~InferenceManager() {}

void InferenceManager::addPendingInference(Node conc,
                                           InferenceId id,
                                           Node exp,
                                           bool forceLemma)
{
  // if we are forcing the inference to be processed as a lemma, if the
  // dtInferAsLemmas option is set, or if the inference must be sent as a lemma
  // based on the policy in mustCommunicateFact.
  if (forceLemma || options().datatypes.dtInferAsLemmas
      || DatatypesInference::mustCommunicateFact(conc, exp))
  {
    d_pendingLem.emplace_back(new DatatypesInference(this, conc, exp, id));
  }
  else
  {
    d_pendingFact.emplace_back(new DatatypesInference(this, conc, exp, id));
  }
}

void InferenceManager::process()
{
  // if we are in conflict, immediately reset and clear pending
  if (d_theoryState.isInConflict())
  {
    reset();
    clearPending();
    return;
  }
  // process pending lemmas, used infrequently, only for definitional lemmas
  doPendingLemmas();
  if (hasSentLemma())
  {
    // Sending lemmas may trigger equality engine notifications and SAT
    // backtracking. Any internal facts queued before this point may have stale
    // explanations and will be regenerated in a later check.
    clearPendingFacts();
    return;
  }
  // Since datatype facts may be queued from equality engine notifications,
  // facts can become stale if another theory sends a lemma and causes
  // backtracking before we process them. If we detect this, clear the whole
  // queue; the facts will be regenerated in a later check if still relevant.
  for (const std::unique_ptr<TheoryInference>& fact : d_pendingFact)
  {
    SimpleTheoryInternalFact* sf =
        dynamic_cast<SimpleTheoryInternalFact*>(fact.get());
    if (sf != nullptr && !sf->d_exp.isNull() && !sf->d_exp.isConst())
    {
      std::vector<Node> pexp{sf->d_exp};
      if (!isFactCurrent(pexp))
      {
        clearPendingFacts();
        return;
      }
    }
  }
  // now process the pending facts
  doPendingFacts();
}

bool InferenceManager::sendDtLemma(Node lem, InferenceId id, LemmaProperty p)
{
  if (isProofEnabled())
  {
    TrustNode trn = processDtLemma(lem, Node::null(), id);
    return trustedLemma(trn, id);
  }
  // otherwise send as a normal lemma directly
  return lemma(lem, id, p);
}

void InferenceManager::sendDtConflict(const std::vector<Node>& conf,
                                      InferenceId id)
{
  if (isProofEnabled())
  {
    Node exp = nodeManager()->mkAnd(conf);
    prepareDtInference(d_false, exp, id, d_ipc.get());
  }
  conflictExp(id, conf, d_ipc.get());
}

TrustNode InferenceManager::processDtLemma(Node conc, Node exp, InferenceId id)
{
  // set up a proof constructor
  std::shared_ptr<InferProofCons> ipcl;
  if (isProofEnabled())
  {
    ipcl = std::make_shared<InferProofCons>(d_env, nullptr);
  }
  conc = prepareDtInference(conc, exp, id, ipcl.get());
  // send it as a lemma
  Node lem;
  if (!exp.isNull() && !exp.isConst())
  {
    lem = nodeManager()->mkNode(Kind::IMPLIES, exp, conc);
  }
  else
  {
    lem = conc;
  }
  if (isProofEnabled())
  {
    // store its proof
    std::shared_ptr<ProofNode> pbody = ipcl->getProofFor(conc);
    std::shared_ptr<ProofNode> pn = pbody;
    if (!exp.isNull() && !exp.isConst())
    {
      std::vector<Node> expv;
      expv.push_back(exp);
      pn = d_env.getProofNodeManager()->mkScope(pbody, expv);
    }
    d_lemPg->setProofFor(lem, pn);
  }
  return TrustNode::mkTrustLemma(lem, d_lemPg.get());
}

Node InferenceManager::processDtFact(Node conc,
                                     Node exp,
                                     InferenceId id,
                                     ProofGenerator*& pg)
{
  pg = d_ipc.get();
  return prepareDtInference(conc, exp, id, d_ipc.get());
}

Node InferenceManager::prepareDtInference(Node conc,
                                          Node exp,
                                          InferenceId id,
                                          InferProofCons* ipc)
{
  Trace("dt-lemma-debug") << "prepareDtInference : " << conc << " via " << exp
                          << " by " << id << std::endl;
  if (isProofEnabled())
  {
    Assert(ipc != nullptr);
    // If proofs are enabled, notify the proof constructor.
    // Notice that we have to reconstruct a datatypes inference here. This is
    // because the inference in the pending vector may be destroyed as we are
    // processing this inference, if we triggered to backtrack based on the
    // call below, since it is a unique pointer.
    std::shared_ptr<DatatypesInference> di =
        std::make_shared<DatatypesInference>(this, conc, exp, id);
    ipc->notifyFact(di);
  }
  return conc;
}

bool InferenceManager::isFactCurrent(const std::vector<Node>& exp) const
{
  std::vector<Node> expc = exp;
  NodeManager* nm = nodeManager();
  for (size_t i = 0; i < expc.size(); i++)
  {
    Node e = expc[i];
    bool epol = e.getKind() != Kind::NOT;
    Node eatom = epol ? e : e[0];
    if (eatom.getKind() == Kind::AND)
    {
      if (!epol)
      {
        return false;
      }
      expc.insert(expc.end(), eatom.begin(), eatom.end());
    }
    else if (eatom.getKind() == Kind::EQUAL)
    {
      if (!d_theoryState.hasTerm(eatom[0]) || !d_theoryState.hasTerm(eatom[1]))
      {
        return false;
      }
      if (epol && !d_theoryState.areEqual(eatom[0], eatom[1]))
      {
        return false;
      }
      if (!epol && !d_theoryState.areDisequal(eatom[0], eatom[1]))
      {
        return false;
      }
    }
    else
    {
      if (!d_theoryState.hasTerm(eatom))
      {
        return false;
      }
      Node bval = nm->mkConst(epol);
      if (!d_theoryState.areEqual(eatom, bval))
      {
        return false;
      }
    }
  }
  return true;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
