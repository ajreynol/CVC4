/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "prop/theory_proxy.h"

#include "context/context.h"
#include "decision/decision_engine.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/prop_options.h"
#include "options/parallel_options.h"
#include "options/smt_options.h"
#include "prop/cnf_stream.h"
#include "prop/proof_cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat_relevancy.h"
#include "prop/skolem_def_manager.h"
#include "prop/zero_level_learner.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace prop {

TheoryProxy::TheoryProxy(Env& env,
                         PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         decision::DecisionEngine* decisionEngine,
                         SkolemDefManager* skdm)
    : EnvObj(env),
      d_propEngine(propEngine),
      d_cnfStream(nullptr),
      d_decisionEngine(decisionEngine),
      d_dmNeedsActiveDefs(d_decisionEngine->needsActiveSkolemDefs()),
      d_theoryEngine(theoryEngine),
      d_queue(context()),
      d_satRlv(nullptr),
      d_tpp(env, *theoryEngine),
      d_skdm(skdm),
      d_zll(nullptr),
      d_stopSearch(false, userContext())
{
  bool trackZeroLevel =
      options().smt.deepRestartMode != options::DeepRestartMode::NONE
      || isOutputOn(OutputTag::LEARNED_LITS)
      || options().smt.produceLearnedLiterals
      || options().parallel.computePartitions > 0;
  if (trackZeroLevel)
  {
    d_zll = std::make_unique<ZeroLevelLearner>(env, theoryEngine);
  }
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::finishInit(CDCLTSatSolverInterface* satSolver,
                             CnfStream* cnfStream)
{
  d_cnfStream = cnfStream;

  if (options().prop.satTheoryRelevancy != options::SatRelevancyMode::NONE)
  {
    d_satRlv.reset(new SatRelevancy(satSolver,
                                    d_theoryEngine,
                                    d_env,
                                    cnfStream,
                                    options().prop.satTheoryRelevancy));
  }
}

void TheoryProxy::presolve()
{
  d_decisionEngine->presolve();
  d_theoryEngine->presolve();
  if (d_satRlv != nullptr)
  {
    d_satRlv->presolve(d_queue);
  }
  d_stopSearch = false;
}

void TheoryProxy::notifyTopLevelSubstitution(const Node& lhs,
                                             const Node& rhs) const
{
  if (d_zll != nullptr)
  {
    d_zll->notifyTopLevelSubstitution(lhs, rhs);
  }
}

void TheoryProxy::notifyInputFormulas(
    const std::vector<Node>& assertions,
    std::unordered_map<size_t, Node>& skolemMap)
{
  // notify the theory engine of preprocessed assertions
  d_theoryEngine->notifyPreprocessedAssertions(assertions);
  // Now, notify the theory proxy of the assertions and skolem definitions.
  // Notice we do this before asserting the formulas to the CNF stream below,
  // since (preregistration) lemmas may occur during calls to assertInternal.
  // These lemmas we want to be notified about after the theory proxy has
  // been notified about all input assertions.
  std::unordered_map<size_t, Node>::iterator it;
  for (size_t i = 0, asize = assertions.size(); i < asize; i++)
  {
    // is the assertion a skolem definition?
    it = skolemMap.find(i);
    Node skolem;
    if (it != skolemMap.end())
    {
      skolem = it->second;
    }
    if (!skolem.isNull())
    {
      notifySkolemDefinition(assertions[i], skolem);
    }
    notifyAssertion(assertions[i], skolem, false);
  }

  // the zero-level learner needs to be notified of the input assertions, to
  // determine what is learnable
  if (d_zll != nullptr)
  {
    d_zll->notifyInputFormulas(assertions);
  }
}

void TheoryProxy::notifySkolemDefinition(Node a, TNode skolem)
{
  Assert(!skolem.isNull());
  d_skdm->notifySkolemDefinition(skolem, a);
}

void TheoryProxy::notifyAssertion(Node a, TNode skolem, bool isLemma)
{
  if (skolem.isNull())
  {
    if (d_satRlv != nullptr)
    {
      // an input assertion
      // NOTE: we don't currently distinguish input from lemmas since unit
      // input formulas trigger assertions before input, thus, adding a formula
      // may trigger assertions to add to d_queue already here.
      d_satRlv->notifyLemma(a, d_queue);
    }
    d_decisionEngine->addAssertion(a, isLemma);
  }
  else
  {
    d_decisionEngine->addSkolemDefinition(a, skolem, isLemma);
  }
}

void TheoryProxy::variableNotify(SatVariable var) {
  Node n = d_cnfStream->getNode(SatLiteral(var));
  if (d_satRlv != nullptr)
  {
    d_satRlv->notifyVarNotify(n);
  }
  else
  {
    d_theoryEngine->preRegister(n);
  }
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  if (d_satRlv != nullptr)
  {
    d_satRlv->check(effort, d_queue);
  }
  while (!d_queue.empty()) {
    TNode assertion = d_queue.front();
    d_queue.pop();
    if (d_zll != nullptr)
    {
      if (d_stopSearch.get())
      {
        break;
      }
      int32_t alevel = d_propEngine->getDecisionLevel(assertion);
      if (!d_zll->notifyAsserted(assertion, alevel))
      {
        d_stopSearch = true;
        break;
      }
    }
    // now, assert to theory engine
    d_theoryEngine->assertFact(assertion);
    if (d_dmNeedsActiveDefs || d_satRlv != nullptr)
    {
      Assert(d_skdm != nullptr);
      Trace("sat-rlv-assert")
          << "Assert to theory engine: " << assertion << std::endl;
      // assertion processed makes all skolems in assertion active,
      // which triggers their definitions to becoming relevant
      std::vector<TNode> activeSkolemDefs;
      d_skdm->notifyAsserted(assertion, activeSkolemDefs);
      if (!activeSkolemDefs.empty())
      {
        if (d_satRlv != nullptr)
        {
          d_satRlv->notifyActivatedSkolemDefs(activeSkolemDefs, d_queue);
        }
        // notify the decision engine of the skolem definitions that have become
        // active due to the assertion.
        d_decisionEngine->notifyActiveSkolemDefs(activeSkolemDefs);
      }
    }
  }
  if (!d_stopSearch.get())
  {
    d_theoryEngine->check(effort);
  }
}

void TheoryProxy::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    /*
    // TEMPORARY
    if (d_satRlv != nullptr)
    {
      d_satRlv->notifyPropagate(outputNodes[i]);
    }
    */
    Trace("prop-explain") << "theoryPropagate() => " << outputNodes[i] << std::endl;
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void TheoryProxy::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Trace("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;

  TrustNode tte = d_theoryEngine->getExplanation(lNode);
  Node theoryExplanation = tte.getNode();
  if (d_env.isSatProofProducing())
  {
    Assert(options().smt.proofMode != options::ProofMode::FULL
           || tte.getGenerator());
    d_propEngine->getProofCnfStream()->convertPropagation(tte);
  }
  Trace("prop-explain") << "explainPropagation() => " << theoryExplanation
                        << std::endl;
  explanation.push_back(l);
  if (theoryExplanation.getKind() == kind::AND)
  {
    for (const Node& n : theoryExplanation)
    {
      explanation.push_back(~d_cnfStream->getLiteral(n));
    }
  }
  else
  {
    explanation.push_back(~d_cnfStream->getLiteral(theoryExplanation));
  }
  if (TraceIsOn("sat-proof"))
  {
    std::stringstream ss;
    ss << "TheoryProxy::explainPropagation: clause for lit is ";
    for (unsigned i = 0, size = explanation.size(); i < size; ++i)
    {
      ss << explanation[i] << " [" << d_cnfStream->getNode(explanation[i])
         << "] ";
    }
    Trace("sat-proof") << ss.str() << "\n";
  }
}

void TheoryProxy::notifyCurrPropagationInsertedAtLevel(int explLevel)
{
  d_propEngine->getProofCnfStream()->notifyCurrPropagationInsertedAtLevel(
      explLevel);
}

void TheoryProxy::notifyClauseInsertedAtLevel(const SatClause& clause,
                                              int clLevel)
{
  d_propEngine->getProofCnfStream()->notifyClauseInsertedAtLevel(clause,
                                                                 clLevel);
}

void TheoryProxy::enqueueTheoryLiteral(const SatLiteral& l) {
  if (d_satRlv != nullptr)
  {
    // use the sat relevancy to enqueue literals that are relevant
    d_satRlv->notifyAsserted(l, d_queue);
    return;
  }
  Node literalNode = d_cnfStream->getNode(l);
  Trace("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_queue.push(literalNode);
}

SatLiteral TheoryProxy::getNextTheoryDecisionRequest() {
  TNode n = d_theoryEngine->getNextDecisionRequest();
  // it becomes relevant in this context
  if (!n.isNull())
  {
    SatLiteral lit = d_cnfStream->getLiteral(n);
    if (d_satRlv != nullptr)
    {
      // also notify the SAT relevancy module, which will make this request
      // relevant
      d_satRlv->notifyDecisionRequest(n, d_queue);
    }
    return lit;
  }
  return undefSatLiteral;
}

SatLiteral TheoryProxy::getNextDecisionEngineRequest(bool &stopSearch) {
  Assert(d_decisionEngine != NULL);
  Assert(stopSearch != true);
  if (d_stopSearch.get())
  {
    stopSearch = true;
    return undefSatLiteral;
  }
  SatLiteral ret = d_decisionEngine->getNext(stopSearch);
  if(stopSearch) {
    Trace("decision") << "  ***  Decision Engine stopped search *** " << std::endl;
  }
  return ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  if (d_stopSearch.get())
  {
    return false;
  }
  return d_theoryEngine->needCheck();
}

bool TheoryProxy::isIncomplete() const
{
  return d_stopSearch.get() || d_theoryEngine->isIncomplete();
}

theory::IncompleteId TheoryProxy::getIncompleteId() const
{
  if (d_stopSearch.get())
  {
    return theory::IncompleteId::STOP_SEARCH;
  }
  return d_theoryEngine->getIncompleteId();
}

TNode TheoryProxy::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void TheoryProxy::notifyRestart() {
  d_propEngine->spendResource(Resource::RestartStep);
  d_theoryEngine->notifyRestart();
}

void TheoryProxy::spendResource(Resource r)
{
  d_theoryEngine->spendResource(r);
}

bool TheoryProxy::isDecisionRelevant(SatVariable var) { return true; }

bool TheoryProxy::isDecisionEngineDone() {
  return d_decisionEngine->isDone() || d_stopSearch.get();
}

SatValue TheoryProxy::getDecisionPolarity(SatVariable var) {
  return SAT_VALUE_UNKNOWN;
}

CnfStream* TheoryProxy::getCnfStream() { return d_cnfStream; }

TrustNode TheoryProxy::preprocessLemma(
    TrustNode trn, std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_tpp.preprocessLemma(trn, newLemmas);
}

TrustNode TheoryProxy::preprocess(TNode node,
                                  std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_tpp.preprocess(node, newLemmas);
}

TrustNode TheoryProxy::removeItes(TNode node,
                                  std::vector<theory::SkolemLemma>& newLemmas)
{
  RemoveTermFormulas& rtf = d_tpp.getRemoveTermFormulas();
  return rtf.run(node, newLemmas, true);
}

void TheoryProxy::getSkolems(TNode node,
                             std::vector<Node>& skAsserts,
                             std::vector<Node>& sks)
{
  std::unordered_set<Node> skolems;
  d_skdm->getSkolems(node, skolems);
  for (const Node& k : skolems)
  {
    sks.push_back(k);
    skAsserts.push_back(d_skdm->getDefinitionForSkolem(k));
  }
}

void TheoryProxy::preRegister(Node n)
{
  if (d_satRlv != nullptr)
  {
    // do nothing?
    d_satRlv->notifyPrereg(n);
  }
  else
  {
    d_theoryEngine->preRegister(n);
  }
}

std::vector<Node> TheoryProxy::getLearnedZeroLevelLiterals(
    modes::LearnedLitType ltype) const
{
  if (d_zll != nullptr)
  {
    return d_zll->getLearnedZeroLevelLiterals(ltype);
  }
  return {};
}

modes::LearnedLitType TheoryProxy::getLiteralType(const Node& lit) const
{
  if (d_zll != nullptr)
  {
    return d_zll->computeLearnedLiteralType(lit);
  }
  return modes::LEARNED_LIT_UNKNOWN;
}

std::vector<Node> TheoryProxy::getLearnedZeroLevelLiteralsForRestart() const
{
  if (d_zll != nullptr)
  {
    return d_zll->getLearnedZeroLevelLiteralsForRestart();
  }
  return {};
}

}  // namespace prop
}  // namespace cvc5::internal
