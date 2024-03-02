/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for final processing proof nodes.
 */

#include "smt/proof_post_processor_dsl.h"

#include "theory/uf/embedding_op.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofPostprocessDsl::ProofPostprocessDsl(Env& env, rewriter::RewriteDb* rdb)
    : EnvObj(env), d_rdbPc(env, rdb)
{
  NodeManager * nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  // initialize the axioms
  const std::map<rewriter::DslProofRule, rewriter::RewriteProofRule>& rules = rdb->getAllRules();
  for (const std::pair<const rewriter::DslProofRule, rewriter::RewriteProofRule>& rr : rules)
  {
    const rewriter::RewriteProofRule& rpr = rr.second;
    Node conc = rpr.getConclusion(true);
    const std::vector<Node>& conds = rpr.getConditions();
    Node ax = conds.empty() ? conc : nm->mkNode(Kind::IMPLIES, nm->mkAnd(conds), conc);
    const std::vector<Node>& vars = rpr.getVarList();
    if (!vars.empty())
    {
      ax = nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, vars), ax);
    }
    Trace("pp-dsl") << "Embedding of " << rr.first << " is " << ax << std::endl;
    // convert to embedding
    ax = EmbeddingOp::convertToEmbedding(ax);
    d_embedAxioms.push_back(ax);
    d_axRule[ax] = rr.first;
  }
}

void ProofPostprocessDsl::reconstruct(
    std::unordered_set<std::shared_ptr<ProofNode>>& pfs)
{
  // run an updated for this
  ProofNodeUpdater pnu(d_env, *this, false);
  for (std::shared_ptr<ProofNode> p : pfs)
  {
    pnu.process(p);
  }
}

bool ProofPostprocessDsl::reconstruct(std::shared_ptr<ProofNode>& pf)
{
  return true;
}

bool ProofPostprocessDsl::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                       const std::vector<Node>& fa,
                                       bool& continueUpdate)
{
  ProofRule id = pn->getRule();
  return id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE;
}

bool ProofPostprocessDsl::update(Node res,
                                 ProofRule id,
                                 const std::vector<Node>& children,
                                 const std::vector<Node>& args,
                                 CDProof* cdp,
                                 bool& continueUpdate)
{
  continueUpdate = false;
  Assert(id == ProofRule::TRUST || id == ProofRule::TRUST_THEORY_REWRITE);
  // don't try if children are non-empty
  if (!children.empty())
  {
    return false;
  }
  bool reqTrueElim = false;
  // if not an equality, make (= res true).
  if (res.getKind() != Kind::EQUAL)
  {
    res = res.eqNode(d_true);
    reqTrueElim = true;
  }
  TheoryId tid = THEORY_LAST;
  MethodId mid = MethodId::RW_REWRITE;
  // if theory rewrite, get diagnostic information
  if (id == ProofRule::TRUST_THEORY_REWRITE)
  {
    builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
    getMethodId(args[2], mid);
  }
  int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
  int64_t stepLimit = options().proof.proofRewriteRconsStepLimit;
  // attempt to reconstruct the proof of the equality into cdp using the
  // rewrite database proof reconstructor
  if (d_rdbPc.prove(cdp, res[0], res[1], tid, mid, recLimit, stepLimit))
  {
    // If we made (= res true) above, conclude the original res.
    if (reqTrueElim)
    {
      cdp->addStep(res[0], ProofRule::TRUE_ELIM, {res}, {});
      res = res[0];
    }
    // if successful, we update the proof
    return true;
  }
  // otherwise no update
  return false;
}

bool ProofPostprocessDsl::isProvable(
    std::unique_ptr<SolverEngine>& se,
    const Node& n, std::unordered_set<rewriter::DslProofRule>& ucRules)
{
  se->push();
  Node nembed = EmbeddingOp::convertToEmbedding(n);
  se->assertFormula(nembed.negate());
  Result r = se->checkSat();
  se->pop();
  std::vector<Node> uc;
  getUnsatCoreFromSubsolver(*se.get(), uc);
  std::map<Node, rewriter::DslProofRule>::iterator it;
  for (const Node& u : uc)
  {
    it =  d_axRule.find(u);
    if (it !=d_axRule.end())
    {
      ucRules.insert(it->second);
    }
  }

  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
