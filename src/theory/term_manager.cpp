/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term manager.
 */

#include "theory/term_manager.h"

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers_engine.h"
#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {

TermDbManager::TermDbManager(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "TermDbManager"), d_omap(userContext()), d_qinLevel(userContext()), d_inputTerms(userContext())
{
}

void TermDbManager::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  std::vector<Node> emptyVec;
  visit.insert(visit.end(), assertions.begin(), assertions.end());
  do
  {
    cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!expr::isBooleanConnective(cur))
      {
        d_inputTerms.insert(cur);
        addOrigin(cur, InferenceId::NONE, emptyVec);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void TermDbManager::notifyLemma(TNode n,
                                InferenceId id,
                                LemmaProperty p,
                                const std::vector<Node>& skAsserts,
                                const std::vector<Node>& sks)
{
  Node q;
  Node lem = n;
  std::vector<Node> args;
  if (n.getKind()==Kind::IMPLIES && n[0].getKind()==Kind::FORALL)
  {
    // Assume any lemma of the form (=> (forall ...) ...) is an instantiation
    // lemma.
    QuantifiersEngine* qe = d_val.getQuantifiersEngine();
    if (qe->getTermVectorForInstantiation(n, args))
    {
      args.insert(args.begin(), n[0]);
      lem = n[1];
    }
  }
  // get new terms
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.emplace_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_inputTerms.find(cur)!=d_inputTerms.end())
    {
      // input terms never change origin
      continue;
    }
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!expr::isBooleanConnective(cur))
      {
        addOrigin(cur, id, args);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

TermDbManager::TermOrigin::TermOrigin(context::Context* c)
    : d_origin(c), d_quantDepth(c)
{
}
void TermDbManager::TermOrigin::addOrigin(InferenceId id, const Node& arg)
{
  d_origin.emplace_back(id, arg);
}

void TermDbManager::addOrigin(const Node& n,
                              InferenceId id,
                              const std::vector<Node>& args)
{
  Node arg;
  if (args.size() == 1)
  {
    arg = args[0];
  }
  else
  {
    arg = nodeManager()->mkNode(Kind::SEXPR, args);
  }
  TermOrigin* t;
  context::CDHashMap<Node, std::shared_ptr<TermOrigin>>::iterator it =
      d_omap.find(n);
  if (it == d_omap.end())
  {
    std::shared_ptr<TermOrigin> tor =
        std::make_shared<TermOrigin>(userContext());
    initializeTerm(n);
    d_omap.insert(n, tor);
    t = tor.get();
  }
  else
  {
    t = it->second.get();
  }
  Trace("term-origin") << "Term " << n << " has origin " << id << " / " << args << std::endl;
  t->addOrigin(id, arg);
}

void TermDbManager::initializeTerm(const Node& n)
{
  if (n.getKind() == Kind::FORALL)
  {
    // get the origin level specified by user attribute
    // :quant-inst-origin-max-level.
    quantifiers::QAttributes qa;
    quantifiers::QuantAttributes::computeQuantAttributes(n, qa);
    if (qa.d_qinstNestedLevel != -1)
    {
      d_qinLevel[n] = qa.d_qinstNestedLevel;
      Trace("term-origin") << "Quantified formula " << n << " has inst nested level " << qa.d_qinstNestedLevel << std::endl;
    }
  }
}

}  // namespace theory
}  // namespace cvc5::internal
