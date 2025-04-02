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

namespace cvc5::internal {
namespace theory {

TermDbManager::TermDbManager(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "TermDbManager"), d_omap(userContext())
{
}

void TermDbManager::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.insert(visit.end(), assertions.begin(), assertions.end());
  do
  {
    cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());

  std::vector<Node> emptyVec;
  for (TNode t : visited)
  {
    addOrigin(t, InferenceId::NONE, emptyVec);
  }
}

void TermDbManager::notifyLemma(TNode n,
                                InferenceId id,
                                LemmaProperty p,
                                const std::vector<Node>& skAsserts,
                                const std::vector<Node>& sks)
{
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
    }
  }
}

}  // namespace theory
}  // namespace cvc5::internal
