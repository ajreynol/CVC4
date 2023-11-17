/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds,
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevance manager.
 */

#include "theory/assigner_infer.h"

#include "expr/assigner.h"
#include "expr/node_algorithm.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace theory {

AssignerInference::AssignerInference(Env& env)
    : EnvObj(env),
      d_numAssigners(statisticsRegistry().registerInt(
          "theory::AssignerInference::numAssigners"))
{
}
void AssignerInference::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<Node> visited;
  for (const Node& a : assertions)
  {
    registerAssigners(visited, a);
  }
}

Node AssignerInference::getSymbolsHash(const Node& n)
{
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  // get the free symbols in the literal
  expr::getSymbols(n, syms, visited);
  if (syms.empty())
  {
    return Node::null();
  }
  std::vector<Node> symvec;
  symvec.insert(symvec.end(), syms.begin(), syms.end());
  if (symvec.size() == 1)
  {
    return symvec[0];
  }
  std::sort(symvec.begin(), symvec.end());
  return NodeManager::currentNM()->mkNode(Kind::SEXPR, symvec);
}

bool AssignerInference::registerAssigner(const Node& n)
{
  Assert(n.getKind() == Kind::OR);
  Node symHash;
  for (const Node& nc : n)
  {
    if (!Assigner::isLiteralCube(nc))
    {
      return false;
    }
    Node h = getSymbolsHash(nc);
    if (h.isNull())
    {
      return false;
    }
    if (symHash.isNull())
    {
      symHash = h;
    }
    else if (symHash != h)
    {
      return false;
    }
  }
  if (Assigner::isAssigner(n))
  {
    d_numAssigners++;
    CVC5_UNUSED Assigner* a = d_env.registerAssigner(n);
    Assert(a != nullptr);
    Trace("assigner") << "Found assigner: " << n << std::endl;
    return true;
  }
  return false;
}

void AssignerInference::registerAssigners(std::unordered_set<Node>& visited,
                                          const Node& n)
{
  std::unordered_set<Node>::iterator it;
  std::unordered_set<Node> processedInferred;
  std::vector<Node> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (expr::isBooleanConnective(cur))
      {
        // if assigner, register to env
        if (cur.getKind() == Kind::OR && registerAssigner(cur))
        {
          continue;
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

}  // namespace theory
}  // namespace cvc5::internal
