/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Apply substitutions preprocessing pass.
 *
 * Apply top level substitutions to assertions, rewrite, and store back into
 * assertions.
 */

#include "preprocessing/passes/assigner_infer.h"

#include "expr/assigner.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/theory_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

AssignerInfer::AssignerInfer(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "assigner-infer"),
      d_numAssigners(
          statisticsRegistry().registerInt("AssignerInfer::numAssigners"))
{
}

PreprocessingPassResult AssignerInfer::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  std::vector<Node> lemmas;
  std::unordered_map<Node, Node> visited;
  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < size; ++i)
  {
    const Node& assertion = (*assertionsToPreprocess)[i];
    const Node& aa = convertToAssigner(visited, assertion, lemmas);
    if (aa != assertion || !lemmas.empty())
    {
      std::vector<Node> conj;
      conj.push_back(aa);
      conj.insert(conj.end(), lemmas.begin(), lemmas.end());
      Node anew = nm->mkAnd(conj);
      assertionsToPreprocess->replace(i, anew);
      lemmas.clear();
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node AssignerInfer::getSymbolsHash(const Node& n)
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

Node AssignerInfer::inferAssigners(const Node& n, std::vector<Node>& lemmas)
{
  Assert(n.getKind() == Kind::OR);
  std::map<Node, std::vector<Node>> symHashToLits;
  std::vector<Node> resLits;
  for (const Node& nc : n)
  {
    if (Assigner::isLiteralCube(nc))
    {
      Node h = getSymbolsHash(nc);
      if (!h.isNull())
      {
        symHashToLits[h].push_back(nc);
        continue;
      }
    }
    // TODO: flatten OR?
    resLits.push_back(nc);
  }
  NodeManager* nm = NodeManager::currentNM();
  bool changed = false;
  // for each grouping
  for (std::pair<const Node, std::vector<Node>>& hl : symHashToLits)
  {
    Node ca;
    if (hl.second.size() == 1)
    {
      resLits.push_back(hl.second[0]);
      continue;
    }
    else if (hl.second.size() == n.getNumChildren())
    {
      ca = n;
    }
    else
    {
      ca = nm->mkOr(hl.second);
    }
    if (Assigner::isAssigner(ca))
    {
      d_numAssigners++;
      Assigner* a = d_env.registerAssigner(ca);
      Assert(a != nullptr);
      Node lit = a->getSatLiteral();
      Trace("assigner") << "Found assigner: " << lit << " <=> " << ca
                        << std::endl;
      /*
      SkolemManager* skm = nm->getSkolemManager();
      Node conc = ca;
      if (options().theory.assignerProxy)
      {
        SkolemManager* skm = nm->getSkolemManager();
        std::vector<Node> cdisj;
        for (const Node& cc : ca)
        {
          Assert(cc.getKind() != Kind::NOT);
          cdisj.push_back(skm->mkProxyLit(cc));
        }
        conc = nm->mkOr(cdisj);
      }
      Node lem = nm->mkNode(Kind::EQUAL, lit, conc);
      lemmas.emplace_back(lem);
      */
      resLits.push_back(lit);
      changed = true;
    }
  }
  if (changed)
  {
    return nm->mkOr(resLits);
  }
  return n;
}

Node AssignerInfer::convertToAssigner(std::unordered_map<Node, Node>& visited,
                                      const Node& n,
                                      std::vector<Node>& lemmas)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node> visitedPre;
  std::unordered_map<Node, Node>::iterator it;
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
      if (expr::isBooleanConnective(cur))
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        // if assigner, register to node manager, and replace by its assigner
        // variable
        if (cur.getKind() == Kind::OR
            && processedInferred.find(cur) == processedInferred.end())
        {
          Node cura = inferAssigners(cur, lemmas);
          if (cura != cur)
          {
            // don't recompute
            processedInferred.insert(cura);
            visitedPre[cur] = cura;
            visit.push_back(cura);
            continue;
          }
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      visited[cur] = cur;
    }
    else if (it->second.isNull())
    {
      it = visitedPre.find(cur);
      if (it != visitedPre.end())
      {
        visited[cur] = visited[it->second];
        continue;
      }
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
