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
 * A utility for updating proof nodes.
 */

#include "proof/proof_node_converter.h"

#include "proof/proof.h"

namespace cvc5::internal {

ProofNodeConverter::ProofNodeConverter(Env& env,
                                       ProofNodeConverterCallback& cb,
                                       bool autoSym)
    : EnvObj(env), d_cb(cb)
{
}

std::shared_ptr<ProofNode> ProofNodeConverter::process(
    std::shared_ptr<ProofNode> pf)
{
  // The list of proof nodes we are currently traversing beneath. This is used
  // for checking for cycles in the overall proof.
  std::vector<std::shared_ptr<ProofNode>> traversing;
  std::shared_ptr<ProofNode> pft = pf;
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, std::shared_ptr<ProofNode>>
      visited;
  std::unordered_map<std::shared_ptr<ProofNode>,
                     std::shared_ptr<ProofNode>>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      traversing.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      // now, process children
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        if (std::find(traversing.begin(), traversing.end(), cp)
            != traversing.end())
        {
          Unhandled()
              << "ProofNodeUpdater::processInternal: cyclic proof! (use "
                 "--proof-check=eager)"
              << std::endl;
        }
        visit.push_back(cp);
      }
      continue;
    }
    visit.pop_back();
    if (it->second == nullptr)
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      std::vector<std::shared_ptr<ProofNode>> pchildren;
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        it = visited.find(cp);
        Assert(it != visited.end());
        pchildren.push_back(it->second);
      }
      std::shared_ptr<ProofNode> ret = processInternal(cur, pchildren);
      if (ret==nullptr)
      {
        return nullptr;
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
  return visited[pf];
}

std::shared_ptr<ProofNode> ProofNodeConverter::processInternal(
    std::shared_ptr<ProofNode> pf,
    const std::vector<std::shared_ptr<ProofNode>>& pchildren)
{
  ProofRule id = pf->getRule();
  // use CDProof to open a scope for which the callback updates
  CDProof cpf(d_env, nullptr, "ProofNodeConverter::CDProof", false);
  Node res = pf->getResult();
  std::vector<Node> children;
    for (const std::shared_ptr<ProofNode>& cp : pchildren)
    {
        children.push_back(cp->getResult());
    }
  const std::vector<Node>& args = pf->getArguments();
  Node newRes = d_cb.convert(res, id, children, args, &cpf);
  if (newRes.isNull())
  {
      return nullptr;
  }
  return cpf.getProofFor(newRes);
}

}  // namespace cvc5::internal
