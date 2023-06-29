/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof rewriter
 */


#include "proof/proof_rewriter.h"

#include "proof/proof_rule_checker.h"

namespace cvc5::internal {
  
ProofRewriter::ProofRewriter(ProofNodeManager* pnm) : d_pnm(pnm) {}
  
void ProofRewriter::rewrite(std::shared_ptr<ProofNode> pn)
{
  PfRule id = pn->getRule();
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  std::shared_ptr<ProofNode> pnr = nullptr;
  if (id==PfRule::SYMM)
  {
    if (children[0]->getRule()==PfRule::SYMM)
    {
      pnr = children[0]->getChildren()[0];
    }
  }
  else if (id==PfRule::AND_ELIM)
  {
    if (children[0]->getRule()==PfRule::AND_INTRO)
    {
      uint32_t i;
      if (ProofRuleChecker::getUInt32(pn->getArguments()[0], i))
      {
        Assert (i<children[0]->getChildren().size());
        pnr = children[0]->getChildren()[i];
      }
    }
  }
  else if (id==PfRule::EQ_RESOLVE)
  {
    if (children[0]->getRule()==PfRule::EQ_RESOLVE && children[0]->getChildren()[0]->getResult()==pn->getResult())
    {
      pnr = children[0]->getChildren()[0];
    }
  }
  if (pnr==nullptr)
  {
    for (std::shared_ptr<ProofNode> c : children)
    {
      const std::vector<std::shared_ptr<ProofNode>>& children2 = c->getChildren();
      if (c->getResult()==pn->getResult())
      {
        AlwaysAssert(id==PfRule::SCOPE || c->getRule()==PfRule::SCOPE) << "Found child proof eq " << id << " at " << c->getRule();
      }
      for (size_t i=0, nchildren = children2.size(); i<nchildren; i++)
      {
        if (children2[i]->getResult()==pn->getResult())
        {
          AlwaysAssert(id==PfRule::SCOPE || c->getRule()==PfRule::SCOPE) << "Found child proof eq " << id << " under " << c->getRule() << " at child " << i << std::endl << *pn.get();
        }
      }
    }
  }
  if (pnr!=nullptr)
  {
    d_pnm->updateNode(pn.get(), pnr.get());
  }
}

}
