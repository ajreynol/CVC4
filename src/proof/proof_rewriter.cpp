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

namespace cvc5::internal {
  
ProofRewriter::ProofRewriter(ProofNodeManager* pnm) : d_pnm(pnm) {}
  
void ProofRewriter::rewrite(std::shared_ptr<ProofNode> pn)
{
  PfRule id = pn->getRule();
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  ProofNode* pnr = nullptr;
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
      if (getUInt32(pn->getArgs()[0], i))
      {
        Assert (i<children[0]->getChildren().size());
        pnr = children[0]->getChildren()[i];
      }
    }
  }
  if (pnr!=nullptr)
  {
    d_pnm->updateNode(pn.get(), pnr);
  }
}

}
