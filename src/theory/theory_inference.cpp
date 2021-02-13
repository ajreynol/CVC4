/*********************                                                        */
/*! \file theory_inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory inference utility
 **/

#include "theory/theory_inference.h"

#include "theory/theory_inference_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

SimpleTheoryLemma::SimpleTheoryLemma(InferenceId id, 
                                     Node n,
                                     LemmaProperty p,
                                     ProofGenerator* pg)
    : TheoryInference(id), d_node(n), d_property(p), d_pg(pg)
{
}

bool SimpleTheoryLemma::process(TheoryInferenceManager* im, bool asLemma)
{
  Assert(!d_node.isNull());
  Assert(asLemma);
  // send (trusted) lemma on the output channel with property p
  return im->trustedLemma(TrustNode::mkTrustLemma(d_node, d_pg), getId(), d_property);
}

SimpleTheoryInternalFact::SimpleTheoryInternalFact(InferenceId id,
                                                   Node conc,
                                                   Node exp,
                                                   ProofGenerator* pg)
    : TheoryInference(id), d_conc(conc), d_exp(exp), d_pg(pg)
{
}

bool SimpleTheoryInternalFact::process(TheoryInferenceManager* im, bool asLemma)
{
  Assert(!asLemma);
  bool polarity = d_conc.getKind() != NOT;
  TNode atom = polarity ? d_conc : d_conc[0];
  // no double negation or conjunctive conclusions
  Assert(atom.getKind() != NOT && atom.getKind() != AND);
  if (d_pg != nullptr)
  {
    im->assertInternalFact(atom, polarity, getId(), {d_exp}, d_pg);
  }
  else
  {
    im->assertInternalFact(atom, polarity, getId(), d_exp);
  }
  return true;
}

}  // namespace theory
}  // namespace CVC4
