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
 * Trivial inst match generator class.
 */

#include "theory/quantifiers/ematching/inst_match_generator_trivial.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstMatchGeneratorTrivial::InstMatchGeneratorTrivial(Env& env, Trigger* tparent, Node q, Node pat) : d_quant(q), d_pat(pat), d_terms(d_env.getUserContext()){
  
  for (size_t i = 0, nchild = d_pat.getNumChildren(); i < nchild; i++)
  {
    Assert (d_pat[i].getKind() == Kind::INST_CONSTANT);
    d_varNum.push_back(d_pat[i].getAttribute(InstVarNumAttribute()));
  }
}

void InstMatchGeneratorTrivial::resetInstantiationRound()
{
  // do nothing
}

uint64_t InstMatchGeneratorTrivial::addInstantiations(InstMatch& m)
{
  TermDb* tdb = d_treg.getTermDatabase();
  DbList* dbl = tdb->getGroundTermList(f);
  context::CDList<Node>& list = dbl->d_list;
  uint64_t addedLemmas = 0;
  for (const Node& n : list)
  {
    // if already considered this term
    if (d_terms.find(n)!=d_terms.end())
    {
      continue;
    }
    d_treg.getTermDatabase()->getTermArgTrie(op);
    // not active based on e.g. relevant policy
    if (!tdb->isTermActive(n))
    {
      continue;
    }
    d_terms.insert(n);
    Assert (n.getNumChildren()==d_quant[0].getNumChildren());
    std::vector<Node> terms;
    terms.resize(n.getNumChildren());
    for (size_t i=0, nvars=d_varNum.size(); i<nvars; i++)
    {
      Assert(v.first < n.getNumChildren());
      terms[d_varNum[i]] = n[i];
    }
    if (sendInstantiation(terms,
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_TRIVIAL))
    {
      addedLemmas++;
    }
  }
  return addedLemmas;
}

int InstMatchGeneratorTrivial::getActiveScore()
{
  TermDb* tdb = d_treg.getTermDatabase();
  Node f = tdb->getMatchOperator(d_pat);
  size_t ngt = tdb->getNumGroundTerms(f);
  return static_cast<int>(ngt);
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

