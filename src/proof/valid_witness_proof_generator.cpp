/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Valid witness proof generator utility.
 */

#include "proof/valid_witness_proof_generator.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "proof/proof.h"
#include "util/string.h"
#include "expr/sort_to_term.h"

namespace cvc5::internal {


ValidWitnessProofGenerator::ValidWitnessProofGenerator(Env& env) : EnvObj(env) {}

ValidWitnessProofGenerator::~ValidWitnessProofGenerator() {}

std::shared_ptr<ProofNode> ValidWitnessProofGenerator::getProofFor(Node fact) 
{
  Trace("valid-witness") << "Prove " << fact << std::endl;
  // proofs not yet supported
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::VALID_WITNESS, {}, {});
  return cdp.getProofFor(fact);
}

std::string ValidWitnessProofGenerator::identify() const { return "ValidWitnessProofGenerator"; }

Node mkProofSpec(NodeManager * nm, ProofRule r, const std::vector<Node>& args)
{
  std::vector<Node> pfspec;
  pfspec.push_back(nm->mkConst(String("witness")));
  std::vector<Node> sargs;
  // store as uint32_t
  sargs.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(r))));
  sargs.insert(sargs.end(), args.begin(), args.end());
  pfspec.push_back(nm->mkNode(Kind::SEXPR, args));
  return nm->mkNode(Kind::INST_ATTRIBUTE, pfspec);
}

Node ValidWitnessProofGenerator::mkWitness(NodeManager * nm, ProofRule r, const std::vector<Node>& args)
{
  Node exists = mkExists(nm, r, args);
  if (exists.isNull())
  {
    return Node::null();
  }
  Assert (exists.getKind()==Kind::NOT && exists[0].getKind()==Kind::FORALL);
  std::vector<Node> children;
  children.push_back(exists[0][0]);
  children.push_back(exists[0][1].negate());
  children.push_back(nm->mkNode(Kind::INST_PATTERN_LIST, mkProofSpec(nm, r, args)));
  return nm->mkNode(Kind::WITNESS, children);
}

/**
 * Mapping to the variable used for binding the witness term.
 */
struct ValidWitnessVarAttributeId
{
};
using ValidWitnessVarAttribute = expr::Attribute<ValidWitnessVarAttributeId, Node>;

Node ValidWitnessProofGenerator::mkExists(NodeManager * nm, ProofRule r, const std::vector<Node>& args)
{
  // first compute the desired type based on the rule and arguments
  TypeNode tn;
  switch (r)
  {
    case ProofRule::EXISTS_STRING_LENGTH:
      Assert (args.size()==2);
      if (args[0].getKind()==Kind::SORT_TO_TERM)
      {
        tn = args[0].getConst<SortToTerm>().getType();
      }
      break;
    case ProofRule::EXISTS_INVERTIBILITY_CONDITION:
      break;
    default:
      break;
  }
  if (tn.isNull())
  {
    return Node::null();
  }
  Node spec = mkProofSpec(nm, r, args);
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node v = bvm->mkBoundVar<ValidWitnessVarAttribute>(spec, "@var.witness", tn);
  // then construct the predicate
  Node pred;
  switch (r)
  {
    case ProofRule::EXISTS_STRING_LENGTH:
      Assert (args.size()==2);
      if (args[1].getKind()==Kind::CONST_INTEGER && args[1].getConst<Rational>().getNumerator().sgn()>=0)
      {
        pred = nm->mkNode(Kind::STRING_LENGTH, v).eqNode(args[1]);
      }
      break;
    case ProofRule::EXISTS_INVERTIBILITY_CONDITION:
      break;
    default:
      break;
  }
  if (!pred.isNull())
  {
    return nm->mkNode(Kind::FORALL, pred.negate()).notNode();
  }
  return Node::null();
}

}  // namespace cvc5::internal

