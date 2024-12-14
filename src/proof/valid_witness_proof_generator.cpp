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
#include "expr/sort_to_term.h"
#include "proof/proof.h"
#include "proof/proof_rule_checker.h"
#include "util/string.h"

namespace cvc5::internal {

Node mkProofSpec(NodeManager* nm, ProofRule r, const std::vector<Node>& args)
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

bool getProofSpec(const Node& attr, ProofRule& r, std::vector<Node>& args)
{
  if (attr.getKind()==Kind::INST_ATTRIBUTE && attr.getNumChildren()==2)
  {
    std::string str = attr[0].getConst<String>().toString();
    if (str=="witness" && attr[1].getKind()==Kind::SEXPR && attr[1].getNumChildren()>0)
    {
      Node rn = attr[1][0];
      uint32_t rval;
      if (ProofRuleChecker::getUInt32(rn, rval))
      {
        r = static_cast<ProofRule>(rval);
        args.insert(args.end(), attr[1].begin()+1, attr[1].end());
        return true;
      }
    }
  }
  return false;
}

ValidWitnessProofGenerator::ValidWitnessProofGenerator(Env& env) : EnvObj(env) {}

ValidWitnessProofGenerator::~ValidWitnessProofGenerator() {}

std::shared_ptr<ProofNode> ValidWitnessProofGenerator::getProofFor(Node fact) 
{
  Trace("valid-witness") << "Prove " << fact << std::endl;
  if (fact.getKind()==Kind::NOT && fact[0].getKind()==Kind::FORALL && fact[0].getNumChildren()==2)
  {
    Node attr = fact[0][2][0];
    // should be constructed via mkProofSpec
    ProofRule r;
    std::vector<Node> args;
    if (getProofSpec(attr, r, args))
    {
      Node ex = mkExists(nodeManager(), r, args);
    }
  }
  // proof failed
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::VALID_WITNESS, {}, {});
  return cdp.getProofFor(fact);
}

std::string ValidWitnessProofGenerator::identify() const { return "ValidWitnessProofGenerator"; }

Node ValidWitnessProofGenerator::mkWitness(NodeManager* nm,
                                           ProofRule r,
                                           const std::vector<Node>& args)
{
  Node exists = mkExists(nm, r, args);
  if (exists.isNull())
  {
    return Node::null();
  }
  Assert(exists.getKind() == Kind::NOT && exists[0].getKind() == Kind::FORALL);
  std::vector<Node> children;
  children.push_back(exists[0][0]);
  children.push_back(exists[0][1].negate());
  children.push_back(
      nm->mkNode(Kind::INST_PATTERN_LIST, mkProofSpec(nm, r, args)));
  return nm->mkNode(Kind::WITNESS, children);
}

/**
 * Mapping to the variable used for binding the witness term.
 */
struct ValidWitnessVarAttributeId
{
};
using ValidWitnessVarAttribute =
    expr::Attribute<ValidWitnessVarAttributeId, Node>;

Node ValidWitnessProofGenerator::mkExists(NodeManager* nm,
                                          ProofRule r,
                                          const std::vector<Node>& args)
{
  // first compute the desired type based on the rule and arguments
  TypeNode tn;
  switch (r)
  {
    case ProofRule::EXISTS_STRING_LENGTH:
      Assert(args.size() == 2);
      if (args[0].getKind() == Kind::SORT_TO_TERM)
      {
        tn = args[0].getConst<SortToTerm>().getType();
      }
      break;
    case ProofRule::EXISTS_INVERTIBILITY_CONDITION: break;
    default: break;
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
      Assert(args.size() == 2);
      if (args[1].getKind() == Kind::CONST_INTEGER
          && args[1].getConst<Rational>().getNumerator().sgn() >= 0)
      {
        pred = nm->mkNode(Kind::STRING_LENGTH, v).eqNode(args[1]);
      }
      break;
    case ProofRule::EXISTS_INVERTIBILITY_CONDITION: break;
    default: break;
  }
  if (!pred.isNull())
  {
    Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, v);
    return nm->mkNode(Kind::FORALL, bvl, pred.negate()).notNode();
  }
  return Node::null();
}

}  // namespace cvc5::internal

