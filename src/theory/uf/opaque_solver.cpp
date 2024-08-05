/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of opaque solver.
 */

#include "theory/uf/opaque_solver.h"

#include "expr/skolem_manager.h"
#include "options/uf_options.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/uf/opaque_value.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"
#include "options/smt_options.h"
#include "theory/smt_engine_subsolver.h"
#include "proof/unsat_core.h"
#include "expr/attribute.h"


using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {
  
struct OpaqueFormAttributeId
{
};
using OpaqueFormAttribute = expr::Attribute<OpaqueFormAttributeId, Node>;
    
Node OpaqueConverter::postConvertUntyped(Node orig,
                        const std::vector<Node>& terms,
                        bool termsChanged)
{
  Kind ok = orig.getKind();
  if (ok==Kind::APPLY_OPAQUE)
  {
    std::vector<Node> cc;
    for (size_t i=1, nterms = terms.size(); i<nterms; i++)
    {
      const Node& t = terms[i];
      if (t.getKind() == Kind::OPAQUE_VALUE)
      {
        cc.push_back(t.getConst<OpaqueValue>().getValue());
      }
      else
      {
        cc.push_back(t);
      }
    }
    return TheoryUfRewriter::getOriginalFromOpaque(orig, cc);
  }
  else if (ok==Kind::EQUAL)
  {
    return d_nm->mkNode(Kind::EQUAL, terms);
  }
  else if (orig.getNumChildren()>0)
  {
    SkolemManager * skm = d_nm->getSkolemManager();
    return skm->mkPurifySkolem(orig);
  }
  else if (orig.isVar() && orig.getType().isOpaque())
  {
    SkolemManager * skm = d_nm->getSkolemManager();
    SkolemId id;
    Node cacheVal;
    if (skm->isSkolemFunction(orig, id, cacheVal))
    {
      Assert (id==SkolemFunId::PURIFY_OPAQUE);
      return cacheVal[1];
    }
    Assert (false);
  }
  return orig;
}
                          
OpaqueSolver::OpaqueSolver(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_oconv(nodeManager()),
      d_asserts(context())
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // requires full proofs
  d_subOptions.write_smt().produceProofs = true;
  // don't do simplification, which can preprocess quantifiers to those not
  // occurring in the main solver
  d_subOptions.write_smt().simplificationMode =
      options::SimplificationMode::NONE;
  // requires unsat cores
  d_subOptions.write_smt().produceUnsatCores = true;
  // don't do this strategy
  d_subOptions.write_smt().elimArith = false;
}

OpaqueSolver::~OpaqueSolver() {}

void OpaqueSolver::preRegisterTerm(TNode term)
{
}

void OpaqueSolver::check()
{
  if (d_asserts.empty())
  {
    return;
  }
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> findConflict;
  initializeSubsolver(findConflict, ssi, false);
  // assert and check-sat
  Trace("opaque-solver") << "Check opaque with " << d_asserts.size() << " assertions..." << std::endl;
  for (const std::pair<Node, bool>& a : d_asserts)
  {
    Node lit = a.second ? a.first : a.first.notNode();
    Trace("opaque-assert") << "- " << lit << std::endl;
    findConflict->assertFormula(lit);
  }
  Result r = findConflict->checkSat();
  Trace("opaque-solver") << "<<< ...result is " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    UnsatCore uc = findConflict->getUnsatCore();
    std::vector<Node> opaqueCore;
    OpaqueFormAttribute ofa;
    for (const Node& a : uc)
    {
      bool pol = a.getKind()!=Kind::NOT;
      Node oa = pol ? a : a[0];
      oa = oa.getAttribute(ofa);
      Assert (!oa.isNull());
      opaqueCore.push_back(pol ? oa : oa.notNode());
    }
    Node ucc = nodeManager()->mkAnd(opaqueCore);
    Trace("opaque-solver") << "Unsat core is " << ucc << std::endl;
    Trace("opaque-solver") << "Core size = " << uc.getCore().size() << std::endl;
    d_im.lemma(ucc.notNode(), InferenceId::OPAQUE_SUB_UC);
  }
}

void OpaqueSolver::notifyFact(const Node& atom, bool pol)
{
  Node catom = convertFromOpaque(atom);
  OpaqueFormAttribute ofa;
  catom.setAttribute(ofa, atom);
  d_asserts.push_back(std::pair<Node, bool>(catom, pol));
}

Node OpaqueSolver::convertFromOpaque(const Node& n)
{
  return d_oconv.convert(n, false);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
