/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus abduction utility, which transforms an arbitrary
 * input into an abduction problem.
 */

#include "theory/quantifiers/sygus/sygus_abduct.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusAbduct::SygusAbduct() {}

Node SygusAbduct::mkAbductionConjecture(NodeManager* nm,
                                        const std::string& name,
                                        const std::vector<Node>& asserts,
                                        const std::vector<Node>& axioms,
                                        TypeNode abdGType)
{
  std::unordered_set<Node> symset;
  for (size_t i = 0, size = asserts.size(); i < size; i++)
  {
    expr::getSymbols(asserts[i], symset);
  }
  Trace("sygus-abduct-debug")
      << "...finish, got " << symset.size() << " symbols." << std::endl;

  Trace("sygus-abduct-debug") << "Setup symbols..." << std::endl;
  std::vector<Node> syms;
  std::vector<Node> vars;
  std::vector<Node> varlist;
  std::vector<TypeNode> varlistTypes;
  for (const Node& s : symset)
  {
    TypeNode tn = s.getType();
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      // datatype symbols should be considered interpreted symbols here, not
      // (higher-order) variables.
      continue;
    }
    // Notice that we allow for non-first class (e.g. function) variables here.
    // This is applicable to the case where we are doing get-abduct in a logic
    // with UF.
    std::stringstream ss;
    ss << s;
    Node var = NodeManager::mkBoundVar(tn);
    syms.push_back(s);
    vars.push_back(var);
    Node vlv = NodeManager::mkBoundVar(ss.str(), tn);
    varlist.push_back(vlv);
    varlistTypes.push_back(tn);
    // set that this variable encodes the term s
    SygusVarToTermAttribute sta;
    vlv.setAttribute(sta, s);
  }
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make abduction predicate..." << std::endl;
  // make the abduction predicate to synthesize
  TypeNode abdType = varlistTypes.empty() ? nm->booleanType()
                                          : nm->mkPredicateType(varlistTypes);
  Node abd = NodeManager::mkBoundVar(name.c_str(), abdType);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  // the sygus variable list
  Node abvl;
  // if provided, we will associate the provide sygus datatype type with the
  // function-to-synthesize. However, we must convert it so that its
  // free symbols are universally quantified.
  if (!abdGType.isNull())
  {
    Assert(abdGType.isDatatype() && abdGType.getDType().isSygus());
    Trace("sygus-abduct-debug") << "Process abduction type:" << std::endl;
    Trace("sygus-abduct-debug") << abdGType.getDType().getName() << std::endl;

    // substitute the free symbols of the grammar with variables corresponding
    // to the formal argument list of the new sygus datatype type.
    TypeNode abdGTypeS = datatypes::utils::substituteAndGeneralizeSygusType(
        abdGType, syms, varlist);

    Assert(abdGTypeS.isDatatype() && abdGTypeS.getDType().isSygus());

    Trace("sygus-abduct-debug")
        << "Make sygus grammar attribute..." << std::endl;
    // Set the sygus grammar attribute to indicate that abdGTypeS encodes the
    // grammar for abd.
    SygusUtils::setSygusType(abd, abdGTypeS);
    Trace("sygus-abduct-debug") << "Finished setting up grammar." << std::endl;

    // use the bound variable list from the new substituted grammar type
    const DType& agtsd = abdGTypeS.getDType();
    abvl = agtsd.getSygusVarList();
    Assert(!abvl.isNull() && abvl.getKind() == Kind::BOUND_VAR_LIST);
  }
  else if (!varlist.empty())
  {
    // the bound variable list of the abduct-to-synthesize is determined by
    // the variable list above
    abvl = nm->mkNode(Kind::BOUND_VAR_LIST, varlist);
    // We do not set a grammar type for abd (SygusSynthGrammarAttribute).
    // Its grammar will be constructed internally in the default way
  }

  Trace("sygus-abduct-debug") << "Make abduction predicate app..." << std::endl;
  std::vector<Node> achildren;
  achildren.push_back(abd);
  achildren.insert(achildren.end(), vars.begin(), vars.end());
  Node abdApp = vars.empty() ? abd : nm->mkNode(Kind::APPLY_UF, achildren);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Set attributes..." << std::endl;
  // set the sygus bound variable list
  SygusUtils::setSygusArgumentList(abd, abvl);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make conjecture body..." << std::endl;
  Node input =
      asserts.size() == 1 ? asserts[0] : nm->mkNode(Kind::AND, asserts);
  input = input.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  // A(x) => ~input( x )
  input = nm->mkNode(Kind::OR, abdApp.negate(), input.negate());
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make conjecture..." << std::endl;
  Node res = input.negate();
  if (!vars.empty())
  {
    Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, vars);
    // exists x. ~( A( x ) => ~input( x ) )
    res = nm->mkNode(Kind::EXISTS, bvl, res);
  }
  // sygus attribute
  Node aconj =
      axioms.size() == 0
          ? nm->mkConst(true)
          : (axioms.size() == 1 ? axioms[0] : nm->mkNode(Kind::AND, axioms));
  aconj = aconj.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  Trace("sygus-abduct") << "---> Assumptions: " << aconj << std::endl;
  Node sc = nm->mkNode(Kind::AND, aconj, abdApp);
  if (!vars.empty())
  {
    Node vbvl = nm->mkNode(Kind::BOUND_VAR_LIST, vars);
    sc = nm->mkNode(Kind::EXISTS, vbvl, sc);
  }
  Node sygusScVar = NodeManager::mkDummySkolem("sygus_sc", nm->booleanType());
  sygusScVar.setAttribute(theory::SygusSideConditionAttribute(), sc);
  Node instAttr = nm->mkNode(Kind::INST_ATTRIBUTE, sygusScVar);
  // build in the side condition
  //   exists x. A( x ) ^ input_axioms( x )
  // as an additional annotation on the sygus conjecture. In other words,
  // the abducts A we procedure must be consistent with our axioms.

  // forall A. exists x. ~( A( x ) => ~input( x ) )
  res = SygusUtils::mkSygusConjecture(nm, {abd}, res, {instAttr});
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct") << "Generate: " << res << std::endl;

  return res;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
