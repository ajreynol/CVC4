/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Caleb Donovick, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewrite preprocessing pass.
 *
 * Calls the rewriter on every assertion.
 */

#include "preprocessing/passes/dt_elim.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/rewriter.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

bool isUnaryPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::UNIT || policy == DtElimPolicy::UNARY;
}

bool isBinaryTestPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::BINARY_ENUM || policy == DtElimPolicy::BINARY;
}

bool isAbstractPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::ABSTRACT_ENUM
         || policy == DtElimPolicy::ABSTRACT;
}

const char* toString(DtElimPolicy policy)
{
  switch (policy)
  {
    case DtElimPolicy::NONE: return "NONE";
    case DtElimPolicy::UNIT: return "UNIT";
    case DtElimPolicy::UNARY: return "UNARY";
    case DtElimPolicy::BINARY_ENUM: return "BINARY_ENUM";
    case DtElimPolicy::BINARY: return "BINARY";
    case DtElimPolicy::ABSTRACT_ENUM: return "ABSTRACT_ENUM";
    case DtElimPolicy::ABSTRACT: return "ABSTRACT";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, DtElimPolicy policy)
{
  out << toString(policy);
  return out;
}

DtElimConverter::DtElimConverter(Env& env, const std::vector<Node>& assertions)
    : EnvObj(env), NodeConverter(nodeManager())
{
  computePolicies(assertions);
  d_dtElimSc = nodeManager()->mkSortConstructor("@dt-elim-sort", 1);
}
DtElimConverter::~DtElimConverter() {}
/**
 * Compute the policies for each datatype
 */
void DtElimConverter::computePolicies(const std::vector<Node>& assertions)
{
  std::unordered_set<TypeNode> allDt;
  std::unordered_set<TypeNode> preserveTypes;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit(assertions.begin(), assertions.end());
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());

  for (const TypeNode& tn : allDt)
  {
    if (preserveTypes.find(tn) != preserveTypes.end())
    {
      continue;
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    if (dt.isParametric())
    {
      // parameteric datatypes can't be eliminated currently?
      continue;
    }
    bool isEnum = true;
    size_t ncons = dt.getNumConstructors();
    for (size_t i = 0; i < ncons; i++)
    {
      if (dt[i].getNumArgs() > 0)
      {
        isEnum = false;
        break;
      }
    }
    DtElimPolicy policy = DtElimPolicy::NONE;
    if (isEnum)
    {
      policy = (ncons == 1 ? DtElimPolicy::UNIT
                           : (ncons == 2 ? DtElimPolicy::BINARY_ENUM
                                         : DtElimPolicy::ABSTRACT_ENUM));
    }
    else
    {
      // check if recursive
      if (!dt.isRecursive())
      {
        policy = (ncons == 1 ? DtElimPolicy::UNARY
                            : (ncons == 2 ? DtElimPolicy::BINARY
                                          : DtElimPolicy::ABSTRACT));
      }
    }
    Trace("dt-elim-policy")
        << "Policy for " << tn << " is " << policy << std::endl;
  }
}
/**
 */
Node DtElimConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (k == Kind::APPLY_TESTER)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    if (d_dtep.find(tn) == d_dtep.end())
    {
      return n;
    }
    // eliminate the tester
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    size_t i = datatypes::utils::indexOf(n.getOperator());
    Node ticons = datatypes::utils::getInstCons(t, dt, i, false);
    Node eq = t.eqNode(ticons);
    return convert(eq);
  }
  else if (k == Kind::EQUAL)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
    if (itd == d_dtep.end())
    {
      return n;
    }
    else if (itd->second == DtElimPolicy::UNIT)
    {
      // unit equality is always true
      return d_nm->mkConst(true);
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    Node cur = d_nm->mkConst(false);
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      size_t ii = ncons - i - 1;
      // their selectors are each equal
      const std::vector<Node>& sels1 = getSelectorVec(n[0], ii);
      const std::vector<Node>& sels2 = getSelectorVec(n[1], ii);
      Assert(sels1.size() == sels2.size());
      std::vector<Node> conj;
      for (size_t j = 0, nsels = sels1.size(); j < nsels; j++)
      {
        conj.push_back(sels1[j].eqNode(sels2[j]));
      }
      Node eq = d_nm->mkAnd(conj);
      if (ncons == 1)
      {
        cur = eq;
        break;
      }
      else
      {
        // if they are both this constructor, their selectors are equal
        Node tester1 = getTester(n[0], itd->second, ii);
        Node tester2 = getTester(n[1], itd->second, ii);
        Node cond = d_nm->mkNode(Kind::AND, tester1, tester2);
        cur = d_nm->mkNode(Kind::ITE, cond, eq, cur);
      }
    }
    return cur;
  }
  else if (k == Kind::ITE)
  {
    TypeNode tn = n.getType();
    if (d_dtep.find(tn) == d_dtep.end())
    {
      // non-datatype ite, skip
      return n;
    }
    // eliminate ITE by lifting
    Node kt = SkolemManager::mkPurifySkolem(n);
    Node iteLemma =
        d_nm->mkNode(Kind::ITE, n[0], kt.eqNode(n[1]), kt.eqNode(n[2]));
    d_newLemmas.push_back(iteLemma);
    return kt;
  }
  else if (k == Kind::APPLY_SELECTOR)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    if (d_dtep.find(tn) == d_dtep.end())
    {
      return n;
    }
    // We can only apply to variables and APPLY_UF. We first check if we
    // are an unrewritten correctly applied selector.
    Kind kt = t.getKind();
    if (kt == Kind::APPLY_CONSTRUCTOR)
    {
      Node nr = rewrite(n);
      if (nr != n)
      {
        return nr;
      }
    }
    if (!t.isVar() && t.getKind() != Kind::APPLY_UF)
    {
      // if we are not, we must purify??
    }
  }
  else if (k == Kind::FORALL)
  {
    // TODO: see if any variables need to be split??
    for (const Node& v : n[0])
    {
      TypeNode tn = v.getType();
      std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
      if (itd == d_dtep.end())
      {
        continue;
      }
    }
  }
  else if ((k != Kind::BOUND_VARIABLE && n.isVar()) || k == Kind::APPLY_UF)
  {
    TypeNode tn = n.getType();
    if (tn.isFunction())
    {
      // check if any argument is a datatype, if so we replace by a lambda
      std::vector<TypeNode> argTypes = tn.getArgTypes();
      for (const TypeNode& tna : argTypes)
      {
        std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tna);
        if (itd == d_dtep.end())
        {
          continue;
        }
        // otherwise we construct the appropriate lambda.
      }
    }
    std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
    if (itd == d_dtep.end())
    {
      return n;
    }
    // change the variable into constructors only??
  }
  return n;
}

Node DtElimConverter::getDtAbstraction(const Node& v)
{
  Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
  Assert(v.getKind() != Kind::BOUND_VARIABLE);
  TypeNode vtn = v.getType();
  Assert(vtn.isDatatype());
  const std::vector<Node>& cvec = getConstructorVec(vtn);
  const DType& dt = vtn.getDType();
  Assert(cvec.size() == dt.getNumConstructors());
  Node cur = cvec[0];
  for (size_t i = 1, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node tester = datatypes::utils::mkTester(v, i, dt);
    cur = d_nm->mkNode(Kind::ITE, tester, cvec[i], cur);
  }
  return cur;
}

Node DtElimConverter::getTesterFunctionInternal(const Node& v,
                                                DtElimPolicy policy)
{
  Assert(v.getKind() == Kind::APPLY_UF);
  Node op = v.getOperator();
  std::map<Node, Node>::iterator it = d_tester.find(op);
  if (it != d_tester.end())
  {
    return it->second;
  }
  std::vector<Node> lamArgs;
  for (const Node& vc : v)
  {
    lamArgs.push_back(d_nm->mkBoundVar(v.getType()));
  }
  Node lbvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, lamArgs);
  lamArgs.insert(lamArgs.begin(), v.getOperator());
  Node lbody = d_nm->mkNode(Kind::APPLY_UF, lamArgs);
  if (isBinaryTestPolicy(policy))
  {
    TypeNode vtn = v.getType();
    Assert(vtn.isDatatype());
    const DType& dt = vtn.getDType();
    lbody = datatypes::utils::mkTester(lbody, 0, dt);
  }
  else if (isAbstractPolicy(policy))
  {
    lbody = getDtAbstraction(lbody);
  }
  else
  {
    Unhandled() << "getTesterFunctionInternal: Unknown policy " << policy;
  }
  Node lam = d_nm->mkNode(Kind::LAMBDA, lbvl, lbody);
  return SkolemManager::mkPurifySkolem(lam);
}

Node DtElimConverter::getTesterInternal(const Node& v, DtElimPolicy policy)
{
  Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
  Assert(v.getKind() != Kind::BOUND_VARIABLE);
  std::map<Node, Node>::iterator it = d_tester.find(v);
  if (it != d_tester.end())
  {
    return it->second;
  }
  Node tester;
  if (v.getKind() == Kind::APPLY_UF)
  {
    std::vector<Node> ufArgs;
    ufArgs.push_back(getTesterFunctionInternal(v, policy));
    ufArgs.insert(ufArgs.end(), v.begin(), v.end());
    tester = d_nm->mkNode(Kind::APPLY_UF, ufArgs);
  }
  else
  {
    // The tester for v : (Option-Bool), call it v-is-some, is equivalent
    // to ((_ is some) v). Analoguously if abstract, we use
    // v-get-cons which is equivalent to (ite ((_ is some) v) U_some U_none).
    Assert(v.isVar() && v.getKind() != Kind::BOUND_VARIABLE);
    if (isBinaryTestPolicy(policy))
    {
      TypeNode vtn = v.getType();
      Assert(vtn.isDatatype());
      const DType& dt = vtn.getDType();
      Node tpred = datatypes::utils::mkTester(v, 0, dt);
      tester = SkolemManager::mkPurifySkolem(tpred);
    }
    else if (isAbstractPolicy(policy))
    {
      Node consKind = getDtAbstraction(v);
      tester = SkolemManager::mkPurifySkolem(consKind);
    }
    else
    {
      Unhandled() << "getTesterInternal: Unknown policy " << policy;
    }
  }
  Assert(!isBinaryTestPolicy(policy) || tester.getType().isBoolean());
  Assert(!isAbstractPolicy(policy)
         || tester.getType() == getTypeAbstraction(vtn));
  d_tester[v] = tester;
  return tester;
}

Node DtElimConverter::getTester(const Node& v, DtElimPolicy policy, size_t i)
{
  Node tester = getTesterInternal(v, policy);
  if (isBinaryTestPolicy(policy))
  {
    return i == 0 ? tester : tester.notNode();
  }
  else if (isAbstractPolicy(policy))
  {
    TypeNode vtn = v.getType();
    const std::vector<Node>& cvec = getConstructorVec(vtn);
    Assert(i < cvec.size());
    return tester.eqNode(cvec[i]);
  }
  else
  {
    Unhandled() << "getTester: Unknown policy " << policy;
  }
  return Node::null();
}

const std::vector<Node>& DtElimConverter::getSelectorVec(const Node& v,
                                                         size_t i)
{
  Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
  Assert(v.getKind() != Kind::BOUND_VARIABLE);
  std::map<Node, std::vector<Node>>::iterator it = d_selectors.find(v);
  if (it != d_selectors.end())
  {
    return it->second;
  }
  // TODO
}

TypeNode DtElimConverter::getTypeAbstraction(const TypeNode& dt)
{
  Assert(dt.isDatatype());
  return nodeManager()->mkSort(d_dtElimSc, {dt});
}

const std::vector<Node>& DtElimConverter::getConstructorVec(const TypeNode& tn)
{
  Assert(tn.isDatatype());
  std::map<TypeNode, std::vector<Node>>::iterator it = d_constructors.find(tn);
  if (it != d_constructors.end())
  {
    return it->second;
  }
  TypeNode u = getTypeAbstraction(tn);
  std::vector<Node>& cons = d_constructors[tn];
  const DType& dt = tn.getDType();
  SkolemManager* skm = d_nm->getSkolemManager();
  for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node id = d_nm->mkConstInt(Rational(i));
    Node k = skm->mkInternalSkolemFunction(
        InternalSkolemId::DT_ELIM_CONS_ABSTRACTION, u, {id});
    cons.push_back(k);
  }
  // distinctness is a lemma
  if (cons.size() > 1)
  {
    Node distinct = d_nm->mkNode(Kind::DISTINCT, cons);
    d_newLemmas.push_back(distinct);
  }
  return cons;
}

DtElim::DtElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "dt-elim")
{
}

Node DtElim::processInternal(const Node& n, std::unordered_set<TNode>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (n.hasOperator())
      {
        visit.push_back(n.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      TypeNode tn = n.getType();
      if (!d_processed.insert(tn).second)
      {
        continue;
      }
      if (tn.isDatatype())
      {
        d_candidateDt.push_back(tn);
      }
      else if (tn.getNumChildren() > 0)
      {
      }
    }
  } while (!visit.empty());
  return n;
}

PreprocessingPassResult DtElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_set<TNode> visited;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    const Node& a = (*assertionsToPreprocess)[i];
    processInternal(a, visited);
  }
  /*
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node ar = processInternal(a,visited);
    assertionsToPreprocess->replace(i, ar);
  }
  */
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
