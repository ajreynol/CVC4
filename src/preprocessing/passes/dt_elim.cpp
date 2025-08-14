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

#include "expr/node_algorithm.h"
#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

class DtElimConverter : protected EnvObj, public NodeConverter
{
 public:
  DtElimConverter(Env& env, const std::vector<Node>& assertions)
      : EnvObj(env), NodeConverter(nodeManager())
  {
    computePolicies(assertions);
    d_dtElimSc = nodeManager()->mkSortConstructor("@dt-elim-sort", 1);
  }
  ~DtElimConverter() {}
  /**
   * Compute the policies for each datatype
   */
  void computePolicies(const std::vector<Node>& assertions)
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
      // check for recursion
      for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
      {
      }
    }
  }
  /**
   */
  Node postConvert(Node n) override
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
      // eliminate the equality
      switch (itd->second)
      {
        case DtElimPolicy::UNIT:
        case DtElimPolicy::ONE_INLINE: return d_nm->mkConst(true);
        case DtElimPolicy::BINARY_TEST:
        case DtElimPolicy::BINARY_TEST_SPLIT:
        {
          std::vector<Node> conds;
          std::vector<Node> branches;
          for (size_t i = 0; i < 2; i++)
          {
          }
        }
        break;
        case DtElimPolicy::ABSTRACT: break;
        case DtElimPolicy::ABSTRACT_SPLIT:
        default: break;
      }
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
        // if we are not, we must purify
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
      // change the variable into constructors only
    }
    return n;
  }

 private:
  Node getBinaryTesterPredicate(const Node& v, const DType& dt)
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
    lbody = datatypes::utils::mkTester(lbody, 0, dt);
    Node lam = d_nm->mkNode(Kind::LAMBDA, lbvl, lbody);
    return SkolemManager::mkPurifySkolem(lam);
  }
  Node getBinaryTester(const Node& v)
  {
    Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
    Assert(v.getKind() != Kind::BOUND_VARIABLE);
    std::map<Node, Node>::iterator it = d_tester.find(v);
    if (it != d_tester.end())
    {
      return it->second;
    }
    std::vector<Node> args;
    TypeNode vtn = v.getType();
    Assert(vtn.isDType());
    const DType& dt = vtn.getDType();
    Node tester;
    if (v.getKind() == Kind::APPLY_UF)
    {
      // if an apply UF, we get the predicate that is true when the function
      // f is that tester. For instance, for f : Int -> (Option Bool), we
      // introduce a predicate f-is-some : Int -> Bool that is equivalent to
      // (lambda ((x Int)) ((_ is some) (f x))). The tester for (f a) is
      // (f-is-some a).
      std::vector<Node> ufArgs;
      ufArgs.push_back(getBinaryTesterPredicate(v, dt));
      ufArgs.insert(ufArgs.end(), v.begin(), v.end());
      tester = d_nm->mkNode(Kind::APPLY_UF, ufArgs);
    }
    else
    {
      // The tester for v : (Option-Bool), call it v-is-some, is equivalent
      // to ((_ is some) v).
      Assert(v.isVar() && v.getKind() != Kind::BOUND_VARIABLE);
      Node tpred = datatypes::utils::mkTester(v, 0, dt);
      tester = SkolemManager::mkPurifySkolem(tpred);
    }
    d_tester[v] = tester;
    return tester;
  }
  Node getAbstractConsKind(const Node& v)
  {
    Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
    Assert(v.getKind() != Kind::BOUND_VARIABLE);
    std::map<Node, Node>::iterator it = d_tester.find(v);
    if (it != d_tester.end())
    {
      return it->second;
    }
    TypeNode tn = v.getType();
    TypeNode u = getTypeAbstraction(tn);
    return Node::null();
  }
  const std::vector<Node>& getSelectorVec(const Node& v, size_t i)
  {
    Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
    Assert(v.getKind() != Kind::BOUND_VARIABLE);
    std::map<Node, std::vector<Node>>::iterator it = d_selectors.find(v);
    if (it != d_selectors.end())
    {
      return it->second;
    }
  }
  TypeNode getTypeAbstraction(const TypeNode& dt)
  {
    Assert(dt.isDatatype());
    return nodeManager()->mkSort(d_dtElimSc, {dt});
  }
  const std::vector<Node>& getConstructorVec(const TypeNode& tn)
  {
    Assert(tn.isDatatype());
    std::map<TypeNode, std::vector<Node>>::iterator it =
        d_constructors.find(tn);
    if (it != d_constructors.end())
    {
      return it->second;
    }
    TypeNode u = getTypeAbstraction(tn);
    std::vector<Node>& cons = d_constructors[tn];
    const DType& dt = tn.getDType();
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      // Node g =
      // Node ticons = utils::getInstCons(t, dt, i, shareSel);
    }
    return cons;
  }
  /** The new lemmas */
  std::vector<Node> d_newLemmas;
  /** The policy */
  std::map<TypeNode, DtElimPolicy> d_dtep;
  /** Used for getBinaryTester and getAbstractConsKind */
  std::map<Node, Node> d_tester;
  /** */
  std::map<Node, std::vector<Node>> d_selectors;
  /** */
  std::map<TypeNode, std::vector<Node>> d_constructors;
  /** */
  TypeNode d_dtElimSc;
};

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
