/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/arith/arith_ite_utils.h"

#include <ostream>

#include "base/output.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "preprocessing/util/ite_utilities.h"
#include "smt/env.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_model.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith {

Node ArithIteUtils::applyReduceVariablesInItes(Node n){
  NodeBuilder nb(nodeManager(), n.getKind());
  if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    nb << (n.getOperator());
  }
  for(Node::iterator it = n.begin(), end = n.end(); it != end; ++it){
    nb << reduceVariablesInItes(*it);
  }
  Node res = nb;
  return res;
}

Node ArithIteUtils::reduceVariablesInItes(Node n){
  using namespace cvc5::internal::kind;
  if(d_reduceVar.find(n) != d_reduceVar.end()){
    Node res = d_reduceVar[n];
    return res.isNull() ? n : res;
  }

  switch(n.getKind()){
    case Kind::ITE:
    {
      Node c = n[0], t = n[1], e = n[2];
      TypeNode tn = n.getType();
      if (tn.isRealOrInt())
      {
        Node rc = reduceVariablesInItes(c);
        Node rt = reduceVariablesInItes(t);
        Node re = reduceVariablesInItes(e);

        Node vt = d_varParts[t];
        Node ve = d_varParts[e];
        Node vpite = (vt == ve) ? vt : Node::null();

        NodeManager* nm = nodeManager();
        if (vpite.isNull())
        {
          Node rite = rc.iteNode(rt, re);
          // do not apply
          d_reduceVar[n] = rite;
          d_constants[n] = nm->mkConstRealOrInt(tn, Rational(0));
          d_varParts[n] = rite;  // treat the ite as a variable
          return rite;
        }
        else
        {
          Node constantite = rc.iteNode(d_constants[t], d_constants[e]);
          Node sum = nm->mkNode(Kind::ADD, vpite, constantite);
          d_reduceVar[n] = sum;
          d_constants[n] = constantite;
          d_varParts[n] = vpite;
          return sum;
        }
      }
      else
      {  // non-arith ite
        if (!d_contains.containsTermITE(n))
        {
          // don't bother adding to d_reduceVar
          return n;
        }
        else
        {
          Node newIte = applyReduceVariablesInItes(n);
          d_reduceVar[n] = (n == newIte) ? Node::null() : newIte;
          return newIte;
        }
      }
    }
    break;
    default:
    {
      TypeNode tn = n.getType();
      if (tn.isRealOrInt() && linear::Polynomial::isMember(n))
      {
        Node newn = Node::null();
        if (!d_contains.containsTermITE(n))
        {
          newn = n;
        }
        else if (n.getNumChildren() > 0)
        {
          newn = applyReduceVariablesInItes(n);
          newn = rewrite(newn);
          Assert(linear::Polynomial::isMember(newn));
        }
        else
        {
          newn = n;
        }
        NodeManager* nm = nodeManager();
        linear::Polynomial p = linear::Polynomial::parsePolynomial(newn);
        if (p.isConstant())
        {
          d_constants[n] = newn;
          d_varParts[n] = nm->mkConstRealOrInt(tn, Rational(0));
          // don't bother adding to d_reduceVar
          return newn;
        }
        else if (!p.containsConstant())
        {
          d_constants[n] = nm->mkConstRealOrInt(tn, Rational(0));
          d_varParts[n] = newn;
          d_reduceVar[n] = p.getNode();
          return p.getNode();
        }
        else
        {
          linear::Monomial mc = p.getHead();
          d_constants[n] = mc.getConstant().getNode();
          d_varParts[n] = p.getTail().getNode();
          d_reduceVar[n] = newn;
          return newn;
        }
      }
      else
      {
        if (!d_contains.containsTermITE(n))
        {
          return n;
        }
        if (n.getNumChildren() > 0)
        {
          Node res = applyReduceVariablesInItes(n);
          d_reduceVar[n] = res;
          return res;
        }
        else
        {
          return n;
        }
      }
  }
    break;
  }
  Unreachable();
}

ArithIteUtils::ArithIteUtils(
    Env& env,
    preprocessing::util::ContainsTermITEVisitor& contains,
    SubstitutionMap& subs)
    : EnvObj(env),
      d_contains(contains),
      d_subs(subs),
      d_one(1),
      d_subcount(userContext(), 0),
      d_skolems(userContext()),
      d_implies(),
      d_orBinEqs()
{
}

ArithIteUtils::~ArithIteUtils(){
}

void ArithIteUtils::clear(){
  d_reduceVar.clear();
  d_constants.clear();
  d_varParts.clear();
}

const Integer& ArithIteUtils::gcdIte(Node n){
  if(d_gcds.find(n) != d_gcds.end()){
    return d_gcds[n];
  }
  if (n.isConst())
  {
    const Rational& q = n.getConst<Rational>();
    if(q.isIntegral()){
      d_gcds[n] = q.getNumerator();
      return d_gcds[n];
    }else{
      return d_one;
    }
  }
  else if (n.getKind() == Kind::ITE && n.getType().isRealOrInt())
  {
    const Integer& tgcd = gcdIte(n[1]);
    if(tgcd.isOne()){
      d_gcds[n] = d_one;
      return d_one;
    }else{
      const Integer& egcd = gcdIte(n[2]);
      Integer ite_gcd = tgcd.gcd(egcd);
      d_gcds[n] = ite_gcd;
      return d_gcds[n];
    }
  }
  return d_one;
}

Node ArithIteUtils::reduceIteConstantIteByGCD_rec(Node n, const Rational& q){
  if(n.isConst()){
    Assert(n.getType().isRealOrInt());
    return nodeManager()->mkConstRealOrInt(n.getType(),
                                           n.getConst<Rational>() * q);
  }else{
    Assert(n.getKind() == Kind::ITE);
    Assert(n.getType().isInteger());
    Node rc = reduceConstantIteByGCD(n[0]);
    Node rt = reduceIteConstantIteByGCD_rec(n[1], q);
    Node re = reduceIteConstantIteByGCD_rec(n[2], q);
    return rc.iteNode(rt, re);
  }
}

Node ArithIteUtils::reduceIteConstantIteByGCD(Node n){
  Assert(n.getKind() == Kind::ITE);
  Assert(n.getType().isRealOrInt());
  const Integer& gcd = gcdIte(n);
  NodeManager* nm = nodeManager();
  if(gcd.isOne()){
    Node newIte = reduceConstantIteByGCD(n[0]).iteNode(n[1],n[2]);
    d_reduceGcd[n] = newIte;
    return newIte;
  }else if(gcd.isZero()){
    Node zeroNode = nm->mkConstRealOrInt(n.getType(), Rational(0));
    d_reduceGcd[n] = zeroNode;
    return zeroNode;
  }else{
    Rational divBy(Integer(1), gcd);
    Node redite = reduceIteConstantIteByGCD_rec(n, divBy);
    Node gcdNode = nm->mkConstRealOrInt(n.getType(), Rational(gcd));
    Node multIte = nm->mkNode(Kind::MULT, gcdNode, redite);
    d_reduceGcd[n] = multIte;
    return multIte;
  }
}

Node ArithIteUtils::reduceConstantIteByGCD(Node n){
  if(d_reduceGcd.find(n) != d_reduceGcd.end()){
    return d_reduceGcd[n];
  }
  if (n.getKind() == Kind::ITE && n.getType().isRealOrInt())
  {
    return reduceIteConstantIteByGCD(n);
  }

  if(n.getNumChildren() > 0){
    NodeBuilder nb(nodeManager(), n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      nb << (n.getOperator());
    }
    bool anychange = false;
    for(Node::iterator it = n.begin(), end = n.end(); it != end; ++it){
      Node child = *it;
      Node redchild = reduceConstantIteByGCD(child);
      anychange = anychange || (child != redchild);
      nb << redchild;
    }
    if(anychange){
      Node res = nb;
      d_reduceGcd[n] = res;
      return res;
    }else{
      d_reduceGcd[n] = n;
      return n;
    }
  }else{
    return n;
  }
}

unsigned ArithIteUtils::getSubCount() const{
  return d_subcount;
}

void ArithIteUtils::addSubstitution(TNode f, TNode t){
  Trace("arith::ite") << "adding " << f << " -> " << t << endl;
  d_subcount = d_subcount + 1;
  d_subs.addSubstitution(f, t);
}

Node ArithIteUtils::applySubstitutions(TNode f){
  AlwaysAssert(!options().base.incrementalSolving);
  return d_subs.apply(f);
}

Node ArithIteUtils::selectForCmp(Node n) const{
  if (n.getKind() == Kind::ITE)
  {
    if(d_skolems.find(n[0]) != d_skolems.end()){
      return selectForCmp(n[1]);
    }
  }
  return n;
}

void ArithIteUtils::learnSubstitutions(const std::vector<Node>& assertions){
  AlwaysAssert(!options().base.incrementalSolving);
  for(size_t i=0, N=assertions.size(); i < N; ++i){
    collectAssertions(assertions[i]);
  }
  bool solvedSomething;
  do{
    solvedSomething = false;
    size_t readPos = 0, writePos = 0, N = d_orBinEqs.size();
    for(; readPos < N; readPos++){
      Node curr = d_orBinEqs[readPos];
      bool solved = solveBinOr(curr);
      if(solved){
        solvedSomething = true;
      }else{
        // didn't solve, push back
        d_orBinEqs[writePos] = curr;
        writePos++;
      }
    }
    Assert(writePos <= N);
    d_orBinEqs.resize(writePos);
  }while(solvedSomething);

  d_implies.clear();
  d_orBinEqs.clear();
}

void ArithIteUtils::addImplications(Node x, Node y){
  // (or x y)
  // (=> (not x) y)
  // (=> (not y) x)

  Node xneg = x.negate();
  Node yneg = y.negate();
  d_implies[xneg].insert(y);
  d_implies[yneg].insert(x);
}

void ArithIteUtils::collectAssertions(TNode assertion){
  if (assertion.getKind() == Kind::OR)
  {
    if(assertion.getNumChildren() == 2){
      TNode left = assertion[0], right = assertion[1];
      addImplications(left, right);
      if (left.getKind() == Kind::EQUAL && right.getKind() == Kind::EQUAL)
      {
        if(left[0].getType().isInteger() && right[0].getType().isInteger()){
          d_orBinEqs.push_back(assertion);
        }
      }
    }
  }
  else if (assertion.getKind() == Kind::AND)
  {
    for(unsigned i=0, N=assertion.getNumChildren(); i < N; ++i){
      collectAssertions(assertion[i]);
    }
  }
}

Node ArithIteUtils::findIteCnd(TNode tb, TNode fb) const{
  Node negtb = tb.negate();
  Node negfb = fb.negate();
  ImpMap::const_iterator ti = d_implies.find(negtb);
  ImpMap::const_iterator fi = d_implies.find(negfb);

  if(ti != d_implies.end() && fi != d_implies.end()){
    const std::set<Node>& negtimp = ti->second;
    const std::set<Node>& negfimp = fi->second;

    // (or (not x) y)
    // (or x z)
    // (or y z)
    // ---
    // (ite x y z) return x
    // ---
    // (not y) => (not x)
    // (not z) => x
    std::set<Node>::const_iterator ci = negtimp.begin(), cend = negtimp.end();
    for (; ci != cend; ++ci)
    {
      Node impliedByNotTB = *ci;
      Node impliedByNotTBNeg = impliedByNotTB.negate();
      if(negfimp.find(impliedByNotTBNeg) != negfimp.end()){
        return impliedByNotTBNeg; // implies tb
      }
    }
  }

  return Node::null();
}

bool ArithIteUtils::solveBinOr(TNode binor){
  Assert(binor.getKind() == Kind::OR);
  Assert(binor.getNumChildren() == 2);
  Assert(binor[0].getKind() == Kind::EQUAL);
  Assert(binor[1].getKind() == Kind::EQUAL);

  //Node n = 
  Node n = applySubstitutions(binor);
  if(n != binor){
    n = rewrite(n);

    if (!(n.getKind() == Kind::OR && n.getNumChildren() == 2
          && n[0].getKind() == Kind::EQUAL && n[1].getKind() == Kind::EQUAL))
    {
      return false;
    }
  }

  Assert(n.getKind() == Kind::OR);
  Assert(n.getNumChildren() == 2);
  TNode l = n[0];
  TNode r = n[1];

  Assert(l.getKind() == Kind::EQUAL);
  Assert(r.getKind() == Kind::EQUAL);

  Trace("arith::ite") << "bin or " << n << endl;

  bool lArithEq = l.getKind() == Kind::EQUAL && l[0].getType().isInteger();
  bool rArithEq = r.getKind() == Kind::EQUAL && r[0].getType().isInteger();

  if(lArithEq && rArithEq){
    TNode sel = Node::null();
    TNode otherL = Node::null();
    TNode otherR = Node::null();
    if(l[0] == r[0]) {
      sel = l[0]; otherL = l[1]; otherR = r[1];
    }else if(l[0] == r[1]){
      sel = l[0]; otherL = l[1]; otherR = r[0];
    }else if(l[1] == r[0]){
      sel = l[1]; otherL = l[0]; otherR = r[1];
    }else if(l[1] == r[1]){
      sel = l[1]; otherL = l[0]; otherR = r[0];
    }
    Trace("arith::ite") << "selected " << sel << endl;
    if (sel.isVar() && sel.getKind() != Kind::SKOLEM)
    {
      Trace("arith::ite") << "others l:" << otherL << " r " << otherR << endl;
      Node useForCmpL = selectForCmp(otherL);
      Node useForCmpR = selectForCmp(otherR);

      Assert(linear::Polynomial::isMember(sel));
      Assert(linear::Polynomial::isMember(useForCmpL));
      Assert(linear::Polynomial::isMember(useForCmpR));
      linear::Polynomial lside = linear::Polynomial::parsePolynomial( useForCmpL );
      linear::Polynomial rside = linear::Polynomial::parsePolynomial( useForCmpR );
      linear::Polynomial diff = lside-rside;

      Trace("arith::ite") << "diff: " << diff.getNode() << endl;
      if(diff.isConstant()){
        // a: (sel = otherL) or (sel = otherR), otherL-otherR = c

        NodeManager* nm = nodeManager();
        SkolemManager* sm = nm->getSkolemManager();

        Node cnd = findIteCnd(binor[0], binor[1]);

        Node eq = sel.eqNode(otherL);
        Node sk = sm->mkPurifySkolem(eq);
        Node ite = sk.iteNode(otherL, otherR);
        d_skolems.insert(sk, cnd);
        // Given (or (= x c) (= x d)), we replace x by (ite @purifyX c d),
        // where @purifyX is the purification skolem for (= x c), where c and
        // d are known to be distinct.
        addSubstitution(sel, ite);
        return true;
      }
    }
  }
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
