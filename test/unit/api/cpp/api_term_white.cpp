/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the Term class.
 */

#include "expr/node_manager.h"
#include "test_api.h"
#include "theory/builtin/generic_op.h"

namespace cvc5::internal {

namespace test {

class TestApiWhiteTerm : public TestApi
{
};

TEST_F(TestApiWhiteTerm, getOp)
{
  Sort intsort = d_tm.getIntegerSort();
  Sort bvsort = d_tm.mkBitVectorSort(8);
  Sort arrsort = d_tm.mkArraySort(bvsort, intsort);
  Sort funsort = d_tm.mkFunctionSort({intsort}, bvsort);

  Term x = d_tm.mkConst(intsort, "x");
  Term a = d_tm.mkConst(arrsort, "a");
  Term b = d_tm.mkConst(bvsort, "b");

  Term ab = d_tm.mkTerm(cvc5::Kind::SELECT, {a, b});
  Op ext = d_tm.mkOp(cvc5::Kind::BITVECTOR_EXTRACT, {4, 0});
  Term extb = d_tm.mkTerm(ext, {b});

  ASSERT_EQ(ab.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::SELECT));
  // can compare directly to a Kind (will invoke Op constructor)
  ASSERT_EQ(ab.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::SELECT));

  Term f = d_tm.mkConst(funsort, "f");
  Term fx = d_tm.mkTerm(cvc5::Kind::APPLY_UF, {f, x});

  ASSERT_EQ(fx.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::APPLY_UF));
  // testing rebuild from op and children

  // Test Datatypes Ops
  Sort sort = d_tm.mkParamSort("T");
  DatatypeDecl listDecl = d_tm.mkDatatypeDecl("paramlist", {sort});
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  cons.addSelector("head", sort);
  cons.addSelectorSelf("tail");
  listDecl.addConstructor(cons);
  listDecl.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(listDecl);
  Sort intListSort =
      listSort.instantiate(std::vector<Sort>{d_tm.getIntegerSort()});
  Term c = d_tm.mkConst(intListSort, "c");
  Datatype list = listSort.getDatatype();
  // list datatype constructor and selector operator terms
  Term consOpTerm = list.getConstructor("cons").getTerm();
  Term nilOpTerm = list.getConstructor("nil").getTerm();
  Term headOpTerm = list["cons"].getSelector("head").getTerm();
  Term tailOpTerm = list["cons"].getSelector("tail").getTerm();

  Term nilTerm = d_tm.mkTerm(cvc5::Kind::APPLY_CONSTRUCTOR, {nilOpTerm});
  Term consTerm = d_tm.mkTerm(cvc5::Kind::APPLY_CONSTRUCTOR,
                              {consOpTerm, d_tm.mkInteger(0), nilTerm});
  Term headTerm =
      d_tm.mkTerm(cvc5::Kind::APPLY_SELECTOR, {headOpTerm, consTerm});
  Term tailTerm =
      d_tm.mkTerm(cvc5::Kind::APPLY_SELECTOR, {tailOpTerm, consTerm});

  ASSERT_EQ(nilTerm.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(consTerm.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::APPLY_CONSTRUCTOR));
  ASSERT_EQ(headTerm.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::APPLY_SELECTOR));
  ASSERT_EQ(tailTerm.getOp(),
            Op(d_solver->getTermManager().d_nm, cvc5::Kind::APPLY_SELECTOR));
}

TEST_F(TestApiWhiteTerm, applyIndexedSymbolic)
{
  NodeManager* nm = d_tm.d_nm.get();
  Term b = d_tm.mkConst(d_tm.mkBitVectorSort(8), "b");
  Term high = d_tm.mkInteger(4);
  Term low = d_tm.mkInteger(0);
  Node op = nm->mkConst(cvc5::internal::Kind::APPLY_INDEXED_SYMBOLIC_OP,
                        GenericOp(cvc5::internal::Kind::BITVECTOR_EXTRACT));
  Node concreteIndexed =
      nm->mkNode(op, high.getNode(), low.getNode(), b.getNode());
  Term concreteTerm(d_tm.d_nm, concreteIndexed);

  ASSERT_EQ(concreteTerm.getKind(), cvc5::Kind::BITVECTOR_EXTRACT);
  ASSERT_EQ(concreteTerm.getNumChildren(), 1);
  ASSERT_EQ(concreteTerm[0], b);
  std::vector<Term> children(concreteTerm.begin(), concreteTerm.end());
  ASSERT_EQ(children.size(), 1);
  ASSERT_EQ(children[0], b);
  ASSERT_TRUE(concreteTerm.hasOp());
  Op concreteOp = concreteTerm.getOp();
  ASSERT_EQ(concreteOp.getKind(), cvc5::Kind::BITVECTOR_EXTRACT);
  ASSERT_TRUE(concreteOp.isIndexed());
  ASSERT_EQ(concreteOp.getNumIndices(), 2);
  ASSERT_EQ(concreteOp[0], high);
  ASSERT_EQ(concreteOp[1], low);
  ASSERT_EQ(d_tm.mkTerm(concreteOp, children),
            d_tm.mkTerm(d_tm.mkOp(cvc5::Kind::BITVECTOR_EXTRACT, {4, 0}), {b}));

  Term i = d_tm.mkConst(d_tm.getIntegerSort(), "i");
  Node symbolicIndexed =
      nm->mkNode(op, i.getNode(), low.getNode(), b.getNode());
  Term symbolicTerm(d_tm.d_nm, symbolicIndexed);

  ASSERT_EQ(symbolicTerm.getKind(), cvc5::Kind::INTERNAL_KIND);
  ASSERT_FALSE(symbolicTerm.hasOp());
  ASSERT_THROW(symbolicTerm.getOp(), CVC5ApiException);
}
}  // namespace test
}  // namespace cvc5::internal
