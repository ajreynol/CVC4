/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #640
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("sets-infer-as-lemmas", "false");
  Sort s0 = solver.getBooleanSort();
  Sort s1 = solver.mkBagSort(s0);
  Sort s2 = solver.mkSetSort(s1);
  Term t3 = solver.mkConst(s1, "_x0");
  Term t4 = solver.mkConst(s1, "_x3");
  Term t5 = solver.mkEmptySet(s2);
  Term t6 = solver.mkTerm(SET_INSERT, {t4, t3, t5});
  Op o7 = solver.mkOp(SET_CHOOSE);
  Term t8 = solver.mkTerm(o7, {t6});
  Op o9 = solver.mkOp(SET_INSERT);
  Term t10 = solver.mkTerm(o9, {t8, t6});
  Op o11 = solver.mkOp(SET_IS_SINGLETON);
  Term t12 = solver.mkTerm(o11, {t6});
  Term t13 = solver.mkTerm(ITE, {t12, t10, t5});
  Op o14 = solver.mkOp(SET_CHOOSE);
  Term t15 = solver.mkTerm(o7, {t13});
  Term t16 = solver.mkTerm(BAG_UNION_DISJOINT, {t3, t3});
  Op o17 = solver.mkOp(DISTINCT);
  Term t18 = solver.mkTerm(o17, {t16, t3});
  Term t19 = solver.mkTerm(BAG_DIFFERENCE_REMOVE, {t15, t3});
  Op o20 = solver.mkOp(BAG_SUBBAG);
  Term t21 = solver.mkTerm(o20, {t19, t3});
  Term t22 = t21.andTerm(t12);
  Op o23 = solver.mkOp(OR);
  Term t24 = solver.mkTerm(o23, {t22, t18});
  solver.assertFormula(t24);
  solver.checkSat();

  return 0;
}
