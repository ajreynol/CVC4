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
 * Test for project issue #635
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("sygus-fair", "dt-height-bound");
  solver.setOption("produce-abducts", "true");
  solver.setOption("produce-unsat-cores", "true");
  Sort s0 = solver.mkUninterpretedSort("_u0");
  Sort s1 = solver.getBooleanSort();
  Sort s2 = solver.mkArraySort(s1, s1);
  Term t3 = solver.mkConst(s2, "_x7");
  Term t4 = solver.mkConst(s1, "_x32");
  Sort s5 = solver.mkBagSort(s0);
  Term t6 = solver.mkConst(s5, "_x37");
  Term t7 = solver.mkConst(s5, "_x38");
  Op o8 = solver.mkOp(BAG_SUBBAG);
  Term t9 = solver.mkTerm(o8, {t6, t7});
  Op o10 = solver.mkOp(SELECT);
  Term t11 = solver.mkTerm(o10, {t3, t9});
  Term t12 = solver.mkTerm(XOR, {t4, t11});
  Term t13 = solver.getAbduct(t12);

  return 0;
}
