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
 * Test for project issue #638
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("fmf-fun", "true");
  solver.setOption("produce-abducts", "true");
  solver.setOption("sygus-core-connective", "true");
  Sort s0 = solver.mkUninterpretedSort("_u0");
  Sort s1 = solver.mkSetSort(s0);
  Term t2 = solver.mkConst(s1, "_x6");
  Op o3 = solver.mkOp(SET_IS_SINGLETON);
  Term t4 = solver.mkTerm(o3, {t2});
  Sort s5 = t4.getSort();
  Term t6 = solver.getAbduct(t4);

  return 0;
}
