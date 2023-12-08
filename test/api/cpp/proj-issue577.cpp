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
 * Test for project issue #577
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getBooleanSort();
  Sort s1 = solver.mkBagSort(s0);
  Term t2 = solver.mkConst(s1, "_x2");
  Op o3 = solver.mkOp(BAG_CARD);
  Term t4 = solver.mkTerm(o3, {t2});
  Sort s5 = t4.getSort();
  Op o6 = solver.mkOp(DIVISIBLE, "3341361203");
  Term t7 = solver.mkTerm(o6, {t4});
  Term t8 = solver.getAbduct(t7);

  return 0;
}
