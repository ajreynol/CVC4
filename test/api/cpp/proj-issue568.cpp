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
 * Test for project issue #568
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("incremental", "false");
solver.setOption("produce-interpolants", "true");
Sort s0 = solver.getIntegerSort();
Sort s1 = solver.mkSetSort(s0);
Term t2 = solver.mkVar(s1, "_x0");
Term t3 = solver.mkInteger("7152634386661932017026672113134541687");
Term t4 = solver.mkPi();
Sort s5 = t4.getSort();
Term t6 = solver.mkTerm(Kind::SET_SINGLETON, {t3});
Term t7 = solver.mkTerm(Kind::SET_MINUS, {t6, t2});
Term t8 = solver.mkTerm(Kind::TO_INTEGER, {t4});
Op o9 = solver.mkOp(Kind::SET_CHOOSE);
Term t10 = solver.mkTerm(o9, {t7});
Term t11 = solver.mkTerm(Kind::DISTINCT, {t8, t10});
Sort s12 = t11.getSort();
Op o13 = solver.mkOp(Kind::VARIABLE_LIST);
Term t14 = solver.mkTerm(o13, {t2});
Sort s15 = t14.getSort();
Op o16 = solver.mkOp(Kind::EXISTS);
Term t17 = solver.mkTerm(o16, {t14, t11});
Term t18 = solver.getInterpolant(t17);

return 0;
}
