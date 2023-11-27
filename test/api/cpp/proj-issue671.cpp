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
 * Test for project issue #671
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("incremental", "false");
solver.setOption("inst-max-level", "6067390630711104712");
solver.setOption("produce-abducts", "true");
Sort s0 = solver.getStringSort();
Term t1 = solver.mkConst(s0, "_x0");
Term t2 = solver.mkConst(s0, "_x4");
Term t3 = solver.mkString("");
Term t4 = solver.mkConst(s0, "_x8");
Term t5 = solver.mkConst(s0, "_x9");
Op o6 = solver.mkOp(Kind::STRING_REV);
Term t7 = solver.mkTerm(o6, {t4});
Op o8 = solver.mkOp(Kind::EQUAL);
Term t9 = solver.mkTerm(o8, {t7, t2});
Sort s10 = t9.getSort();
Term t11 = solver.mkTerm(Kind::STRING_LEQ, {t1, t4});
Term t12 = solver.mkTerm(Kind::STRING_LT, {t3, t5});
Term t13 = solver.mkTerm(Kind::ITE, {t11, t9, t9});
solver.assertFormula(t13);
Term t14 = solver.getAbduct(t12);

return 0;
}
