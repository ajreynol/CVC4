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
 * Test for project issue #658
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("incremental", "false");
solver.setOption("produce-interpolants", "true");
solver.setOption("sygus-unif-pi", "cond-enum-igain");
solver.setOption("miniscope-quant", "conj");
Sort s0 = solver.getBooleanSort();
Sort s1 = solver.mkBagSort(s0);
Sort s2 = solver.mkSetSort(s0);
Term t3 = solver.mkConst(s2, "_x6");
Term t4 = solver.mkConst(s2, "_x9");
Term t5 = solver.mkConst(s1, "_x14");
Term t6 = solver.mkTerm(Kind::SET_SUBSET, {t4, t3});
Op o7 = solver.mkOp(Kind::BAG_COUNT);
Term t8 = solver.mkTerm(o7, {t6, t5});
Sort s9 = t8.getSort();
Term t10 = solver.mkVar(s9, "_f19_0");
Term t11 = solver.mkVar(s9, "_f19_1");
Term t12 = solver.mkVar(s1, "_f19_2");
Term t13 = solver.mkVar(s0, "_f19_3");
Term t14 = solver.mkVar(s1, "_f19_4");
Sort s15 = solver.mkFunctionSort({s9, s9, s1, s0, s1}, s0);
Term t16 = solver.defineFun("_f19", {t10, t11, t12, t13, t14}, s0, t6, true);
Term t17 = solver.getInterpolant(t6);

return 0;
}
