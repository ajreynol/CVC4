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
 * Test for project issue #419
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver slv;
  slv.setOption("produce-unsat-assumptions", "true");
  Sort s1 = slv.getRealSort();
  Sort s2 = slv.getRoundingModeSort();
  Sort _p4 = slv.mkParamSort("_p4");
  DatatypeDecl _dt1 = slv.mkDatatypeDecl("_dt1", {_p4});
  DatatypeConstructorDecl _cons20 = slv.mkDatatypeConstructorDecl("_cons20");
  _cons20.addSelector("_sel16", s1);
  _dt1.addConstructor(_cons20);
  DatatypeConstructorDecl _cons15 = slv.mkDatatypeConstructorDecl("_cons15");
  _cons15.addSelector("_sel10", _p4);
  _cons15.addSelectorSelf("_sel12");
  _dt1.addConstructor(_cons15);
  Sort s4 = slv.mkDatatypeSorts({_dt1})[0];
  Sort s7 = slv.mkBitVectorSort(1);
  Sort s16 = slv.getIntegerSort();
  Sort s21 = s4.instantiate({s7});
  Term t19 = slv.mkConst(s21, "_x61");
  Term t29 = slv.mkConst(s16, "_x69");
  Term t30 = slv.mkTerm(Kind::TO_REAL, {t29});
  Term t65;
  {
    DatatypeSelector sel =
        t19.getSort().getDatatype().getConstructor("_cons20").getSelector(
            "_sel16");
    t65 = slv.mkTerm(Kind::APPLY_UPDATER, {sel.getUpdaterTerm(), t19, t30});
  }
  Term t95 = slv.mkTerm(Kind::DT_SIZE, {t65});
  Term t246 = slv.mkTerm(Kind::GEQ, {t29, t95});
  slv.assertFormula({t246});
  slv.checkSat();

  return 0;
}
