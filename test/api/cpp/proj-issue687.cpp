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
 * Test for project issue #687
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("fmf-bound", "true");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getIntegerSort();
  Term t1 = solver.mkVar(s0, "_x0");
  Sort s2 = solver.getBooleanSort();
  Sort s3 = solver.mkSequenceSort(s2);
  Sort s4 = solver.getRoundingModeSort();
  Sort s5 = solver.getRealSort();
  DatatypeDecl d6 = solver.mkDatatypeDecl("_dt1");
  DatatypeConstructorDecl dtcd7 = solver.mkDatatypeConstructorDecl("_cons3");
  dtcd7.addSelector("_sel2", s2);
  d6.addConstructor(dtcd7);
  DatatypeConstructorDecl dtcd8 = solver.mkDatatypeConstructorDecl("_cons4");
  d6.addConstructor(dtcd8);
  DatatypeConstructorDecl dtcd9 = solver.mkDatatypeConstructorDecl("_cons5");
  d6.addConstructor(dtcd9);
  DatatypeConstructorDecl dtcd10 = solver.mkDatatypeConstructorDecl("_cons11");
  dtcd10.addSelector("_sel6", s2);
  dtcd10.addSelectorSelf("_sel7");
  dtcd10.addSelector("_sel8", s5);
  dtcd10.addSelector("_sel9", s2);
  dtcd10.addSelector("_sel10", s5);
  d6.addConstructor(dtcd10);
  DatatypeConstructorDecl dtcd11 = solver.mkDatatypeConstructorDecl("_cons15");
  dtcd11.addSelector("_sel12", s5);
  dtcd11.addSelector("_sel13", s5);
  dtcd11.addSelector("_sel14", s4);
  d6.addConstructor(dtcd11);
  Sort s12 =
      solver.declareDatatype("_dt1", {dtcd7, dtcd8, dtcd9, dtcd10, dtcd11});
  Sort s13 = solver.mkBitVectorSort(16);
  Term t14 = solver.mkVar(s12, "_x16");
  Term t15 = solver.mkInteger(27023324836);
  Term t16 = solver.mkConst(s3, "_x17");
  Term t17 = solver.mkInteger("382074608426676787007732890635877183371177");
  Term t18 = solver.mkVar(s13, "_x18");
  Term t19 = solver.mkTerm(Kind::SEQ_EXTRACT, {t16, t17, t15});
  Term t20 = solver.mkTerm(Kind::INTS_MODULUS, {t15, t1});
  Op o21 = solver.mkOp(Kind::SEQ_UPDATE);
  Term t22 = solver.mkTerm(o21, {t19, t20, t16});
  Op o23 = solver.mkOp(Kind::SEQ_SUFFIX);
  Term t24 = solver.mkTerm(o23, {t22, t16});
  Op o25 = solver.mkOp(Kind::VARIABLE_LIST);
  Term t26 = solver.mkTerm(o25, {t18, t14, t1});
  Sort s27 = t26.getSort();
  Term t28 = solver.mkTerm(Kind::FORALL, {t26, t24});
  Term t29 = solver.getAbduct(t28);

  return 0;
}
