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
  TermManager tm;
  Solver slv(tm);
  slv.setOption("produce-interpols", "default");
  Sort s1 = slv.mkUninterpretedSort("_u0");
  DatatypeDecl _dt1 = slv.mkDatatypeDecl("_dt1", {});
  DatatypeConstructorDecl _cons16 = slv.mkDatatypeConstructorDecl("_cons16");
  _cons16.addSelector("_sel11", s1);
  _dt1.addConstructor(_cons16);
  std::vector<Sort> _s2 = slv.mkDatatypeSorts({_dt1});
  Sort s2 = _s2[0];
  DatatypeDecl _dt17 = slv.mkDatatypeDecl("_dt17", {});
  DatatypeConstructorDecl _cons23 = slv.mkDatatypeConstructorDecl("_cons23");
  _cons23.addSelector("_sel22", s2);
  _dt17.addConstructor(_cons23);
  std::vector<Sort> _s3 = slv.mkDatatypeSorts({_dt17});
  Sort s3 = _s3[0];
  Term t3 = slv.mkConst(s2, "_x41");
  Term t30 = slv.mkConst(s3, "_x68");
  Term t600;
  {
    DatatypeSelector sel =
        t30.getSort().getDatatype().getConstructor("_cons23").getSelector(
            "_sel22");
    t600 = slv.mkTerm(Kind::APPLY_UPDATER, {sel.getUpdaterTerm(), t30, t3});
  }
  Term t601 = slv.mkTerm(Kind::EQUAL, {t600, t30});
  slv.assertFormula({t601});
  {
    Term ipol = slv.getInterpolant(t601);
    if (slv.getOption("incremental") == "true")
    {
      while (!ipol.isNull())
      {
        ipol = slv.getInterpolantNext();
      }
    }
  }
  return 0;
}
