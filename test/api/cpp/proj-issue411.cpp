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
  slv.setLogic("UFBVFP");
  slv.setOption("produce-interpolants", "true");
  slv.setOption("incremental", "false");
  Sort s4 = slv.mkBitVectorSort(39);
  Term t3 = slv.mkVar(s4, "_x2");
  Term t26;
  {
    uint32_t bw = s4.getBitVectorSize();
    t26 = slv.mkBitVector(bw, std::string(bw, '1'), 2);
  }
  Term t38 = slv.mkConst(s4, "_x24");
  Term t60 = slv.mkTerm(Kind::BITVECTOR_UREM, {t3, t26});
  Term t63 = slv.mkTerm(Kind::BITVECTOR_REDOR, {t60});
  Term t64 = slv.mkTerm(Kind::BITVECTOR_UGT, {t26, t38});
  Term t66 = slv.mkTerm(Kind::EQUAL, {t64, t63});
  slv.assertFormula({t64});
  {
    Term ipol = slv.getInterpolant(t66);
    if (slv.getOption("incremental") == "true")
    {
      if (!ipol.isNull())
      {
        ipol = slv.getInterpolantNext();
      }
    }
  }

  return 0;
}
