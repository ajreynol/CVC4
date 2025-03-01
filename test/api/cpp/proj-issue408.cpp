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
  slv.setOption("produce-interpolants", "true");
  Sort s2 = tm.mkBitVectorSort(20);
  Term t2 = tm.mkConst(s2, "_x1");
  Term t54 = tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {23}), {t2});
  Term t281 = tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {45}), {t54});
  {
    Term ipol = slv.getInterpolant(t281);
  }
  return 0;
}
