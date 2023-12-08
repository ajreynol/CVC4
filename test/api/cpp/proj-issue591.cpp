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
 * Test for project issue #590
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("macros-quant-mode", "all");
  solver.setOption("produce-unsat-cores", "true");
  solver.setOption("sort-inference", "true");
  solver.setOption("produce-unsat-assumptions", "true");
  solver.setOption("stats-every-query", "true");
  solver.setOption("sygus-inv-templ", "post");
  solver.setOption("sets-proxy-lemmas", "true");
  solver.setOption("produce-interpolants", "true");
  solver.setOption("ho-merge-term-db", "false");
  solver.setOption("sygus-rec-fun", "false");
  solver.setOption("strings-exp", "true");
  solver.setOption("sygus-inv-templ-when-sg", "true");
  solver.setOption("portfolio-jobs", "6058199933344443617");
  solver.setOption("check-synth-sol", "false");
  solver.setOption("nl-ext-factor", "true");
  solver.setOption("uf-ss-fair", "true");
  solver.setOption("dt-blast-splits", "true");
  Sort s0 = solver.getBooleanSort();
  Term t1 = solver.mkConst(s0, "_x0");
  Term t2 = solver.mkFalse();
  Term t3 = solver.mkConst(s0, "_x1");
  Op o4 = solver.mkOp(EQUAL);
  Term t5 = solver.mkTerm(o4, {t3, t2});
  Op o6 = solver.mkOp(NOT);
  Term t7 = solver.mkTerm(o6, {t5});
  Term t8 = solver.mkTerm(AND, {t7, t3});
  Op o9 = solver.mkOp(DISTINCT);
  Term t10 = solver.mkTerm(o9, {t8, t8});
  solver.assertFormula(t5);
  solver.assertFormula(t5);
  solver.assertFormula(t5);
  solver.assertFormula(t10);
  solver.checkSat();
  Term t11 = solver.getInterpolant(t8);

  return 0;
}
