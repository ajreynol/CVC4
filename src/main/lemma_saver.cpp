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
 * Lemma saver for cvc5.
 */

#include "main/lemma_saver.h"

#include "base/check.h"
#include "base/output.h"

namespace cvc5 {
namespace main {

LemmaSaver::LemmaSaver(TermManager& tm, std::string& filename, Solver* s)
    : Plugin(tm), d_filename(filename), d_solver(s)
{
  d_fs.open(filename, std::fstream::out);
}
LemmaSaver::~LemmaSaver() { d_fs.close(); }

void LemmaSaver::notifySatClause(const Term& t)
{
  Trace("lemma-saver") << "LemmaSaver::notifySatClause " << t << std::endl;
  d_fs << t.toString() << " ; SAT" << std::endl;
}

void LemmaSaver::notifyTheoryLemma(const Term& t)
{
  Trace("lemma-saver") << "LemmaSaver::notifyTheoryLemma " << t << std::endl;
  d_fs << t.toString() << std::endl;
}

std::string LemmaSaver::getName() { return "LemmaSaver"; }

std::string LemmaSaver::getFileName() { return d_filename; }

}  // namespace main
}  // namespace cvc5
