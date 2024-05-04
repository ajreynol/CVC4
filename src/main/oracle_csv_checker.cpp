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
 * Lemma loader for cvc5.
 */

#include "main/oracle_csv_checker.h"

namespace cvc5 {
namespace main {

OracleCsvChecker::OracleCsvChecker(TermManager& tm,
            std::string& filename,
            Solver* s,
            parser::SymbolManager* sm);

OracleCsvChecker::~OracleCsvChecker()
{
}

std::vector<Sort> OracleCsvChecker::getArgTypes() const
{
  std::vector<Sort> sorts;
  for (const Term& t :d_vars)
  {
    sorts.push_back(t.getSort());
  }
  return sorts;
}

}  // namespace main
}  // namespace cvc5

