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
 * Oracle CSV checker for cvc5.
 */

#include "main/oracle_csv_checker.h"

namespace cvc5 {
namespace main {

OracleCsvChecker::OracleCsvChecker(TermManager& tm,
                                   std::string& filename,
                                   Solver* s,
                                   parser::SymbolManager* sm)
{
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();
  // TODO: set up variables

  std::vector<Sort> argTypes = getArgTypes();
  Sort boolSort = tm.getBooleanSort();
  d_oracle = d_solver->declareOracleFun(
      "oracle.in_csv", argTypes, boolSort, [&](const std::vector<Term>& input) {
        return this->evaluate(input);
      });
}

OracleCsvChecker::~OracleCsvChecker() {}

Term OracleCsvChecker::getOracle() const { return d_oracle; }
Term OracleCsvChecker::evaluate(const std::vector<Term>& evaluate)
{
  // TODO
  return d_true;
}

std::vector<Sort> OracleCsvChecker::getArgTypes() const
{
  std::vector<Sort> sorts;
  for (const Term& t : d_vars)
  {
    sorts.push_back(t.getSort());
  }
  return sorts;
}

}  // namespace main
}  // namespace cvc5
