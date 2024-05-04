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

#include <cvc5/cvc5_parser.h>
#include <cvc5/cvc5_types.h>

#include "base/check.h"
#include "base/output.h"
#include "parser/sym_manager.h"

namespace cvc5 {
namespace main {

OracleCsvChecker::OracleCsvChecker(TermManager& tm,
                                   std::string& filename,
                                   Solver* s,
                                   parser::SymbolManager* sm)
    : d_filename(filename), d_tm(tm), d_solver(s), d_symman(sm)
{
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();

  initialize();
}

OracleCsvChecker::~OracleCsvChecker() {}

void OracleCsvChecker::initialize()
{
  // set up variables
  parser::InputParser ip(d_solver, d_symman);
  ip.setFileInput(modes::InputLanguage::SMT_LIB_2_6, d_filename);

  Term t;
  do
  {
    t = ip.nextTerm();
    if (t.isNull())
    {
      std::cout << "ERROR: NO DATA" << std::endl;
      return;
    }
    d_vars.push_back(t);
  } while (t.getKind() == Kind::CONSTANT);

  size_t nvars = d_vars.size();

  std::vector<Term> row;
  row.push_back(t);
  size_t i = 1;
  do
  {
    while (i < nvars)
    {
      t = ip.nextTerm();
      if (t.isNull())
      {
        if (row.empty())
        {
          break;
        }
        std::cout << "ERROR: incomplete row" << std::endl;
        return;
      }
      row.push_back(t);
      i++;
    }
    addRow(row);
    i = 0;
    row.clear();
  } while (true);

  std::vector<Sort> argTypes = getArgTypes();
  Sort boolSort = d_tm.getBooleanSort();
  d_oracle = d_solver->declareOracleFun(
      "oracle.in_csv", argTypes, boolSort, [&](const std::vector<Term>& input) {
        return this->evaluate(input);
      });
}

Term OracleCsvChecker::getOracle() const { return d_oracle; }

Term OracleCsvChecker::evaluate(const std::vector<Term>& evaluate)
{
  // TODO
  return d_true;
}

void OracleCsvChecker::addRow(const std::vector<Term>& row)
{
  // TODO
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
