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

#ifndef CVC5__MAIN__ORACLE_CSV_CHECKER_H
#define CVC5__MAIN__ORACLE_CSV_CHECKER_H

#include <cvc5/cvc5.h>

namespace cvc5 {

namespace parser {
class SymbolManager;
}

namespace main {

/**
 * A class to setup an oracle for reading a CSV from disk.
 */
class OracleCsvChecker
{
 public:
  OracleCsvChecker(TermManager& tm,
              std::string& filename,
              Solver* s,
              parser::SymbolManager* sm);
  ~OracleCsvChecker();
  /** */
  std::vector<Sort> getArgTypes() const;
 private:
  /** Evaluate */
  Term evaluate(const std::vector<Term>& evaluate);
  /** The oracle we have declared */
  Term d_oracle;
  /** True and false */
  Term d_true;
  Term d_false;
  /** The variables in the header row of the csv */
  std::vector<Term> d_vars;
  /** The filename to read from */
  std::string d_filename;
  /** The solver we are associated with */
  Solver* d_solver;
  /** The symbol manager (for parsing) */
  parser::SymbolManager* d_symman;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__ORACLE_CSV_CHECKER_H */
