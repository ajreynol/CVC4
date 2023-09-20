/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle caller
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__ORACLE_BINARY_CALLER_H
#define CVC5__EXPR__ORACLE_BINARY_CALLER_H

#include <cvc5/cvc5.h>

namespace cvc5 {

namespace parser {
class SymManager;
}

class OracleBinaryCaller
{
 public:
  OracleBinaryCaller(Solver* slv, parser::SymManager* sm, std::string binName)
      : d_slv(slv),
        d_sm(sm),
        d_binaryName(binName),
        d_parseStreamName("oracle_output_" + binName)
  {
  }
  /** Run */
  std::vector<Term> runOracle(const std::vector<Term>& input);
  /** Run, single return version */
  Term runOracleSingleOut(const std::vector<Term>& input);

 private:
  /** pointer to solver */
  Solver* d_slv;
  /** pointer to symbol manager */
  parser::SymManager* d_sm;
  /** binary name */
  std::string d_binaryName;
  /** name for parse errors */
  std::string d_parseStreamName;
};

}  // namespace cvc5

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
