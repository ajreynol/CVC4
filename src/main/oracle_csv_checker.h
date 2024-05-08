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
class OracleTableImpl
{
 public:
  OracleTableImpl(TermManager& tm,
                  std::string& filename,
                  Solver* s,
                  parser::SymbolManager* sm);
  ~OracleTableImpl();
  /** Get the oracle defined by this class */
  Term getOracleFun() const;
  /** */
  std::vector<Sort> getArgTypes() const;
  /**
   * Initialize. To be called only when parsing is ready and prior to solving.
   */
  void initialize(const std::string& id, const std::vector<Sort>& argSorts);

 private:
  /** */
  void addRow(const std::vector<Term>& row);
  /** Evaluate */
  Term evaluate(const std::vector<Term>& evaluate);
  class Trie
  {
   public:
    Trie() : d_count(0) {}
    size_t d_count;
    std::map<Term, Trie> d_children;
    void add(const std::vector<Term>& row);
  };
  Trie d_data;
  /** Contains */
  int contains(const Trie* curr,
               const std::vector<Term>& row,
               const std::vector<Term>& sources,
               std::vector<bool>& mask,
               std::vector<Term>& prop) const;
  Term mkOr(const std::vector<Term>& children) const;
  Term mkAnd(const std::vector<Term>& children) const;
  /** */
  bool d_optionProp;
  bool d_optionExp;
  /** The oracle we have declared */
  Term d_oracle;
  /** Commonly used terms */
  Term d_srcKeyword;
  Term d_maskKeyword;
  Term d_pexpKeyword;
  Term d_expKeyword;
  Term d_true;
  Term d_false;
  Term d_unknown;
  Term d_null;
  /** The variables in the header row of the csv */
  std::vector<Term> d_header;
  /** The filename to read from */
  std::string d_filename;
  /** The term manager we are associated with */
  TermManager& d_tm;
  /** The solver we are associated with */
  Solver* d_solver;
  /** The symbol manager (for parsing) */
  parser::SymbolManager* d_symman;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__ORACLE_CSV_CHECKER_H */
