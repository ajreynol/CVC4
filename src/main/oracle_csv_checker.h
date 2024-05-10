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

class Explanation
{
 public:
  Explanation() : d_continueLevel(0) {}
  /** Columns that contributed to explanation */
  std::vector<size_t> d_valuesEq;
  /** The column that was in conflict (not in d_valuesEq) */
  size_t d_continueLevel;
  /**
   * If non-empty, this is a complete set of alternatives for the column at
   * d_continueLevel that may lead to finding an entry in the table.
   */
  std::vector<Term> d_continuations;
  /**
   * If non-empty, d_continuationsProp[i] stores a term that sources[i] must be
   * to equal to in order to find an entry in the table.
   */
  std::map<size_t, Term> d_continuationsProp;
  /** Convert to explanation */
  std::vector<Term> toExplanation(TermManager& tm,
                                  const std::vector<Term>& row,
                                  const std::vector<Term>& source);
};

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
  /** initialize the database */
  bool initializeDb();
  /** */
  void addRow(const std::vector<Term>& row);
  /** Evaluate */
  Term evaluate(const std::vector<Term>& evaluate);
  class Trie
  {
   public:
    Trie() : d_count(0) {}
    size_t d_count;
    /** Set of values that do not appear in this subtrie */
    std::map<size_t, std::set<Term>> d_noValues;
    /** List of children */
    std::map<Term, Trie> d_children;
    void add(const std::vector<Term>& row);
    bool computeNoValue(size_t index, const std::pair<size_t, Term>& t);
  };
  /** Contains */
  int lookup(const Trie* curr,
             const std::vector<Term>& row,
             const std::vector<Term>& sources,
             const std::vector<size_t>& forcedValues,
             Explanation& e) const;
  bool isNoValueConflict(const Trie* curr,
                         size_t depth,
                         const std::vector<Term>& row,
                         const std::vector<Term>& sources,
                         const std::vector<size_t>& forcedValues,
                         Explanation& e) const;
  /** Compute no-value */
  void computeNoValue(size_t index, const Term& t);
  Term mkOr(const std::vector<Term>& children) const;
  Term mkAnd(const std::vector<Term>& children) const;
  /** Initialize the database */
  bool d_dbInit;
  /** Whether we were successful */
  bool d_dbInitSuccess;
  /** The data */
  Trie d_data;
  /** The set of values that we have added to "no values" in terms */
  std::set<std::pair<size_t, Term>> d_dataNoValues;
  /** The oracle we have declared */
  Term d_oracle;
  /** Argument sorts we are using */
  std::vector<Sort> d_argSorts;
  /** Commonly used terms */
  Term d_srcKeyword;
  Term d_srcRlvKeyword;
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
