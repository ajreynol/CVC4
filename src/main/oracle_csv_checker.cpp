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
  d_srcKeyword = tm.mkString("source");
  d_maskKeyword = tm.mkString("mask");
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();
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
    d_header.push_back(t);
  } while (t.getKind() == Kind::CONSTANT);

  d_header.pop_back();
  size_t nvars = d_header.size();
  Trace("oracle-csv-parse") << "Header size is " << nvars << std::endl;

  std::vector<Term> row;
  row.push_back(t);
  size_t i = 1;
  bool finished = false;
  do
  {
    while (i < nvars)
    {
      t = ip.nextTerm();
      if (t.isNull())
      {
        finished = true;
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
    if (!finished)
    {
      addRow(row);
      i = 0;
      row.clear();
    }
  } while (!finished);
  Trace("oracle-csv-parse") << "Finished reading csv" << std::endl;

  std::vector<Sort> argTypes = getArgTypes();
  Sort boolSort = d_tm.getBooleanSort();
  d_oracle = d_solver->declareOracleFun(
      "oracle.in_csv", argTypes, boolSort, [&](const std::vector<Term>& input) {
        return this->evaluate(input);
      });
  std::vector<Term> cc;
  cc.push_back(d_oracle);
  cc.insert(cc.end(), d_header.begin(), d_header.end());
  d_oracleConstraint = d_tm.mkTerm(Kind::APPLY_UF, cc);
  d_solver->assertFormula(d_oracleConstraint);
}

Term OracleCsvChecker::getOracle() const { return d_oracle; }
Term OracleCsvChecker::getOracleConstraint() const
{
  return d_oracleConstraint;
}

void OracleCsvChecker::Trie::add(const std::vector<Term>& row)
{
  Trie* curr = this;
  for (const Term& t : row)
  {
    curr = &curr->d_children[t];
  }
}

bool OracleCsvChecker::Trie::contains(const std::vector<Term>& row,
                                      std::vector<bool>& mask) const
{
  Assert(mask.size() == row.size());
  const Trie* curr = this;
  std::map<Term, Trie>::const_iterator it;
  for (size_t i = 0, nterms = row.size(); i < nterms; i++)
  {
    it = curr->d_children.find(row[i]);
    if (it != curr->d_children.end())
    {
      // found, continue
      curr = &it->second;
      continue;
    }
    // values past this don't matter
    for (size_t j = (i + 1); j < nterms; j++)
    {
      mask[j] = false;
    }
    // TODO: more generalization?
    return false;
  }
  return true;
}

Term OracleCsvChecker::evaluate(const std::vector<Term>& row)
{
  // process the mask
  std::vector<bool> mask;
  std::vector<Term> rowValues;
  for (const Term& t : row)
  {
    if (t.getKind() == Kind::APPLY_ANNOTATION)
    {
      // add it to mask if was marked with ":source"
      mask.push_back(true);//t[1] == d_srcKeyword);
      rowValues.push_back(t[0]);
      Assert(t[0].getKind() != Kind::APPLY_ANNOTATION);
    }
    else
    {
      mask.push_back(false);
      rowValues.push_back(t);
    }
  }
  if (d_data.contains(rowValues, mask))
  {
    return d_true;
  }
  std::vector<Term> maskTerms;
  for (bool b : mask)
  {
    maskTerms.push_back(b ? d_true : d_false);
  }
  Term mterm = d_tm.mkTerm(Kind::SEXPR, maskTerms);
  return d_tm.mkTerm(Kind::APPLY_ANNOTATION, {d_false, d_maskKeyword, mterm});
}

void OracleCsvChecker::addRow(const std::vector<Term>& row) { d_data.add(row); }

std::vector<Sort> OracleCsvChecker::getArgTypes() const
{
  std::vector<Sort> sorts;
  for (const Term& t : d_header)
  {
    sorts.push_back(t.getSort());
  }
  return sorts;
}

}  // namespace main
}  // namespace cvc5
