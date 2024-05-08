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

OracleTableImpl::OracleTableImpl(TermManager& tm,
                                 std::string& filename,
                                 Solver* s,
                                 parser::SymbolManager* sm)
    : d_filename(filename), d_tm(tm), d_solver(s), d_symman(sm)
{
  d_srcKeyword = tm.mkString("source");
  d_maskKeyword = tm.mkString("mask");
  d_propKeyword = tm.mkString("propagate");
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();
  d_unknown = tm.mkConst(tm.getBooleanSort());
  // TODO: make option
  d_optionProp = true;
}

OracleTableImpl::~OracleTableImpl() {}

void OracleTableImpl::initialize(const std::string& id,
                                 const std::vector<Sort>& argSorts)
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
  if (nvars != argSorts.size())
  {
    std::cout << "ERROR: Arity mismatch" << std::endl;
    return;
  }

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

  Sort boolSort = d_tm.getBooleanSort();
  // declare it
  d_oracle = d_solver->declareOracleFun(
      id, argSorts, boolSort, [&](const std::vector<Term>& input) {
        return this->evaluate(input);
      });
}

Term OracleTableImpl::getOracleFun() const { return d_oracle; }

void OracleTableImpl::Trie::add(const std::vector<Term>& row)
{
  Trie* curr = this;
  for (const Term& t : row)
  {
    curr->d_count++;
    curr = &curr->d_children[t];
  }
}

Term mkOr(TermManager& tm, const std::vector<Term>& children)
{
  Assert(!children.empty());
  return children.size() == 1 ? children[0] : tm.mkTerm(Kind::OR, children);
}

Term mkAnd(TermManager& tm, const std::vector<Term>& children)
{
  Assert(!children.empty());
  return children.size() == 1 ? children[0] : tm.mkTerm(Kind::AND, children);
}

int OracleTableImpl::contains(const Trie* curr,
                              const std::vector<Term>& row,
                              const std::vector<Term>& sources,
                              std::vector<bool>& mask,
                              std::vector<Term>& prop) const
{
  Assert(mask.size() == row.size());
  std::map<Term, Trie>::const_iterator it;
  std::vector<size_t> forced;
  for (size_t i = 0, nterms = row.size(); i < nterms; i++)
  {
    Term v = row[i];
    if (v.getKind() == Kind::CONSTANT)
    {
      // propagate?
      return 0;
    }
    it = curr->d_children.find(v);
    if (it != curr->d_children.end())
    {
      if (curr->d_children.size() == 1)
      {
        forced.push_back(i);
      }
      // found, continue
      curr = &it->second;
      continue;
    }
    size_t startMask;
    // construct a propagating predicate
    if (d_optionProp)
    {
      startMask = i;
      bool doContinue;
      do
      {
        std::vector<Term> disj;
        const std::map<Term, Trie>& cmap = curr->d_children;
        if (cmap.empty())
        {
          break;
        }
        for (const std::pair<const Term, Trie>& c : cmap)
        {
          disj.push_back(d_tm.mkTerm(Kind::EQUAL, {sources[i], c.first}));
        }
        prop.push_back(mkOr(d_tm, disj));
        doContinue = (cmap.size() == 1);
        if (doContinue)
        {
          curr = &cmap.begin()->second;
          i++;
        }
      } while (doContinue);
    }
    else
    {
      startMask = (i + 1);
    }
    // Forced values won't impact the result
    for (size_t j : forced)
    {
      mask[j] = false;
    }
    // values past this don't matter
    for (size_t j = startMask; j < nterms; j++)
    {
      mask[j] = false;
    }
    return -1;
  }
  return 1;
}

Term OracleTableImpl::evaluate(const std::vector<Term>& row)
{
  // process the mask
  std::vector<bool> mask;
  std::vector<Term> rowValues;
  std::vector<Term> sources;
  for (const Term& t : row)
  {
    if (t.getKind() == Kind::APPLY_ANNOTATION)
    {
      // add it to mask if was marked with ":source"
      if (t[1] == d_srcKeyword)
      {
        mask.push_back(true);
        sources.push_back(t[2]);
      }
      else
      {
        mask.push_back(false);
        sources.push_back(t[0]);
      }
      rowValues.push_back(t[0]);
      Assert(t[0].getKind() != Kind::APPLY_ANNOTATION);
    }
    else
    {
      mask.push_back(false);
      rowValues.push_back(t);
      sources.push_back(t);
    }
  }
  std::vector<Term> prop;
  int result = contains(&d_data, rowValues, sources, mask, prop);
  if (result == 1)
  {
    return d_true;
  }
  if (result == -1)
  {
    std::vector<Term> maskTerms;
    for (bool b : mask)
    {
      maskTerms.push_back(b ? d_true : d_false);
    }
    Term mterm = d_tm.mkTerm(Kind::SEXPR, maskTerms);
    Term ret =
        d_tm.mkTerm(Kind::APPLY_ANNOTATION, {d_false, d_maskKeyword, mterm});
    if (!prop.empty())
    {
      Term pterm = mkAnd(d_tm, prop);
      Trace("oracle-table-debug") << "Propation predicate " << pterm << std::endl;
      ret = d_tm.mkTerm(Kind::APPLY_ANNOTATION, {ret, d_propKeyword, pterm});
    }
    return ret;
  }
  return d_unknown;
}

void OracleTableImpl::addRow(const std::vector<Term>& row) { d_data.add(row); }

std::vector<Sort> OracleTableImpl::getArgTypes() const
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
