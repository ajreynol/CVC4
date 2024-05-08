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
  d_expKeyword = tm.mkString("exp");
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();
  d_unknown = tm.mkConst(tm.getBooleanSort());
  // TODO: make option
  d_optionProp = true;
  d_optionExp = false;
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

Term OracleTableImpl::mkOr(const std::vector<Term>& children) const
{
  if (children.empty())
  {
    return d_false;
  }
  return children.size() == 1 ? children[0] : d_tm.mkTerm(Kind::OR, children);
}

Term OracleTableImpl::mkAnd(const std::vector<Term>& children) const
{
  if (children.empty())
  {
    return d_true;
  }
  return children.size() == 1 ? children[0] : d_tm.mkTerm(Kind::AND, children);
}

int OracleTableImpl::contains(const Trie* curr,
                              const std::vector<Term>& row,
                              const std::vector<Term>& sources,
                              std::vector<bool>& mask,
                              std::vector<Term>& prop) const
{
  Assert(mask.size() == row.size());
  std::map<Term, Trie>::const_iterator it;
  std::set<size_t> forced;
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
        forced.insert(i);
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
        bool isIdent = false;
        for (const std::pair<const Term, Trie>& c : cmap)
        {
          if (sources[i] == c.first)
          {
            isIdent = true;
            break;
          }
          else if (row[i] == sources[i])
          {
            // If row[i] == sources[i], then sources[i] is a value that is
            // distinct from c.first. The equality below simplifies to false.
            continue;
          }
          disj.push_back(d_tm.mkTerm(Kind::EQUAL, {sources[i], c.first}));
        }
        if (!isIdent)
        {
          // If disj is empty, then the entire propagation predicate is false.
          // We don't provide it and simply clear the vector.
          if (disj.empty())
          {
            prop.clear();
            break;
          }
          prop.push_back(mkOr(disj));
        }
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
    if (d_optionExp)
    {
      // prop stores the explanation
      if (!prop.empty())
      {
        Term pterm = mkAnd(prop);
        prop.clear();
        prop.push_back(d_tm.mkTerm(Kind::NOT, {pterm}));
      }
      // values past this don't matter
      for (size_t j = 0; j < startMask; j++)
      {
        // Forced values won't impact the result
        if (forced.find(j) == forced.end() && sources[j] != row[j])
        {
          Term eq = d_tm.mkTerm(Kind::EQUAL, {sources[j], row[j]});
          prop.push_back(eq);
        }
      }
    }
    else
    {
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
    }
    return -1;
  }
  return 1;
}

int OracleTableImpl::containsExp(const Trie* curr,
                                 const std::vector<Term>& row,
                                 const std::vector<Term>& sources,
                                 std::vector<Term>& exp) const
{
  Assert(mask.size() == row.size());
  std::map<Term, Trie>::const_iterator it;
  std::set<size_t> forced;
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
        forced.insert(i);
      }
      // found, continue
      curr = &it->second;
      continue;
    }
    size_t startMask;
    // construct an explanation
    if (d_optionProp)
    {
      startMask = i;
      bool doContinue;
      std::vector<Term> prop;
      do
      {
        std::vector<Term> disj;
        const std::map<Term, Trie>& cmap = curr->d_children;
        if (cmap.empty())
        {
          break;
        }
        bool isIdent = false;
        for (const std::pair<const Term, Trie>& c : cmap)
        {
          if (sources[i] == c.first)
          {
            isIdent = true;
            break;
          }
          else if (row[i] == sources[i])
          {
            // If row[i] == sources[i], then sources[i] is a value that is
            // distinct from c.first. The equality below simplifies to false.
            continue;
          }
          disj.push_back(d_tm.mkTerm(Kind::EQUAL, {sources[i], c.first}));
        }
        if (!isIdent)
        {
          // If disj is empty, then the entire propagation predicate is false.
          // We don't provide it and simply clear the vector.
          if (disj.empty())
          {
            prop.clear();
            break;
          }
          prop.push_back(mkOr(disj));
        }
        doContinue = (cmap.size() == 1);
        if (doContinue)
        {
          curr = &cmap.begin()->second;
          i++;
        }
      } while (doContinue);
      // prop is empty if we encountered a conflict, in this case it does
      // not contribute to the explanation.
      if (!prop.empty())
      {
        Term pterm = mkAnd(prop);
        exp.push_back(d_tm.mkTerm(Kind::NOT, {pterm}));
      }
    }
    else
    {
      startMask = (i + 1);
    }
    // values past this don't matter
    for (size_t j = 0; j < startMask; j++)
    {
      // Forced values won't impact the result
      if (forced.find(j) == forced.end() && sources[j] != row[j])
      {
        Term eq = d_tm.mkTerm(Kind::EQUAL, {sources[j], row[j]});
        exp.push_back(eq);
      }
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
    Term ret;
    if (d_optionExp)
    {
      Assert(!prop.empty());
      Term expTerm = mkAnd(prop);
      Trace("oracle-table-debug") << "Explanation " << expTerm << std::endl;
      ret =
          d_tm.mkTerm(Kind::APPLY_ANNOTATION, {d_false, d_expKeyword, expTerm});
    }
    else
    {
      std::vector<Term> maskTerms;
      for (bool b : mask)
      {
        maskTerms.push_back(b ? d_true : d_false);
      }
      Term mterm = d_tm.mkTerm(Kind::SEXPR, maskTerms);
      ret =
          d_tm.mkTerm(Kind::APPLY_ANNOTATION, {d_false, d_maskKeyword, mterm});
      if (!prop.empty())
      {
        Term pterm = mkAnd(prop);
        Trace("oracle-table-debug")
            << "Propation predicate " << pterm << std::endl;
        ret = d_tm.mkTerm(Kind::APPLY_ANNOTATION, {ret, d_propKeyword, pterm});
      }
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
