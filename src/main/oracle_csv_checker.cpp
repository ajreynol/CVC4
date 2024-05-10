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

std::vector<Term> Explanation::toExplanation(TermManager& tm,
                                             const std::vector<Term>& row,
                                             const std::vector<Term>& source)
{
  std::vector<Term> exp;
  for (size_t v : d_valuesEq)
  {
    Assert(row[v] != source[v]);
    Term eq = tm.mkTerm(Kind::EQUAL, {row[v], source[v]});
    exp.push_back(eq);
  }
  std::vector<Term> cexp;
  if (!d_continuationsProp.empty())
  {
    for (std::pair<const size_t, Term> v : d_continuationsProp)
    {
      Assert(v.second != source[v.first]);
      Term deq = tm.mkTerm(
          Kind::NOT, {tm.mkTerm(Kind::EQUAL, {v.second, source[v.first]})});
      cexp.push_back(deq);
    }
  }
  if (!d_continuations.empty())
  {
    Term s = source[d_continueLevel];
    std::vector<Term> ccexp;
    for (const Term& t : d_continuations)
    {
      Assert(s != t);
      Term deq = tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {t, s})});
      if (cexp.empty())
      {
        // flattens into main conjunction if we don't have propagations
        exp.push_back(deq);
      }
      else
      {
        ccexp.push_back(deq);
      }
    }
    if (!ccexp.empty())
    {
      Term cc = ccexp.size()==1 ? ccexp[0] : tm.mkTerm(Kind::AND, ccexp);
      cexp.push_back(cc);
    }
  }
  if (!cexp.empty())
  {
    Term c = cexp.size()==1 ? cexp[0] : tm.mkTerm(Kind::OR, cexp);
    exp.push_back(c);
  }
  return exp;
}

OracleTableImpl::OracleTableImpl(TermManager& tm,
                                 std::string& filename,
                                 Solver* s,
                                 parser::SymbolManager* sm)
    : d_dbInit(false),
      d_dbInitSuccess(false),
      d_filename(filename),
      d_tm(tm),
      d_solver(s),
      d_symman(sm)
{
  d_srcKeyword = tm.mkString("source");
  d_srcRlvKeyword = tm.mkString("source-rlv");
  d_maskKeyword = tm.mkString("mask");
  d_pexpKeyword = tm.mkString("partial-exp");
  d_expKeyword = tm.mkString("exp");
  d_true = tm.mkTrue();
  d_false = tm.mkFalse();
  d_unknown = tm.mkConst(tm.getBooleanSort());
}

OracleTableImpl::~OracleTableImpl() {}

bool OracleTableImpl::initializeDb()
{
  if (d_dbInit)
  {
    return d_dbInitSuccess;
  }
  d_dbInit = true;
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
      return false;
    }
    d_header.push_back(t);
  } while (t.getKind() == Kind::CONSTANT);

  d_header.pop_back();
  size_t nvars = d_header.size();
  Trace("oracle-csv-parse") << "Header size is " << nvars << std::endl;
  if (nvars != d_argSorts.size())
  {
    std::cout << "ERROR: Arity mismatch" << std::endl;
    return false;
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
        return false;
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
  d_dbInitSuccess = true;
  return true;
}

void OracleTableImpl::initialize(const std::string& id,
                                 const std::vector<Sort>& argSorts)
{
  d_argSorts = argSorts;
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

bool OracleTableImpl::isNoValueConflict(const Trie* curr,
                                        size_t depth,
                                        const std::vector<Term>& row,
                                        const std::vector<Term>& sources,
                                        const std::vector<size_t>& forcedValues,
                                        Explanation& e) const
{
  const std::map<size_t, std::set<Term>>& cmv = curr->d_noValues;
  if (cmv.empty())
  {
    return false;
  }
  std::map<size_t, std::set<Term>>::const_iterator itn;
  for (size_t fv : forcedValues)
  {
    if (fv <= depth)
    {
      // optimization, will not have no-value indices less than this depth
      continue;
    }
    itn = cmv.find(fv);
    if (itn == cmv.end())
    {
      continue;
    }
    const Term& fvr = row[fv];
    if (itn->second.find(fvr) != itn->second.end())
    {
      // infeasible, explain why, the explanation only matters if source is not
      // row
      if (sources[fv] != fvr)
      {
        e.d_valuesEq.push_back(fv);
      }
      return true;
    }
  }
  return false;
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

int OracleTableImpl::lookup(const Trie* curr,
                            const std::vector<Term>& row,
                            const std::vector<Term>& sources,
                            const std::vector<size_t>& forcedValues,
                            Explanation& e) const
{
  Trace("oracle-table") << "Compute lookup" << std::endl;
  Trace("oracle-table") << "- " << row << std::endl;
  Trace("oracle-table") << "- " << sources << std::endl;
  // a no-value conflict at the top, we are already done, its explanation (if
  // applicable) is added to e.
  if (isNoValueConflict(curr, 0, row, sources, forcedValues, e))
  {
    Trace("oracle-table") << "...forced value not in table (global)"
                          << std::endl;
    return -1;
  }
  std::map<Term, Trie>::const_iterator it;
  std::set<size_t> forced;
  for (size_t i = 0, nterms = row.size(); i < nterms; i++)
  {
    Term v = row[i];
    // currently should only have complete assignments
    Assert(v.getKind() != Kind::CONSTANT);
    /*
    if (v.getKind() == Kind::CONSTANT)
    {
      // propagate?
      return 0;
    }
    */
    // see if we have any forced values
    it = curr->d_children.find(v);
    if (it != curr->d_children.end())
    {
      if (curr->d_children.size() > 1)
      {
        Trace("oracle-table") << "...requires column #" << i << std::endl;
        // not forced, so it matters
        e.d_valuesEq.push_back(i);
      }
      else
      {
        Trace("oracle-table") << "...skip forced column #" << i << std::endl;
      }
      // ...otherwise, we will include the equality (lazily).
      // We found, now check whether it is a no-value conflict
      if (!isNoValueConflict(&it->second, i + 1, row, sources, forcedValues, e))
      {
        curr = &it->second;
        continue;
      }
      Trace("oracle-table")
          << "...forced value not in child table for " << v << std::endl;
      // explanation includes the no-value conflict, if applicable
    }
    else
    {
      Trace("oracle-table") << "...no child for " << v << std::endl;
    }
    Trace("oracle-table") << "[1] compute continue predicate" << std::endl;
    // construct a propagating predicate
    bool doContinue;
    std::vector<Term> expContinue;
    // now, only assume the values already in the explanation are forced
    std::vector<size_t> forcedValuesTmp = e.d_valuesEq;
    do
    {
      const std::map<Term, Trie>& cmap = curr->d_children;
      if (cmap.empty())
      {
        break;
      }
      // determine possibilities for how to continue, store in disj
      bool isIdent = false;
      std::vector<Term> continueTerms;
      const Trie* next = nullptr;
      for (const std::pair<const Term, Trie>& c : cmap)
      {
        if (c.first == row[i])
        {
          // already know its infeasible due to the isNoValueConflict check from
          // earlier
          continue;
        }
        Explanation eTmp;
        if (isNoValueConflict(
                &c.second, i + 1, row, sources, forcedValuesTmp, eTmp))
        {
          // eTmp is either empty or contains an explanation from
          // forcedValuesTmp that we already know about.
          Trace("oracle-table") << "......forced value not in child table for "
                                << c.first << std::endl;
          continue;
        }
        else
        {
          if (sources[i] == c.first)
          {
            isIdent = true;
            next = &c.second;
            break;
          }
          else if (row[i] == sources[i])
          {
            // If row[i] == sources[i], then sources[i] is a value that is
            // distinct from c.first. The equality below simplifies to false.
            continue;
          }
        }
        continueTerms.push_back(c.first);
        next = &c.second;
      }
      if (isIdent)
      {
        Trace("oracle-table") << ".........trivial continuation" << std::endl;
        doContinue = true;
      }
      else
      {
        doContinue = (continueTerms.size() == 1);
        if (doContinue)
        {
          e.d_continuationsProp[i] = continueTerms[0];
          Trace("oracle-table")
              << ".........propagate continuation" << std::endl;
        }
        else if (continueTerms.empty())
        {
          // if we have no continue terms, we are in conflict, we reject the
          // previous propagations, if any
          e.d_continuationsProp.clear();
          Trace("oracle-table") << ".........continue conflict" << std::endl;
        }
        else
        {
          e.d_continueLevel = i;
          e.d_continuations.insert(e.d_continuations.end(),
                                   continueTerms.begin(),
                                   continueTerms.end());
          Trace("oracle-table")
              << ".........disjunctive continuation" << std::endl;
        }
      }
      if (doContinue)
      {
        Assert(next != nullptr);
        i++;
        curr = next;
      }
    } while (doContinue);
    // explanation is fully contained in e
    return -1;
  }
  return 1;
}

bool OracleTableImpl::Trie::computeNoValue(size_t index,
                                           const std::pair<size_t, Term>& t)
{
  if (index == 0)
  {
    return d_children.find(t.second) != d_children.end();
  }
  bool found = false;
  std::vector<Trie*> noFinds;
  for (std::pair<const Term, Trie>& c : d_children)
  {
    if (c.second.computeNoValue(index - 1, t))
    {
      found = true;
    }
    else
    {
      noFinds.push_back(&c.second);
    }
  }
  if (found)
  {
    for (Trie* nt : noFinds)
    {
      nt->d_noValues[t.first].insert(t.second);
    }
  }
  return found;
}

void OracleTableImpl::computeNoValue(size_t index, const Term& t)
{
  std::pair<size_t, Term> tp(index, t);
  if (d_dataNoValues.find(tp) != d_dataNoValues.end())
  {
    // already computed
    return;
  }
  d_dataNoValues.insert(tp);
  if (!d_data.computeNoValue(index, tp))
  {
    d_data.d_noValues[index].insert(t);
  }
}

Term OracleTableImpl::evaluate(const std::vector<Term>& row)
{
  if (!initializeDb())
  {
    return d_unknown;
  }
  std::vector<Term> rowValues;
  std::vector<Term> sources;
  std::vector<size_t> forcedValues;
  for (size_t i = 0, nterms = row.size(); i < nterms; i++)
  {
    const Term& t = row[i];
    if (t.getKind() == Kind::APPLY_ANNOTATION)
    {
      if (t[1] == d_srcKeyword)
      {
        sources.push_back(t[2]);
      }
      else if (t[1] == d_srcRlvKeyword)
      {
        sources.push_back(t[2]);
        // also forced
        forcedValues.push_back(i);
        computeNoValue(i, t[0]);
      }
      else
      {
        sources.push_back(t[0]);
      }
      rowValues.push_back(t[0]);
      Assert(t[0].getKind() != Kind::APPLY_ANNOTATION);
    }
    else
    {
      rowValues.push_back(t);
      sources.push_back(t);
      // compute the first place (i,t) does not occur
      forcedValues.push_back(i);
      computeNoValue(i, t);
    }
  }
  Explanation e;
  int result = lookup(&d_data, rowValues, sources, forcedValues, e);
  if (result == 1)
  {
    return d_true;
  }
  if (result == -1)
  {
    std::vector<Term> exp = e.toExplanation(d_tm, rowValues, sources);
    Assert(!exp.empty());
    Term expTerm = mkAnd(exp);
    Trace("oracle-table-debug") << "Explanation " << expTerm << std::endl;
    Term ret =
        d_tm.mkTerm(Kind::APPLY_ANNOTATION, {d_false, d_expKeyword, expTerm});
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
