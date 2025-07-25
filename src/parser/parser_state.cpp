/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parser state implementation.
 */

#include "parser/parser_state.h"

#include <cvc5/cvc5.h>

#include <clocale>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <unordered_set>

#include "base/check.h"
#include "base/output.h"
#include "expr/kind.h"
#include "parser/commands.h"

using namespace std;

namespace cvc5 {
namespace parser {

ParserState::ParserState(ParserStateCallback* psc,
                         Solver* solver,
                         SymManager* sm,
                         ParsingMode parsingMode)
    : d_solver(solver),
      d_tm(d_solver->getTermManager()),
      d_psc(psc),
      d_symman(sm),
      d_symtab(sm->getSymbolTable()),
      d_checksEnabled(true),
      d_parsingMode(parsingMode),
      d_parseOnly(d_solver->getOptionInfo("parse-only").boolValue())
{
}

ParserState::~ParserState() {}

Solver* ParserState::getSolver() const { return d_solver; }

Term ParserState::getVariable(const std::string& name)
{
  Term ret = d_symtab->lookup(name);
  // if the lookup failed, throw an error
  if (ret.isNull())
  {
    checkDeclaration(name, CHECK_DECLARED, SYM_VARIABLE);
  }
  return ret;
}

Term ParserState::getExpressionForNameAndType(const std::string& name, Sort t)
{
  Assert(isDeclared(name));
  // first check if the variable is declared and not overloaded
  Term expr = getVariable(name);
  if (expr.isNull())
  {
    // the variable is overloaded, try with type if the type exists
    if (!t.isNull())
    {
      // if we decide later to support annotations for function types, this will
      // update to separate t into ( argument types, return type )
      expr = getOverloadedConstantForType(name, t);
      if (expr.isNull())
      {
        parseError("Cannot get overloaded constant for type ascription.");
      }
    }
    else
    {
      parseError("Overloaded constants must be type cast.");
    }
  }
  Assert(!expr.isNull());
  return expr;
}

bool ParserState::getTesterName(Term cons, std::string& name) { return false; }

Kind ParserState::getKindForFunction(Term fun)
{
  Sort t = fun.getSort();
  if (t.isFunction())
  {
    return Kind::APPLY_UF;
  }
  else if (t.isDatatypeConstructor())
  {
    return Kind::APPLY_CONSTRUCTOR;
  }
  else if (t.isDatatypeSelector())
  {
    return Kind::APPLY_SELECTOR;
  }
  else if (t.isDatatypeTester())
  {
    return Kind::APPLY_TESTER;
  }
  else if (t.isDatatypeUpdater())
  {
    return Kind::APPLY_UPDATER;
  }
  return Kind::UNDEFINED_KIND;
}

Sort ParserState::getSort(const std::string& name)
{
  Sort t = d_symtab->lookupType(name);
  // if we fail, throw an error
  if (t.isNull())
  {
    checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  }
  return t;
}

Sort ParserState::getParametricSort(const std::string& name,
                                    const std::vector<Sort>& params)
{
  Sort t = d_symtab->lookupType(name, params);
  // if we fail, throw an error
  if (t.isNull())
  {
    checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  }
  return t;
}

bool ParserState::isFunctionLike(Term fun)
{
  if (fun.isNull())
  {
    return false;
  }
  Sort type = fun.getSort();
  return type.isFunction() || type.isDatatypeConstructor()
         || type.isDatatypeTester() || type.isDatatypeSelector();
}

Term ParserState::bindVar(const std::string& name,
                          const Sort& type,
                          bool doOverload)
{
  Trace("parser") << "bindVar(" << name << ", " << type << ")" << std::endl;
  Term expr = d_tm.mkConst(type, name);
  defineVar(name, expr, doOverload);
  return expr;
}

Term ParserState::bindBoundVar(const std::string& name,
                               const Sort& type,
                               bool fresh)
{
  Trace("parser") << "bindBoundVar(" << name << ", " << type << ")"
                  << std::endl;
  std::pair<std::string, Sort> key(name, type);
  Term expr;
  if (fresh)
  {
    expr = d_tm.mkVar(type, name);
  }
  else
  {
    std::map<std::pair<std::string, Sort>, Term>::iterator itv =
        d_varCache.find(key);
    if (itv != d_varCache.end())
    {
      expr = itv->second;
    }
    else
    {
      expr = d_tm.mkVar(type, name);
      d_varCache[key] = expr;
    }
  }
  defineVar(name, expr);
  return expr;
}

std::vector<Term> ParserState::bindBoundVars(
    std::vector<std::pair<std::string, Sort> >& sortedVarNames, bool fresh)
{
  std::vector<Term> vars;
  for (std::pair<std::string, Sort>& i : sortedVarNames)
  {
    vars.push_back(bindBoundVar(i.first, i.second, fresh));
  }
  return vars;
}

std::vector<Term> ParserState::bindBoundVarsCtx(
    std::vector<std::pair<std::string, Sort>>& sortedVarNames,
    std::vector<std::vector<std::pair<std::string, Term>>>& letBinders,
    bool fresh)
{
  if (fresh || letBinders.empty())
  {
    // does not matter if let binders are empty or if we are constructing fresh
    return bindBoundVars(sortedVarNames, fresh);
  }
  std::vector<Term> vars;
  for (std::pair<std::string, Sort>& i : sortedVarNames)
  {
    std::map<std::pair<std::string, Sort>, Term>::const_iterator itv =
        d_varCache.find(i);
    if (itv == d_varCache.end() || !isDeclared(i.first))
    {
      // haven't created this variable yet, or its not declared
      Term v = bindBoundVar(i.first, i.second, fresh);
      vars.push_back(v);
      continue;
    }
    Term v = itv->second;
    // If we are here, then:
    // (1) we are not using fresh declarations
    // (2) there are let binders present,
    // (3) the current variable was shadowed.
    // We must check whether the variable is present in the let bindings.
    bool reqFresh = false;
    // a dummy variable used for checking containment below
    Term vr = d_tm.mkVar(v.getSort(), "dummy");
    // check if it is contained in a let binder, if so, we require making a
    // fresh variable, despite fresh-binders being false.
    for (std::vector<std::pair<std::string, Term>>& lbs : letBinders)
    {
      for (std::pair<std::string, Term>& lb : lbs)
      {
        // To test containment, we use Term::substitute.
        // If the substitution does anything at all, then we will throw a
        // warning. We expect this warning to be very rare.
        Term slbt = lb.second.substitute({v}, {vr});
        if (slbt != lb.second)
        {
          reqFresh = true;
          break;
        }
      }
      if (reqFresh)
      {
        break;
      }
    }
    if (reqFresh)
    {
      // Note that if this warning is thrown:
      // 1. proof reference checking will not be accurate in settings where
      // variables are parsed as canonical.
      // 2. the parser will not be deterministic for the same input even when
      // fresh-binders is false, since we are constructing a fresh variable
      // below.
      Warning() << "Constructing a fresh variable for " << i.first
                << " since this symbol occurs in a let term that is present in "
                   "the current context. Set fresh-binders to true or use -q to avoid "
                   "this warning."
                << std::endl;
    }
    v = bindBoundVar(i.first, i.second, reqFresh);
    vars.push_back(v);
  }
  return vars;
}

std::vector<Term> ParserState::bindBoundVars(
    const std::vector<std::string> names, const Sort& type)
{
  std::vector<Term> vars;
  for (unsigned i = 0; i < names.size(); ++i)
  {
    vars.push_back(bindBoundVar(names[i], type));
  }
  return vars;
}

void ParserState::defineVar(const std::string& name,
                            const Term& val,
                            bool doOverload)
{
  Trace("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  if (!d_symtab->bind(name, val, doOverload))
  {
    std::stringstream ss;
    ss << "Cannot bind " << name << " to symbol of type " << val.getSort();
    ss << ", maybe the symbol has already been defined?";
    parseError(ss.str());
  }
  Assert(isDeclared(name));
}

void ParserState::defineType(const std::string& name,
                             const Sort& type,
                             bool isUser)
{
  if (!isUser && isDeclared(name, SYM_SORT))
  {
    Assert(d_symtab->lookupType(name) == type);
    return;
  }
  d_symman->bindType(name, type, isUser);
  Assert(isDeclared(name, SYM_SORT));
}

void ParserState::defineType(const std::string& name,
                             const std::vector<Sort>& params,
                             const Sort& type,
                             bool isUser)
{
  d_symman->bindType(name, params, type, isUser);
  Assert(isDeclared(name, SYM_SORT));
}

Sort ParserState::mkSort(const std::string& name)
{
  Trace("parser") << "newSort(" << name << ")" << std::endl;
  Sort type = d_tm.mkUninterpretedSort(name);
  defineType(name, type, true);
  return type;
}

Sort ParserState::mkSortConstructor(const std::string& name, size_t arity)
{
  Trace("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  Sort type = d_tm.mkUninterpretedSortConstructorSort(arity, name);
  defineType(name, vector<Sort>(arity), type, true);
  return type;
}

Sort ParserState::mkUnresolvedType(const std::string& name)
{
  Sort unresolved = d_tm.mkUnresolvedDatatypeSort(name);
  defineType(name, unresolved, true);
  return unresolved;
}

Sort ParserState::mkUnresolvedTypeConstructor(const std::string& name,
                                              size_t arity)
{
  Sort unresolved = d_tm.mkUnresolvedDatatypeSort(name, arity);
  defineType(name, vector<Sort>(arity), unresolved, true);
  return unresolved;
}

Sort ParserState::mkUnresolvedTypeConstructor(const std::string& name,
                                              const std::vector<Sort>& params)
{
  Trace("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  Sort unresolved = d_tm.mkUnresolvedDatatypeSort(name, params.size());
  defineType(name, params, unresolved, true);
  Sort t = getParametricSort(name, params);
  return unresolved;
}

Sort ParserState::mkUnresolvedType(const std::string& name, size_t arity)
{
  if (arity == 0)
  {
    return mkUnresolvedType(name);
  }
  return mkUnresolvedTypeConstructor(name, arity);
}

std::vector<Sort> ParserState::mkMutualDatatypeTypes(
    std::vector<DatatypeDecl>& datatypes)
{
  try
  {
    std::vector<Sort> types = d_tm.mkDatatypeSorts(datatypes);

    Assert(datatypes.size() == types.size());

    for (unsigned i = 0; i < datatypes.size(); ++i)
    {
      Sort t = types[i];
      const Datatype& dt = t.getDatatype();
      const std::string& name = dt.getName();
      Trace("parser-idt") << "define " << name << " as " << t << std::endl;
      if (isDeclared(name, SYM_SORT))
      {
        throw ParserException(name + " already declared");
      }
      std::unordered_set<std::string> consNames;
      std::unordered_set<std::string> selNames;
      for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        const DatatypeConstructor& ctor = dt[j];
        Term constructor = ctor.getTerm();
        Trace("parser-idt") << "+ define " << constructor << std::endl;
        std::string constructorName = ctor.getName();
        if (consNames.find(constructorName) == consNames.end())
        {
          consNames.insert(constructorName);
        }
        else
        {
          throw ParserException(constructorName
                                + " already declared in this datatype");
        }
        for (size_t k = 0, nargs = ctor.getNumSelectors(); k < nargs; k++)
        {
          const DatatypeSelector& sel = ctor[k];
          Term selector = sel.getTerm();
          Trace("parser-idt") << "+++ define " << selector << std::endl;
          std::string selectorName = sel.getName();
          if (selNames.find(selectorName) == selNames.end())
          {
            selNames.insert(selectorName);
          }
          else
          {
            throw ParserException(selectorName
                                  + " already declared in this datatype");
          }
        }
      }
    }
    return types;
  }
  catch (internal::IllegalArgumentException& ie)
  {
    throw ParserException(ie.getMessage());
  }
}

Sort ParserState::flattenFunctionType(std::vector<Sort>& sorts,
                                      Sort range,
                                      std::vector<Term>& flattenVars)
{
  if (range.isFunction())
  {
    std::vector<Sort> domainTypes = range.getFunctionDomainSorts();
    for (unsigned i = 0, size = domainTypes.size(); i < size; i++)
    {
      sorts.push_back(domainTypes[i]);
      // the introduced variable is internal (not parsable)
      std::stringstream ss;
      ss << "__flatten_var_" << i;
      Term v = d_tm.mkVar(domainTypes[i], ss.str());
      flattenVars.push_back(v);
    }
    range = range.getFunctionCodomainSort();
  }
  return range;
}

Sort ParserState::flattenFunctionType(std::vector<Sort>& sorts, Sort range)
{
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "flattenFunctionType: range " << range
                    << " and domains ";
    for (Sort t : sorts)
    {
      Trace("parser") << " " << t;
    }
    Trace("parser") << "\n";
  }
  while (range.isFunction())
  {
    std::vector<Sort> domainTypes = range.getFunctionDomainSorts();
    sorts.insert(sorts.end(), domainTypes.begin(), domainTypes.end());
    range = range.getFunctionCodomainSort();
  }
  return range;
}
Sort ParserState::mkFlatFunctionType(std::vector<Sort>& sorts, Sort range)
{
  // Note we require this flattening since the API explicitly checks that
  // the range of functions is not a function.
  Sort newRange = flattenFunctionType(sorts, range);
  if (!sorts.empty())
  {
    return d_tm.mkFunctionSort(sorts, newRange);
  }
  return newRange;
}

Term ParserState::mkHoApply(Term expr, const std::vector<Term>& args)
{
  for (size_t i = 0; i < args.size(); i++)
  {
    expr = d_tm.mkTerm(Kind::HO_APPLY, {expr, args[i]});
  }
  return expr;
}

Term ParserState::applyTypeAscription(Term t, Sort s)
{
  Kind k = t.getKind();
  if (k == Kind::SET_EMPTY)
  {
    t = d_tm.mkEmptySet(s);
  }
  else if (k == Kind::BAG_EMPTY)
  {
    t = d_tm.mkEmptyBag(s);
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    if (!s.isSequence())
    {
      std::stringstream ss;
      ss << "Type ascription on empty sequence must be a sequence, got " << s;
      parseError(ss.str());
    }
    if (!t.getSequenceValue().empty())
    {
      std::stringstream ss;
      ss << "Cannot apply a type ascription to a non-empty sequence";
      parseError(ss.str());
    }
    t = d_tm.mkEmptySequence(s.getSequenceElementSort());
  }
  else if (k == Kind::SET_UNIVERSE)
  {
    t = d_tm.mkUniverseSet(s);
  }
  else if (k == Kind::SEP_NIL)
  {
    t = d_tm.mkSepNil(s);
  }
  else if (k == Kind::APPLY_CONSTRUCTOR)
  {
    // For nullable.null we do not have a kind.
    // so we need to check the sort here.
    if (s.isNullable())
    {
      // parsing (as nullable.null (Nullable T))
      t = d_tm.mkNullableNull(s);
    }
    else
    {
      std::vector<Term> children(t.begin(), t.end());
      // apply type ascription to the operator and reconstruct
      children[0] = applyTypeAscription(children[0], s);
      t = d_tm.mkTerm(Kind::APPLY_CONSTRUCTOR, children);
    }
  }
  Sort etype = t.getSort();
  if (etype.isDatatypeConstructor())
  {
    // Type ascriptions only have an effect on the node structure if this is a
    // parametric datatype.
    // get the datatype that t belongs to
    Sort etyped = etype.getDatatypeConstructorCodomainSort();
    Datatype d = etyped.getDatatype();
    // Note that we check whether the datatype is parametric, and not whether
    // etyped is a parametric datatype, since e.g. the smt2 parser constructs
    // an arbitrary instantitated constructor term before it is resolved.
    // Hence, etyped is an instantiated datatype type, but we correctly
    // check if its datatype is parametric.
    if (d.isParametric())
    {
      // lookup by name
      DatatypeConstructor dc = d.getConstructor(t.toString());
      // ask the constructor for the specialized constructor term
      t = dc.getInstantiatedTerm(s);
    }
    // the type of t does not match the sort s by design (constructor type
    // vs datatype type), thus we use an alternative check here.
    if (t.getSort().getDatatypeConstructorCodomainSort() != s)
    {
      std::stringstream ss;
      ss << "Type ascription on constructor not satisfied, term " << t
         << " expected sort " << s << " but has sort " << etyped;
      parseError(ss.str());
    }
    return t;
  }
  // Otherwise, check that the type is correct. Type ascriptions in SMT-LIB 2.6
  // referred to the range of function sorts. Note that this is only a check
  // and does not impact the returned term.
  Sort checkSort = t.getSort();
  if (checkSort.isFunction())
  {
    checkSort = checkSort.getFunctionCodomainSort();
  }
  if (checkSort != s)
  {
    std::stringstream ss;
    ss << "Type ascription not satisfied, term " << t
       << " expected (codomain) sort " << s << " but has sort " << t.getSort();
    parseError(ss.str());
  }
  return t;
}

bool ParserState::isDeclared(const std::string& name, SymbolType type)
{
  switch (type)
  {
    case SYM_VARIABLE: return d_symtab->isBound(name);
    case SYM_SORT: return d_symtab->isBoundType(name);
    case SYM_VERBATIM: Unreachable();
  }
  Assert(false);  // Unhandled(type);
  return false;
}

void ParserState::checkDeclaration(const std::string& varName,
                                   DeclarationCheck check,
                                   SymbolType type,
                                   std::string notes)
{
  if (!d_checksEnabled)
  {
    return;
  }

  switch (check)
  {
    case CHECK_DECLARED:
      if (!isDeclared(varName, type))
      {
        parseError("Symbol '" + varName + "' not declared as a "
                   + (type == SYM_VARIABLE ? "variable" : "type")
                   + (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_UNDECLARED:
      if (isDeclared(varName, type))
      {
        parseError("Symbol '" + varName + "' previously declared as a "
                   + (type == SYM_VARIABLE ? "variable" : "type")
                   + (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_NONE: break;

    default: Assert(false);  // Unhandled(check);
  }
}

void ParserState::checkFunctionLike(Term fun)
{
  if (d_checksEnabled && !isFunctionLike(fun))
  {
    stringstream ss;
    ss << "Expecting function-like symbol, found '";
    ss << fun;
    ss << "'";
    parseError(ss.str());
  }
}

void ParserState::addOperator(Kind kind) { d_logicOperators.insert(kind); }

void ParserState::warning(const std::string& msg) { d_psc->warning(msg); }

void ParserState::parseError(const std::string& msg) { d_psc->parseError(msg); }

void ParserState::unexpectedEOF(const std::string& msg)
{
  d_psc->unexpectedEOF(msg);
}

void ParserState::attributeNotSupported(const std::string& attr)
{
  if (d_attributesWarnedAbout.find(attr) == d_attributesWarnedAbout.end())
  {
    stringstream ss;
    ss << "warning: Attribute '" << attr
       << "' not supported (ignoring this and all following uses)";
    warning(ss.str());
    d_attributesWarnedAbout.insert(attr);
  }
}

size_t ParserState::scopeLevel() const { return d_symman->scopeLevel(); }

void ParserState::pushScope(bool isUserContext)
{
  d_symman->pushScope(isUserContext);
}

void ParserState::pushGetValueScope()
{
  pushScope();
  // We cannot ask for the model domain elements if we are in parse-only mode.
  // Hence, we do nothing here.
  if (d_parseOnly)
  {
    return;
  }
  // we must bind all relevant uninterpreted constants, which coincide with
  // the set of uninterpreted constants that are printed in the definition
  // of a model.
  std::vector<Sort> declareSorts = d_symman->getDeclaredSorts();
  Trace("parser") << "Push get value scope, with " << declareSorts.size()
                  << " declared sorts" << std::endl;
  for (const Sort& s : declareSorts)
  {
    std::vector<Term> elements = d_solver->getModelDomainElements(s);
    Trace("parser") << "elements for " << s << ":" << std::endl;
    for (const Term& e : elements)
    {
      Trace("parser") << "  " << e.getKind() << " " << e << std::endl;
      if (e.getKind() == Kind::UNINTERPRETED_SORT_VALUE)
      {
        defineVar(e.getUninterpretedSortValue(), e);
      }
      else
      {
        Assert(false)
            << "model domain element is not an uninterpreted sort value: " << e;
      }
    }
  }
}

void ParserState::popScope() { d_symman->popScope(); }

void ParserState::reset() {}

SymManager* ParserState::getSymbolManager() { return d_symman; }

std::string ParserState::stripQuotes(const std::string& s)
{
  if (s.size() < 2 || s[0] != '\"' || s[s.size() - 1] != '\"')
  {
    parseError("Expected a string delimited by quotes, got invalid string `" + s
               + "`.");
  }
  return s.substr(1, s.size() - 2);
}

Term ParserState::mkCharConstant(const std::string& s)
{
  Assert(s.find_first_not_of("0123456789abcdefABCDEF", 0) == std::string::npos
         && s.size() <= 5 && s.size() > 0)
      << "Unexpected string for hexadecimal character " << s;
  char32_t val = static_cast<char32_t>(std::stoul(s, 0, 16));
  return d_tm.mkString(std::u32string(1, val));
}

uint32_t stringToUnsigned(const std::string& str)
{
  uint32_t result;
  std::stringstream ss;
  ss << str;
  ss >> result;
  return result;
}

}  // namespace parser
}  // namespace cvc5
