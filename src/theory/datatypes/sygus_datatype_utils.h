/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for sygus datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__SYGUS_DATATYPE_UTILS_H
#define CVC5__THEORY__STRINGS__SYGUS_DATATYPE_UTILS_H

#include <vector>

#include "expr/dtype.h"
#include "expr/node.h"
#include "theory/datatypes/theory_datatypes_utils.h"

namespace cvc5::internal {

class Env;

namespace theory {

// ----------------------- sygus datatype attributes
/** sygus var num */
struct SygusVarNumAttributeId
{
};
typedef expr::Attribute<SygusVarNumAttributeId, uint64_t> SygusVarNumAttribute;

/**
 * Attribute true for enumerators whose current model values were registered by
 * the datatypes sygus solver, and were not excluded by sygus symmetry breaking.
 * This is set by the datatypes sygus solver during LAST_CALL effort checks for
 * each active sygus enumerator.
 */
struct SygusSymBreakOkAttributeId
{
};
typedef expr::Attribute<SygusSymBreakOkAttributeId, bool>
    SygusSymBreakOkAttribute;

/** sygus var free
 *
 * This attribute is used to mark whether sygus operators have free occurrences
 * of variables from the formal argument list of the function-to-synthesize.
 *
 * We store three possible cases for sygus operators op:
 * (1) op.getAttribute(SygusVarFreeAttribute())==Node::null()
 * In this case, op has no free variables from the formal argument list of the
 * function-to-synthesize.
 * (2) op.getAttribute(SygusVarFreeAttribute())==v, where v is a bound variable.
 * In this case, op has exactly one free variable, v.
 * (3) op.getAttribute(SygusVarFreeAttribute())==op
 * In this case, op has an arbitrary set (cardinality >1) of free variables from
 * the formal argument list of the function to synthesize.
 *
 * This attribute is used to compute applySygusArgs below.
 */
struct SygusVarFreeAttributeId
{
};
typedef expr::Attribute<SygusVarFreeAttributeId, Node> SygusVarFreeAttribute;
// ----------------------- end sygus datatype attributes

namespace datatypes {
namespace utils {


/** get operator kind for sygus builtin
 *
 * This returns the Kind corresponding to applications of the operator op
 * when building the builtin version of sygus terms. This is used by the
 * function mkSygusTerm.
 */
Kind getOperatorKindForSygusBuiltin(Node op);
/**
 * Returns the total version of Kind k if it is a partial operator, or
 * otherwise k itself.
 */
Kind getEliminateKind(Kind k);
/** make sygus term
 *
 * This function returns a builtin term f( children[0], ..., children[n] )
 * where f is the builtin op that the i^th constructor of sygus datatype dt
 * encodes. If doBetaReduction is true, then lambdas are eagerly eliminated
 * via beta reduction.
 *
 * If isExternal is true, then the returned term respects the original grammar
 * that was provided. This includes the use of defined functions.
 */
Node mkSygusTerm(const DType& dt,
                 unsigned i,
                 const std::vector<Node>& children,
                 bool doBetaReduction = true,
                 bool isExternal = false);
/**
 * Same as above, but we already have the sygus operator op. The above method
 * is syntax sugar for calling this method on dt[i].getSygusOp().
 *
 * Note that this method should not be used on sygus operators that denote
 * the "any constant" constructor.
 */
Node mkSygusTerm(const Node& op,
                 const std::vector<Node>& children,
                 bool doBetaReduction = true);
/**
 * n is a builtin term that is a (rewritten) application of operator op.
 *
 * This returns an n' such that (eval n args) is n', where n' is a instance of
 * n for the appropriate substitution.
 *
 * For example, given a function-to-synthesize with formal argument list (x,y),
 * say we have grammar:
 *   A -> A+A | A+x | A+(x+y) | y
 * These lead to constructors with sygus ops:
 *   C1 / L1 where L1 is (lambda w1 w2. w1+w2)
 *   C2 / L2 where L2 is (lambda w1. w1+x)
 *   C3 / L3 where L3 is (lambda w1. w1+(x+y))
 *   C4 / L4 where L4 is y
 * Examples of calling this function:
 *   applySygusArgs( dt, L1, (APPLY_UF L1 t1 t2), { 3, 5 } )
 *     ... returns (APPLY_UF (lambda w1 w2. w1+w2) t1 t2).
 *   applySygusArgs( dt, L2, (APPLY_UF L2 t1), { 3, 5 } )
 *     ... returns (APPLY_UF (lambda w1. w1+3) t1).
 *   applySygusArgs( dt, L3, (APPLY_UF L3 t1), { 3, 5 } )
 *     ... returns (APPLY_UF (lambda w1. w1+(3+5)) t1).
 *   applySygusArgs( dt, L4, L4, { 3, 5 } )
 *     ... returns 5.
 * Notice the attribute SygusVarFreeAttribute is applied to C1, C2, C3, C4,
 * to cache the results of whether the evaluation of this constructor needs
 * a substitution over the formal argument list of the function-to-synthesize.
 */
Node applySygusArgs(const DType& dt,
                    Node op,
                    Node n,
                    const std::vector<Node>& args);
/** Sygus to builtin
 *
 * This method converts a term n of SyGuS datatype type to its builtin
 * equivalent. For example, given input C_*( C_x(), C_y() ), this method returns
 * x*y, assuming C_+, C_x, and C_y have sygus operators *, x, and y
 * respectively.
 *
 * If isExternal is true, then the returned term respects the original grammar
 * that was provided. This includes the use of defined functions. This argument
 * should typically be false, unless we are e.g. exporting the value of the
 * term as a final solution.
 *
 * If n is not constant, then its non-constant subterms that have sygus
 * datatype types are replaced by fresh variables (of the same name, if that
 * subterm is a variable, and having arbitrary name otherwise).
 */
Node sygusToBuiltin(Node n, bool isExternal = false);

/**
 * Builtin variable to sygus. Converts from builtin variables introduced by
 * the method above to their source, which is a sygus variable. It should
 * be the case that v is a variable introduced by the above method, or otherwise
 * null is returned.
 */
Node builtinVarToSygus(Node v);

/** Get free symbols in a sygus datatype type
 *
 * Add the free symbols (expr::getSymbols) in terms that can be generated by
 * sygus datatype sdt to the set syms. For example, given sdt encodes the
 * grammar:
 *   G -> a | +( b, G ) | c | e
 * We have that { a, b, c, e } are added to syms. Notice that expr::getSymbols
 * excludes variables whose kind is BOUND_VARIABLE.
 */
void getFreeSymbolsSygusType(TypeNode sdt, std::unordered_set<Node>& syms);

/**
 * Get variables in a sygus datatype type, analogous to the above but for
 * variables.
 *
 * Add the variables (expr::getVariables) in terms that can be generated by
 * sygus datatype sdt to the set syms. Notice that expr::getVariables
 * only includes variables whose kind is BOUND_VARIABLE.
 */
void getFreeVariablesSygusType(TypeNode sdt, std::unordered_set<Node>& syms);

/** Substitute and generalize a sygus datatype type
 *
 * This transforms a sygus datatype sdt into another one sdt' that generates
 * terms t such that t * { vars -> syms } is generated by sdt.
 *
 * The arguments syms and vars should be vectors of the same size and types.
 * It is recommended that the arguments in syms and vars should be variables
 * (return true for .isVar()) but this is not required.
 *
 * The variables in vars of type BOUND_VARIABLE are added to the
 * formal argument list of t. Other symbols are not.
 *
 * For example, given sdt encodes the grammar:
 *   G -> a | +( b, G ) | c | e
 * Let syms = { a, b, c } and vars = { x_a, x_b, d }, where x_a and x_b have
 * type BOUND_VARIABLE and d does not.
 * The returned type encodes the grammar:
 *   G' -> x_a | +( x_b, G' ) | d | e
 * Additionally, x_a and x_b are treated as formal arguments of a function
 * to synthesize whose syntax restrictions are specified by G'.
 *
 * This method traverses the type definition of the datatype corresponding to
 * the argument sdt.
 */
TypeNode substituteAndGeneralizeSygusType(TypeNode sdt,
                                          const std::vector<Node>& syms,
                                          const std::vector<Node>& vars);
/**
 * This converts all free symbols in the grammar specified by sdt into
 * variables using the above two methods.
 */
TypeNode generalizeSygusType(TypeNode sdt);

/**
 * Get SyGuS term size, which is based on the weight of constructor applications
 * in n.
 */
unsigned getSygusTermSize(Node n);

/**
 * Get the expanded definition form of sygus operator op, returns the
 * expanded form if the above method has been called for op, or returns op
 * otherwise.
 */
Node getExpandedDefinitionForm(Node op);
/**
 * Compute expanded definition form for all operators in sygus datatype tn,
 * recursively. This ensures that getExpandedDefinitionForm can be called
 * on all operators in tn, and moreover that mkSygusTerm can be called on
 * applications of terms of type tn.
 *
 * This method is required since sygus grammars may include user-defined
 * functions. Thus, we must use the top level substitutions in env to
 * associate the use of those functions with their expanded form, since
 * the internal sygus solver must reason about sygus operators after
 * expansion.
 */
void computeExpandedDefinitionForms(Env& env, const TypeNode& tn);
// ------------------------ end sygus utils

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif
