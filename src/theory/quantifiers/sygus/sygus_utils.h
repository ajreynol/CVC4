/*********************                                                        */
/*! \file sygus_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief generic sygus utilities
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H

#include <vector>

#include "expr/node.h"
#include "expr/subs.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SygusUtils
{
 public:
  /**
   * Make (negated) sygus conjecture of the form
   *   forall fs. conj
   * with instantiation attributes in ips. Notice that the marker for
   * sygus conjecture is automatically prepended to this list.
   */
  static Node mkSygusConjecture(const std::vector<Node>& fs,
                                Node conj,
                                const std::vector<Node>& iattrs);
  /** Same as above, without auxiliary instantiation attributes */
  static Node mkSygusConjecture(const std::vector<Node>& fs, Node conj);

  /**
   * Make conjecture, with a set of solved functions.
   */
  static Node mkSygusConjecture(const std::vector<Node>& fs,
                                Node conj,
                                const Subs& solvedf);
  /**
   * Decompose sygus conjecture.
   *
   * @param q The sygus conjecture to decompose
   * @param fs The functions-to-synthesize
   * @param unsf The functions that have not been marked as solved.
   * @param solvedf The substitution corresponding to the solved functions.
   *
   * The vector unsf and the domain of solved are a parition of fs.
   */
  static void decomposeSygusConjecture(Node q,
                                       std::vector<Node>& fs,
                                       std::vector<Node>& unsf,
                                       Subs& solvedf);
  /**
   * Decompose the negated conjecture body.
   *
   * This returns a quantifier-free formula corresponding to the (un-negated)
   * conjecture body. It adds the quantified free variables of the conjecture
   * to vs.
   */
  static Node decomposeConjectureBody(Node conj, std::vector<Node>& vs);

  /**
   * Get the formal argument list for a function-to-synthesize. This returns
   * a node of kind BOUND_VAR_LIST that corresponds to the formal argument list
   * of the function to synthesize.
   *
   * Note that if f is constant, then this returns null, since f has no
   * arguments in this case.
   */
  static Node getSygusArgumentListForSynthFun(Node f);
  /**
   * Same as above, but adds the variables to formals.
   */
  static void getSygusArgumentListForSynthFun(Node f,
                                              std::vector<Node>& formals);
  /**
   * Wrap a solution sol for f in the proper lambda, return the lambda
   * expression. Notice the returned expression is sol itself if f has no
   * formal arguments.
   */
  static Node wrapSolutionForSynthFun(Node f, Node sol);

  /**
   * Get the sygus datatype type that encodes the syntax restrictions for
   * function-to-synthesize f.
   */
  static TypeNode getSygusTypeForSynthFun(Node f);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H */
