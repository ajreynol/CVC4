/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * N-ary term utilities
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__NARY_TERM_UTIL__H
#define CVC5__EXPR__NARY_TERM_UTIL__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace expr {

/** Mark variable as list */
void markListVar(TNode fv, bool isMatchOnly = false);
/** 
 * Is list variable? Returns true if fv is a list variable marked :list,
 * or :match-list and isMatch is true.
 * @param fv The variable to inspect
 * @param isMatch Whether we also return true for :match-list.
*/
bool isListVar(TNode fv, bool isMatch = true);

/** Contains list variable */
bool hasListVar(TNode n, bool isMatch = true);

/**
 * Compute list variable context
 * Stores (one of the) parents for each list variable in n, or fail if a list
 * variable occurs beneath parents that have different kinds.
 */
bool getListVarContext(TNode n, std::map<Node, Node>& context);

/**
 * Substitution with list semantics.
 * Handles mixtures of list / non-list variables in vars.
 * List variables are mapped to SEXPR whose children are the list to substitute.
 *
 * @param src The term to substitute
 * @param vars The domain of the substitution
 * @param subs The range of the substitution
 * @return the substituted term.
 */
Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    bool isMatch = true);
/**
 * Same as above, with visited cache.
 *
 * @param src The term to substitute
 * @param vars The domain of the substitution
 * @param subs The range of the substitution
 * @return the substituted term.
 */
Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    std::unordered_map<TNode, Node>& visited,
                    bool isMatch = true);

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__NARY_TERM_UTIL__H */
