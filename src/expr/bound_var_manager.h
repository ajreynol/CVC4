/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bound variable manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__BOUND_VAR_MANAGER_H
#define CVC5__EXPR__BOUND_VAR_MANAGER_H

#include <string>
#include <unordered_set>

#include "expr/node.h"

namespace cvc5::internal {
  
enum class BoundVariableId
{
  SHADOW_ELIM,
  ARITH_RAN_NUMBER,
  EQ_RANGE_ELIM,
  QUANT_DT_EXPAND,
  QUANT_PRENEX,
  QUANT_MINISCOPE,
  QUANT_SYGUS_BUILTIN,
  SETS_FIRST_INDEX,
  SETS_SECOND_INDEX,
  BAGS_FIRST_INDEX,
  BAGS_SECOND_INDEX,
  STRINGS_RE_ELIM_CONCAT,
  STRINGS_RE_ELIM_STAR,
  STRINGS_INDEX,
  STRINGS_LENGTH,
  STRINGS_VALUE_FOR_LENGTH,
  SEQ_MODEL_VAR,
  UF_FUNCTION_ARG,
};

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, InferenceId i);

/**
 * Bound variable manager.
 *
 * This class is responsible for constructing BOUND_VARIABLE that are
 * canonical based on cache keys (Node). It does this using expression
 * attributes on these nodes.
 */
class BoundVarManager
{
 public:
  BoundVarManager();
  ~BoundVarManager();
  /**
   * Enable or disable keeping cache values. If we keep cache values, then
   * the bound variables returned by the methods below are deterministic in the
   * lifetime of the NodeManager we are using.
   */
  void enableKeepCacheValues(bool isEnabled = true);
  /**
   * Make a bound variable of type tn and name tn, cached based on (T, n),
   * where T is an attribute class of the form:
   *   expr::Attribute<id, Node>
   * This variable is unique for (T, n) during the lifetime of n. If
   * this bound variable manager is configured to keep cache values, then
   * n is added to the d_cacheVals set and survives in the lifetime of the
   * current node manager.
   *
   * Returns the bound variable.
   */
  template <class T>
  Node mkBoundVar(Node n, TypeNode tn)
  {
    T attr;
    if (n.hasAttribute(attr))
    {
      Assert(n.getAttribute(attr).getType() == tn);
      return n.getAttribute(attr);
    }
    Node v = NodeManager::currentNM()->mkBoundVar(tn);
    n.setAttribute(attr, v);
    // if we are keeping cache values, insert it to the set
    if (d_keepCacheVals)
    {
      d_cacheVals.insert(n);
    }
    return v;
  }
  /** Same as above, with a name for the bound variable. */
  template <class T>
  Node mkBoundVar(Node n, const std::string& name, TypeNode tn)
  {
    Node v = mkBoundVar<T>(n, tn);
    setNameAttr(v, name);
    return v;
  }
  //---------------------------------- utilities for computing Node hash
  /** get cache value from two nodes, returns SEXPR */
  static Node getCacheValue(TNode cv1, TNode cv2);
  /** get cache value from three nodes, returns SEXPR */
  static Node getCacheValue(TNode cv1, TNode cv2, TNode cv3);
  /** get cache value from two nodes and a size_t, returns SEXPR */
  static Node getCacheValue(TNode cv1, TNode cv2, size_t i);
  /** get cache value, returns a constant rational node */
  static Node getCacheValue(size_t i);
  /** get cache value, return SEXPR of cv and constant rational node */
  static Node getCacheValue(TNode cv, size_t i);
  //---------------------------------- end utilities for computing Node hash
 private:
  /** Set name of bound variable to name */
  static void setNameAttr(Node v, const std::string& name);
  /** Whether we keep cache values */
  bool d_keepCacheVals;
  /** The set of cache values we have used */
  std::unordered_set<Node> d_cacheVals;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__BOUND_VAR_MANAGER_H */
