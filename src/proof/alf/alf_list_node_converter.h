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
 * Implementation of ALF node tprocersion for list variables in DSL rules
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * Convert list variables in side conditions. This class tprocerts nodes
 * representing LFSC side condition programs to a form that prints properly
 * in LFSC. In particular, this node tprocerter gives consideration to
 * input variables that are "list" variables in the rewrite DSL.
 *
 * For example, for DSL rule:
 *   (define-rule bool-and-flatten
 *      ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
 *      (and xs (and b ys) zs) (and xs zs b ys))
 * This is a helper class used to compute the conclusion of this rule. This
 * class is used to turn
 *   (= (and xs (and b ys) zs) (and xs zs b ys))
 * into:
 *   (=
 *      (nary_concat
 *        f_and
 *        xs
 *        (and (and b ys) zs)
 *        true)
 *      (nary_elim
 *        f_and
 *        (nary_concat f_and xs (nary_concat f_and zs (and b ys) true) true)
 *        true)))
 * Where notice that the list variables xs, ys, zs are treated as lists to
 * concatenate instead of being subterms, according to the semantics of list
 * variables in the rewrite DSL. For exact definitions of nary_elim,
 * nary_concat, see the LFSC signature nary_programs.plf.
 *
 * This runs in two modes.
 * - If isPre is true, then the input is in its original form, and we add
 * applications of nary_elim.
 * - If isPre is false, then the input is in tprocerted form, and we add
 * applications of nary_concat.
 */
class AlfListNodeConverter : public NodeConverter
{
 public:
  AlfListNodeConverter(AlfNodeConverter& tproc);
  /** tprocert to internal */
  Node postConvert(Node n) override;

 private:
  /** The parent tprocerter, used for getting internal symbols and utilities */
  AlfNodeConverter& d_tproc;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
