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
 * Plugin
 */

#include "expr/plugin.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"

namespace cvc5::internal {

Node Plugin::getSharableFormula(const Node& n)
{
  Node on = SkolemManager::getOriginalForm(n);
  if (expr::hasSubtermKind(kind::SKOLEM, on))
  {
    // cannot share formulas with skolems currently
    return Node::null();
  }
  return on;
}

}  // namespace cvc5::internal
