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
 * Function info for eager instantiation
 */

#include "theory/quantifiers/eager/fun_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

FunInfo::FunInfo(context::Context* c) : d_trie(c), d_count(c, 0) {}

void FunInfo::addRelevantDomain(size_t i, TNode r)
{
    //TODO
}

bool FunInfo::inRelevantDomain(size_t i, TNode r) const
{
    return false;
}

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

