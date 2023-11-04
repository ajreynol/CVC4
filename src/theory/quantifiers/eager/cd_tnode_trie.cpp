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
 * Eager term index
 */

#include "theory/quantifiers/eager/cd_tnode_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CDTNodeTrie::CDTNodeTrie(context::Context* c) : d_reps(c), d_repChildren(c), d_repSize(c, 0) {}

void CDTNodeTrie::add(CDTNodeTrieAllocator* a, const std::vector<TNode>& args, TNode t)
{
}

CDTNodeTrieAllocator::CDTNodeTrieAllocator(context::Context* c) : d_ctx(c) {}

CDTNodeTrie* CDTNodeTrieAllocator::alloc()
{
    d_alloc.emplace_back(std::unique_ptr<CDTNodeTrie>(new CDTNodeTrie(d_ctx)));
    return d_alloc.back().get();
}

CDTNodeTrieIterator::CDTNodeTrieIterator(CDTNodeTrieAllocator* a, QuantifiersState& qs, CDTNodeTrie* cdtnt) : d_alloc(a), d_qs(qs)
{
    setActive({cdtnt});
}
TNode CDTNodeTrieIterator::pushNextChild()
{
    return d_null;
}
bool CDTNodeTrieIterator::push(TNode r)
{
    return false;
}
void CDTNodeTrieIterator::pop()
{
}
TNode CDTNodeTrieIterator::getData()
{
    Assert (d_active!=nullptr);
    Assert (d_active->hasData());
    return d_active->getData();
}
void CDTNodeTrieIterator::setActive(const std::vector<CDTNodeTrie*>& active)
{
    Assert (!active.empty());
}

}
}
}
