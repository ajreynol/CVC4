/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Instantiation lemma manager.
 */

#include "prop/inst_lemma_manager.h"

namespace cvc5::internal {
namespace prop {

InstLemmaManager::InstLemmaManager(context::Context* context,
                                   context::UserContext* userContext)
    : d_userContext(userContext), d_qlemmas(userContext), d_qactive(context)
{
}

InstLemmaManager::~InstLemmaManager() {}

InstLemmaManager::NodeList* InstLemmaManager::getOrMkList(TNode q)
{
  NodeListMap::iterator it = d_qlemmas.find(q);
  if (it != d_qlemmas.end())
  {
    return it->second.get();
  }
  std::shared_ptr<NodeList> lems = std::make_shared<NodeList>(d_userContext);
  d_qlemmas.insert(q, lems);
  return lems.get();
}

void InstLemmaManager::notifyInstLemma(TNode q, Node lem)
{
  Trace("inst-lemma-mgr") << "notifyInstLemma: " << lem << " for " << q
                          << std::endl;
  getOrMkList(q)->push_back(lem);
}

void InstLemmaManager::notifyAsserted(TNode literal,
                                      std::vector<TNode>& revisitLemmas)
{
  // we only care about asserted quantified formulas
  if (literal.getKind() != Kind::FORALL)
  {
    return;
  }
  if (d_qactive.find(literal) != d_qactive.end())
  {
    // already active in the current SAT context, no need to revisit again
    return;
  }
  Trace("inst-lemma-mgr") << "notifyAsserted: " << literal << std::endl;
  d_qactive.insert(literal);
  NodeListMap::iterator it = d_qlemmas.find(literal);
  if (it != d_qlemmas.end())
  {
    for (const Node& lem : *it->second)
    {
      Trace("inst-lemma-mgr") << "...revisit " << lem << std::endl;
      revisitLemmas.push_back(lem);
    }
  }
}

}  // namespace prop
}  // namespace cvc5::internal
