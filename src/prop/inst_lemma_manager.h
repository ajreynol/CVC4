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

#include "cvc5_private.h"

#ifndef CVC5__PROP__INST_LEMMA_MANAGER_H
#define CVC5__PROP__INST_LEMMA_MANAGER_H

#include <memory>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace prop {

/**
 * This class manages the mapping between quantified formulas and the
 * instantiation lemmas that were generated for them. It is used to manage
 * which instantiation lemmas are relevant in the current context, namely an
 * instantiation lemma (=> q body) for quantified formula q is relevant when q
 * is asserted.
 *
 * This is the analog of SkolemDefManager for instantiation lemmas: instead of
 * activating a skolem definition when its skolem appears in an asserted
 * literal, it activates the instantiation lemmas of a quantified formula when
 * that quantified formula is asserted.
 *
 * It tracks (in a SAT-context-dependent manner) which quantified formulas are
 * "active", i.e. have been asserted in the current SAT context.
 */
class InstLemmaManager
{
  using NodeList = context::CDList<Node>;
  using NodeListMap =
      context::CDHashMap<Node, std::shared_ptr<NodeList>>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  InstLemmaManager(context::Context* context,
                   context::UserContext* userContext);
  ~InstLemmaManager();

  /**
   * Notify that lem is an instantiation lemma associated with quantified
   * formula q. This records the lemma. If q is already active in the current
   * SAT context, lem is added to activatedLemmas so that it can be activated
   * immediately.
   *
   * @param q The quantified formula the lemma was generated for
   * @param lem The instantiation lemma
   * @param activatedLemmas The list to add lem to if q is already active
   */
  void notifyInstLemma(TNode q, Node lem, std::vector<TNode>& activatedLemmas);

  /**
   * Notify that the given literal has been asserted. If literal is a quantified
   * formula that has not yet been marked active in the current SAT context,
   * it is marked active and all of its recorded instantiation lemmas are added
   * to activatedLemmas.
   *
   * @param literal The literal that became asserted
   * @param activatedLemmas The list to add activated instantiation lemmas to
   */
  void notifyAsserted(TNode literal, std::vector<TNode>& activatedLemmas);

 private:
  /** Get (or make) the lemma list for quantified formula q */
  NodeList* getOrMkList(TNode q);
  /** The user context */
  context::UserContext* d_userContext;
  /** quantified formulas to their instantiation lemmas (user-context) */
  NodeListMap d_qlemmas;
  /** set of active (asserted) quantified formulas (SAT-context) */
  NodeSet d_qactive;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__INST_LEMMA_MANAGER_H */
