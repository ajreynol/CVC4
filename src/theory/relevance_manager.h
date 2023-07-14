/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__RELEVANCE_MANAGER__H
#define CVC5__THEORY__RELEVANCE_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/term_context.h"
#include "theory/difficulty_manager.h"
#include "theory/theory_engine_module.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

/**
 * This class manages queries related to relevance of asserted literals.
 * In particular, note the following definition:
 *
 * Let F be a formula, and let L = { l_1, ..., l_n } be a set of
 * literals that propositionally entail it. A "relevant selection of L with
 * respect to F" is a subset of L that also propositionally entails F.
 *
 * This class computes a relevant selection of the current assertion stack
 * at FULL effort with respect to the input formula + theory lemmas that are
 * critical to justify (see LemmaProperty::NEEDS_JUSTIFY). By default, theory
 * lemmas are not critical to justify; in fact, all T-valid theory lemmas
 * are not critical to justify, since they are guaranteed to be satisfied in
 * all inputs. However, some theory lemmas that introduce skolems need
 * justification.
 *
 * As an example of such a lemma, take the example input formula:
 *   (and (exists ((x Int)) (P x)) (not (P 0)))
 * A skolemization lemma like the following needs justification:
 *   (=> (exists ((x Int)) (P x)) (P k))
 * Intuitively, this is because the satisfiability of the existential above is
 * being deferred to the satisfiability of (P k) where k is fresh. Thus,
 * a relevant selection must include both (exists ((x Int)) (P x)) and (P k)
 * in this example.
 *
 * Theories are responsible for marking such lemmas using the NEEDS_JUSTIFY
 * property when calling OutputChannel::lemma.
 *
 * Notice that this class has some relation to the justification decision
 * heuristic (--decision=justification), which constructs a relevant selection
 * of the input formula by construction. This class is orthogonal to this
 * method, since it computes relevant selection *after* a full assignment. Thus
 * its main advantage with respect to decision=justification is that it can be
 * used in combination with any SAT decision heuristic.
 *
 * Internally, this class stores the input assertions and can be asked if an
 * asserted literal is part of the current relevant selection. The relevant
 * selection is computed lazily, i.e. only when someone asks if a literal is
 * relevant, and only at most once per FULL effort check.
 */
class RelevanceManager : public TheoryEngineModule
{
  using RlvPair = std::pair<Node, uint32_t>;
  using RlvPairHashFunction = PairHashFunction<Node, uint32_t, std::hash<Node>>;
  using NodeList = context::CDList<Node>;
  using NodeMap = context::CDHashMap<Node, Node>;
  using NodeListMap = context::CDHashMap<Node, std::shared_ptr<NodeList>>;
  using NodeSet = context::CDHashSet<Node>;
  using RlvPairIntMap =
      context::CDHashMap<RlvPair, int32_t, RlvPairHashFunction>;

 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  RelevanceManager(Env& env, TheoryEngine* engine);
  /**
   * Notify (preprocessed) assertions. This is called for input formulas or
   * lemmas that need justification that have been fully processed, just before
   * adding them to the PropEngine.
   *
   * @param assertions The assertions
   * @param isInput Whether the assertions are preprocessed input assertions;
   * this flag is false for lemmas.
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions,
                                    bool isInput);
  /** Singleton version of above */
  void notifyPreprocessedAssertion(Node n, bool isInput);
  /**
   * Begin round, called at the beginning of a full effort check in
   * TheoryEngine.
   */
  void check(Theory::Effort effort) override;
  /** End round, called at the end of a full effort check in TheoryEngine. */
  void postCheck(Theory::Effort effort) override;
  /**
   * Is lit part of the current relevant selection? This computes the set of
   * relevant assertions if not already done so. This call is valid during a
   * full effort check in TheoryEngine, or after TheoryEngine has terminated
   * with "sat". This means that theories can query this during FULL or
   * LAST_CALL efforts, through the Valuation class.
   */
  bool isRelevant(TNode lit);
  /**
   * Get the explanation for why lit is relevant. This returns the
   * preprocessed formula that was the reason why the literal was
   * asserted in the current context, which must be an input formula or
   * theory lemma that requires justification.
   *
   * Note this method can be called before full effort check. It partially
   * caches the results of justifying input formulas that contain lit.
   */
  TNode getExplanationForRelevant(TNode lit);
  /**
   * Get the explanation for why the atom of lit is asserted. This returns a
   * preprocessed formula whose justification includes lit. If multiple
   * formulas are justified by lit, then the first one in the list of
   * input formulas / theory lemmas is returned.
   *
   * In contrast to getExplanationForRelevant, this method may return
   * theory lemmas that do not require justification. Also unlike the above
   * method, it is intended to be called during full effort check only.
   */
  TNode getExplanationForAsserted(TNode lit);
  /**
   * Get the current relevant selection (see above). This computes this set
   * if not already done so. This call is valid during a full effort check in
   * TheoryEngine, or after TheoryEngine has terminated with "sat". This method
   * sets the flag success to false if we failed to compute relevant
   * assertions, which occurs if the values from the SAT solver do not satisfy
   * the assertions we are notified of. This should never happen.
   *
   * The value of this return is only valid if success was not updated to false.
   *
   * Note that this returns a context-independent set to the user, which
   * copies the assertions.
   */
  std::unordered_set<TNode> getRelevantAssertions(bool& success);
  /**
   * Called when lem with associated skolem lemmas skLemmas is added as a
   * lemma to the SAT solver.
   *
   * This updates the list of input assertions and lemmas, as well as
   * incrementing the difficulty if we are tracking difficulty based on lemmas.
   *
   * @param lem The lemma.
   * @param skAsserts Its associated skolem lemmas.
   */
  void notifyLemma(TNode n,
                   theory::LemmaProperty p,
                   const std::vector<Node>& skAsserts,
                   const std::vector<Node>& sks) override;
  /** Needs candidate model, return true if the method below requires calling */
  bool needsCandidateModel() override;
  /** Notify that m is a (candidate) model, for difficulty measurements */
  void notifyCandidateModel(TheoryModel* m) override;
  /**
   * Get difficulty map
   *
   * @param dmap The difficulty map to populate.
   * @param includeLemmas Whether to include difficulty of lemmas in the domain
   * of dmap.
   */
  void getDifficultyMap(std::map<Node, Node>& dmap, bool includeLemmas);
  /**
   * Get the current difficulty for input formula or lemma n.
   */
  uint64_t getCurrentDifficulty(const Node& n) const;

 private:
  /**
   * Called when an input assertion is added, this populates d_atomMap.
   */
  void addInputToAtomsMap(TNode input, std::unordered_set<TNode>& visited);
  /**
   * Compute relevance for input assertion input. This returns false and
   * sets d_fullEffortCheckFail to true if we are at full effort and input
   * fails to be computed.
   */
  bool computeRelevanceFor(TNode input);
  /**
   * Add the set of assertions to the formulas known to this class. This
   * method handles optimizations such as breaking apart top-level applications
   * of and.
   */
  void addAssertionsInternal(std::vector<Node>& toProcess,
                             context::CDList<Node>& list);
  /** compute the relevant selection */
  void computeRelevance();
  /**
   * Justify formula n. To "justify" means we have added literals to our
   * relevant selection set (d_rset) whose current values ensure that n
   * evaluates to true or false.
   *
   * This method returns 1 if we justified n to be true, -1 means
   * justified n to be false, 0 means n could not be justified.
   *
   * @param n The formula to justify
   * @param needsJustify True if n is an input formula, or a lemma that needs
   * justification. If this flag is false, we do not add literals to the
   * relevant set.
   */
  int32_t justify(TNode n, bool needsJustify);
  /**
   * Update justify last child. This method is a helper function for justify,
   * which is called at the moment that Boolean connective formula cur
   * has a new child that has been computed in the justify cache maintained
   * by this class.
   *
   * @param cur The Boolean connective formula
   * @param childrenJustify The values of the previous children (not including
   * the current one)
   * @return True if we wish to visit the next child. If this is the case, then
   * the justify value of the current child is added to childrenJustify.
   */
  bool updateJustifyLastChild(const RlvPair& cur,
                              std::vector<int32_t>& childrenJustify);
  /** Return the explanation for why atom is asserted, if it exists */
  TNode getExpForAssertedInternal(TNode atom) const;
  /** Get the list of assertions that contain atom */
  NodeList* getInputListFor(TNode atom, bool doMake = true);
  /** The valuation object, used to query current value of theory literals */
  Valuation d_val;
  /** The input assertions */
  NodeList d_input;
  /** The lemmas */
  NodeList d_lemmas;
  /** Map from atoms to the list of input assertions that are contained in */
  NodeListMap d_atomMap;
  /**
   * The current relevant selection, SAT-context dependent, includes
   * literals that are definitely relevant in this context.
   */
  NodeSet d_rset;
  /** Are we in a full effort check? */
  bool d_inFullEffortCheck;
  /** Have we computed relevance for input formulas at full effort? */
  bool d_computedRelevance;
  /** Have we computed relevance for input formulas lemmas at full effort? */
  bool d_computedRelevanceForLemmas;
  /**
   * Did we succeed in computing the relevant selection? If this is false, there
   * was a syncronization issue between the input formula and the satisfying
   * assignment since this class found that the input formula was not satisfied
   * by the assignment. This should never happen, but if it does, this class
   * aborts and indicates that all literals are relevant.
   *
   * This flag is only valid at FULL effort.
   */
  bool d_success;
  /**
   * Whether we have miniscoped top-level AND of assertions, which is done
   * as an optimization. This is disabled if e.g. we are computing difficulty,
   * which requires preserving the original form of the preprocessed
   * assertions.
   */
  bool d_miniscopeTopLevel;
  /**
   * Map from asserted literals to the assertion in d_input or d_lemmas that is
   * the reason why that literal is currently asserted. The domain of this
   * map is a superset of d_rset.
   */
  NodeMap d_assertExp;
  /** For computing polarity on terms */
  PolarityTermContext d_ptctx;
  /**
   * Set of nodes that we have justified (SAT context dependent). This is SAT
   * context dependent to avoid repeated calls to justify for uses of
   * the relevance manager at standard effort. Notice that we pair each node
   * with its polarity. We take into account the polarity of the node when
   * computing relevance, where a node is only relevant if it is asserted
   * and either does not have a polarity in the overall formula, or if its
   * asserted value matches its polarity.
   */
  RlvPairIntMap d_jcache;
  /** Difficulty module */
  std::unique_ptr<DifficultyManager> d_dman;
  /** Lemmas added during a full effort check */
  std::unordered_set<Node> d_currLemmas;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
