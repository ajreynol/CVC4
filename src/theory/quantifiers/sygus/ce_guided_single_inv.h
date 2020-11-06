/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H
#define CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H

#include "context/cdlist.h"
#include "expr/subs.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/inst_match_trie.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv_sol.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;

// this class infers whether a conjecture is single invocation (Reynolds et al CAV 2015), and sets up the
// counterexample-guided quantifier instantiation utility (d_cinst), and methods for solution
// reconstruction (d_sol).
// It also has more advanced techniques for:
// (1) partitioning a conjecture into single invocation / non-single invocation portions for invariant synthesis,
// (2) inferring whether the conjecture corresponds to a deterministic transistion system (by utility d_ti).
// For these techniques, we may generate a template (d_templ) which specifies a restricted
// solution space. We may in turn embed this template as a SyGuS grammar.
class CegSingleInv
{
 private:
  //presolve
  void collectPresolveEqTerms( Node n,
                               std::map< Node, std::vector< Node > >& teq );
  void getPresolveEqConjuncts( std::vector< Node >& vars,
                               std::vector< Node >& terms,
                               std::map< Node, std::vector< Node > >& teq,
                               Node n, std::vector< Node >& conj );
 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  // single invocation inference utility
  SingleInvocationPartition* d_sip;
  // solution reconstruction
  CegSingleInvSol* d_sol;

  // list of skolems for each argument of programs
  std::vector<Node> d_single_inv_arg_sk;
  // program to solution index
  std::map<Node, unsigned> d_prog_to_sol_index;
  // original conjecture
  Node d_orig_conjecture;

 public:
  //---------------------------------representation of the solution
  /**
   * The list of instantiations that suffice to show the first-order equivalent
   * of the negated synthesis conjecture is unsatisfiable.
   */
  std::vector<std::vector<Node> > d_inst;
  /**
   * The list of instantiation lemmas, corresponding to instantiations of the
   * first order conjecture for the term vectors above.
   */
  std::vector<Node> d_instConds;
  /** The solutions, without reconstruction to syntax */
  std::vector<Node> d_solutions;
  /** The solutions, after reconstruction to syntax */
  std::vector<Node> d_rcSolutions;
  /** is solved */
  bool d_isSolved;
  //---------------------------------end representation of the solution

 private:
  Node d_simp_quant;
  // are we single invocation?
  bool d_single_invocation;
  // single invocation portion of quantified formula
  Node d_single_inv;
  
 public:
  CegSingleInv(QuantifiersEngine* qe);
  ~CegSingleInv();

  // get simplified conjecture
  Node getSimplifiedConjecture() { return d_simp_quant; }
 public:
  // initialize this class for synthesis conjecture q
  void initialize( Node q );
  /** finish initialize
   *
   * This method sets up final decisions about whether to use single invocation
   * techniques.
   *
   * The argument syntaxRestricted is whether the syntax for solutions for the
   * initialized conjecture is restricted.
   */
  void finishInit(bool syntaxRestricted);
  /** solve
   *
   * If single invocation techniques are being used, it solves
   * the first order form of the negated synthesis conjecture using a fresh
   * copy of the SMT engine. This method returns true if it has successfully
   * found a solution to the synthesis conjecture using this method.
   */
  bool solve();
  /**
   * Get solution for the index^th function to synthesize of the conjecture
   * this class was initialized with.
   */
  Node getSolution(size_t sol_index,
                   TypeNode stn,
                   int& reconstructed,
                   bool rconsSygus = true);
  //reconstruct to syntax
  Node reconstructToSyntax( Node s, TypeNode stn, int& reconstructed,
                            bool rconsSygus = true );
  // is single invocation
  bool isSingleInvocation() const { return !d_single_inv.isNull(); }
  /** preregister conjecture */
  void preregisterConjecture( Node q );

 private:
  /** solve trivial
   *
   * If this method returns true, it sets d_isSolved to true and adds
   * t1 ... tn to d_inst if it can be shown that (forall x1 ... xn. P) is
   * unsatisfiable for instantiation {x1 -> t1 ... xn -> tn}.
   */
  bool solveTrivial(Node q);
  /**
   * Get solution from inst
   */
  Node getSolutionFromInst(size_t index);
  /**
   * Set solution
   */
  void setSolution();
  /** The conjecture */
  Node d_quant;
  //-------------- decomposed conjecture
  /** All functions */
  std::vector<Node> d_funs;
  /** Unsolved functions */
  std::vector<Node> d_unsolvedf;
  /** Mapping of solved functions */
  Subs d_solvedf;
  //-------------- end decomposed conjecture
};

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
