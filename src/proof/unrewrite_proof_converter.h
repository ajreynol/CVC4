/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__UNREWRITE_PROOF_CONVERTER_H
#define CVC5__PROOF__UNREWRITE_PROOF_CONVERTER_H

#include "expr/node.h"
#include "proof/proof_node_converter.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofChecker;

/**
 * A callback class for converting proofs to those where theory rewriting is
 * not performed on literals.
 */
class UnrewriteConverterCallback : public ProofNodeConverterCallback,
                                     protected EnvObj
{
 public:
  UnrewriteConverterCallback(Env& env);
  virtual ~UnrewriteConverterCallback() {}
  /**
   * This converts all proofs of formulas F into proofs where the theory
   * literals are not rewritten.
   */
  Node convert(Node res,
               ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               CDProof* cdp) override;

 private:
  /**
   * Try to prove expected via the given rule, children, and arguments. Return
   * true if this proves expected, otherwise we return false and set newRes
   * to what was proven by (id, children, args).
   *
   * If we return true, we add the step (id, children, args) to cdp.
   */
  bool tryWith(ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node expected,
               Node& newRes,
               CDProof* cdp);
  /** The proof checker we are using */
  ProofChecker* d_pc;
};

}  // namespace cvc5::internal

#endif
