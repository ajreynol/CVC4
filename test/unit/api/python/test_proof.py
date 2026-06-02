###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for proof API.
#
# Obtained by translating test/unit/api/sort_black.cpp
##

import pytest
import cvc5
from cvc5 import Kind, ProofRule


@pytest.fixture
def tm():
    return cvc5.TermManager()
@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def create_proof(tm, solver):
    solver.setOption("produce-proofs", "true")

    uSort = tm.mkUninterpretedSort("u")
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()
    uToIntSort = tm.mkFunctionSort(uSort, intSort)
    intPredSort = tm.mkFunctionSort(intSort, boolSort)

    x = tm.mkConst(uSort, "x")
    y = tm.mkConst(uSort, "y")
    f = tm.mkConst(uToIntSort, "f")
    p = tm.mkConst(intPredSort, "p")
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    summ = tm.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)
    solver.assertFormula(tm.mkTerm(Kind.GT, zero, f_x))
    solver.assertFormula(tm.mkTerm(Kind.GT, zero, f_y))
    solver.assertFormula(tm.mkTerm(Kind.GT, summ, one))
    solver.assertFormula(p_0)
    solver.assertFormula(p_f_y.notTerm())
    assert solver.checkSat().isUnsat()

    return solver.getProof()[0]


def create_rewrite_proof(tm, solver):
    solver.setOption("produce-proofs", "true")
    solver.setOption("proof-granularity", "dsl-rewrite")
    int_sort = tm.getIntegerSort()
    x = tm.mkConst(int_sort, "x")
    zero = tm.mkInteger(0)
    geq = tm.mkTerm(Kind.GEQ, x, zero)
    leq = tm.mkTerm(Kind.LEQ, zero, x)
    solver.assertFormula(tm.mkTerm(Kind.DISTINCT, geq, leq))
    solver.checkSat()
    return solver.getProof()[0]


def create_theory_rewrite_proof(tm, solver):
    solver.setOption("produce-proofs", "true")
    solver.setOption("proof-granularity", "theory-rewrite")
    int_sort = tm.getIntegerSort()
    x = tm.mkConst(int_sort, "x")
    zero = tm.mkInteger(0)
    geq = tm.mkTerm(Kind.GEQ, x, zero)
    leq = tm.mkTerm(Kind.LEQ, zero, x)
    solver.assertFormula(tm.mkTerm(Kind.DISTINCT, geq, leq))
    solver.checkSat()
    return solver.getProof()[0]


def find_proof_with_rule(proof, rule):
    stack = [proof]
    while stack:
        current = stack.pop()
        if current.getRule() == rule:
            return current
        stack.extend(current.getChildren())
    return None


def has_argument_string_with_prefix(proof, prefix):
    stack = [proof]
    while stack:
        current = stack.pop()
        for i in range(len(current.getArguments())):
            if current.getArgumentString(i).startswith(prefix):
                return True
        stack.extend(current.getChildren())
    return False


def test_null_proof(solver):
  proof = cvc5.Proof()
  assert proof.getRule() == ProofRule.UNKNOWN
  assert hash(ProofRule.UNKNOWN) == hash(ProofRule.UNKNOWN)
  assert proof.getResult().isNull()
  assert len(proof.getChildren()) == 0
  assert len(proof.getArguments()) == 0
  with pytest.raises(RuntimeError):
      proof.getArgumentString(0)


def test_get_rule(tm, solver):
    proof = create_proof(tm, solver)
    rule = proof.getRule()
    assert rule == ProofRule.SCOPE


def test_get_rewrite_rule(tm, solver):
    proof = create_rewrite_proof(tm, solver)
    with pytest.raises(RuntimeError):
        proof.getRewriteRule()
    rule = None
    stack = [proof]
    while rule != ProofRule.DSL_REWRITE:
        proof = stack.pop()
        rule = proof.getRule()
        children = proof.getChildren()
        stack.extend(children)
    assert proof.getRewriteRule() is not None


def test_get_result(tm, solver):
    proof = create_proof(tm, solver)
    proof.getResult()


def test_get_children(tm, solver):
    proof = create_proof(tm, solver)
    children = proof.getChildren()
    assert len(children) > 0


def test_get_arguments(tm, solver):
    proof = create_proof(tm, solver)
    proof.getArguments()


def test_get_argument_string(tm, solver):
    proof = create_rewrite_proof(tm, solver)
    rewrite_proof = find_proof_with_rule(proof, ProofRule.DSL_REWRITE)
    assert rewrite_proof is not None
    args = rewrite_proof.getArguments()
    assert len(args) > 0
    assert rewrite_proof.getArgumentString(0) == rewrite_proof.getRewriteRule().name
    with pytest.raises(RuntimeError):
        rewrite_proof.getArgumentString(len(args))


def test_get_argument_string_theory_id(tm, solver):
    proof = create_theory_rewrite_proof(tm, solver)
    assert has_argument_string_with_prefix(proof, "THEORY_")


def test_eq(tm, solver):
    x = create_proof(tm, solver)
    y = x.getChildren()[0]
    z = cvc5.Proof()

    assert x == x
    assert not x != x
    assert not x == y
    assert x != y
    assert not (x == z)
    assert x != z

    assert hash(x) == hash(x)
