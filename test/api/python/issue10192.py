###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Alex Ozdemir, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #4889
##

import cvc5
from cvc5 import *


s = cvc5.Solver()
s.setOption('produce-abducts', 'true')
s.setOption('incremental', 'false')
s.setLogic('QF_BV')

bitvec = s.mkBitVectorSort(2)
boolean = s.getBooleanSort()

x_0_L = s.mkConst(bitvec, 'x_0_L')
x_1_L = s.mkConst(bitvec, 'x_1_L')

const_2 = s.mkVar(bitvec, 'const_2')
start = s.mkVar(boolean, 'start')
eq = s.mkVar(boolean, 'eq')

Eq_x_0 = s.mkTerm(Kind.EQUAL, x_0_L, const_2)
Eq_x_1 = s.mkTerm(Kind.EQUAL, x_1_L, const_2)
And = s.mkTerm(Kind.AND, start, start)

g = s.mkGrammar([], [start, eq, const_2])

g.addAnyConstant(const_2)
g.addRules(start, [And, eq])
g.addRules(eq, [Eq_x_0, Eq_x_1])

print(g)

r = s.mkTerm(Kind.BITVECTOR_OR, x_0_L, x_1_L)

abd = s.getAbduct(s.mkTerm(Kind.EQUAL, r, s.mkBitVector(2, 0)), g)
print(abd)
