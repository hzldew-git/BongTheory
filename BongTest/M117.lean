/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryRemarks

/-!
# M117 Beli 2009/2010, Lemma 5.1 and Remark 5.2 smoke tests
-/

namespace BongTest.M117

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    [Beli2009BinaryNormContainmentLaws (K := K)] : True := by
  have _ := beli2009Lemma51 (K := K) a ha
  trivial

example (b : BONG.GoodBONG q L 2)
    [Beli2009BinaryNormContainmentLaws (K := K)] : True := by
  have _ := b.beli2009Remark52
  trivial

#print axioms Bong.Dyadic.quadraticDefect_eq_zero_of_odd_ordUnit
#print axioms Bong.beli2009BinaryAlphaCongruenceGroup_spec
#print axioms Bong.quadraticNormValuationClassSubgroup_mul_square
#print axioms Bong.beli2009Lemma51
#print axioms Bong.BONG.GoodBONG.binaryAlphaCut_parameter_eq
#print axioms Bong.BONG.GoodBONG.beli2009Remark52

end BongTest.M117
