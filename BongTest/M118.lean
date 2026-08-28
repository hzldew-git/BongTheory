/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009FinalRemarks

/-!
# M118 Beli 2009/2010, final Section 5 remarks smoke tests
-/

namespace BongTest.M118

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : BONG.GoodBONG q L (n + 2)) (i : Fin (n + 1)) : True := by
  have _ := b.beli2009Section5_recursiveAlphaFormula i
  trivial

example (a : Fin (n + 1) → Kˣ) :
    Beli2009BinaryReachable (K := K) a a :=
  beli2009BinaryReachable_refl a

section FieldSpecificConclusions

variable [Beli2009BinaryTransformationLaws.{u, v} (K := K)]

example (a b : BONG.GoodBONG q L (n + 1))
    (h : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i)) :
    ClassificationConditions a b :=
  beli2009Section5_binaryTransformations_necessary a b h

example : True := by
  have _ := beli2009Section5_binaryTransformationDichotomy
    (K := K)
  trivial

example (htwoAdic : ramificationIndex K = 1)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) : True := by
  have _ := beli2009Section5_q2Counterexample
    (K := K) htwoAdic hres
  trivial

end FieldSpecificConclusions

#print axioms Bong.BONG.GoodBONG.beli2009Section5_recursiveAlphaFormula
#print axioms Bong.beli2009BinaryReachable_refl
#print axioms Bong.beli2009Section5_binaryTransformations_necessary
#print axioms Bong.beli2009Section5_residueTwoParametricCounterexample
#print axioms Bong.beli2009Section5_binaryTransformationDichotomy
#print axioms Bong.beli2009Section5_q2Counterexample

end BongTest.M118
