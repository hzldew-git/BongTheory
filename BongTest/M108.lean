/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaMonotonicity

/-!
# M108 Beli 2009/2010, Lemmas 2.1--2.3 smoke tests
-/

namespace BongTest.M108

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable [localization : Bong.Beli2009AlphaLocalizationLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1))
    (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha s.pivotFin ≤ (w.toGoodBONG b.good).alpha s.localPivot :=
  b.beli2009Lemma21_le_segmentAlpha s w

example (b : BONG.GoodBONG q L (n + 2)) :
    Monotone b.alphaLeftEndpoint :=
  b.alphaLeftEndpoint_monotone

example (b : BONG.GoodBONG q L (n + 2)) :
    Antitone b.alphaRightEndpoint :=
  b.alphaRightEndpoint_antitone

example (b : BONG.GoodBONG q L (n + 2))
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (hsum : b.adjacentOrderSum i = b.adjacentOrderSum j) :
    BONG.GoodBONG.ConstantAdjacentSumConsequences b i j :=
  b.beli2009Corollary23 i j hij hsum

#print axioms Bong.BONG.GoodBONG.beli2009Lemma21_le_segmentAlpha
#print axioms Bong.BONG.GoodBONG.alphaLeftEndpoint_monotone
#print axioms Bong.BONG.GoodBONG.alphaRightEndpoint_antitone
#print axioms Bong.BONG.GoodBONG.beli2009Corollary23

end BongTest.M108
