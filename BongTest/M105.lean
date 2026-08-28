/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremThree

/-!
# M105 Beli 2003, Theorem 3 smoke tests
-/

namespace BongTest.M105

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n m : Nat}

example (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    ordUnit K (b.adjacentParameter i hi) =
      b.order ⟨i.1 + 1, hi⟩ - b.order i :=
  b.ordUnit_adjacentParameter i hi

variable [BeliLemma49Laws.{u, v} K] [BinarySpinorLocalLaws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]
  [BONG.BeliLemma66Laws.{u, v} K]
  [BONG.BeliLemma67Laws.{u, v} K]
  [BeliLemma411Laws.{u, v} K]
  [BeliLemma71Laws.{u, v} K] [BeliLemma72Laws K]
  [BeliLemma73Laws.{u, v} K]
  [BeliTheoremThreeLaws.{u, v} K]

example (b : BONG V q L m) (hgood : b.IsGood) :
    Lattice.SpinorNormIsUnitBounded q L ↔
      b.SatisfiesTheoremThreeConditions :=
  b.beliTheoremThree hgood

example (b : BONG V q L m) (hgood : b.IsGood)
    (hunit : Lattice.SpinorNormIsUnitBounded q L) :
    b.SatisfiesTheoremThreeConditions :=
  b.theoremThreeConditions_of_spinorNormIsUnitBounded hgood hunit

#print axioms Bong.BONG.ordUnit_adjacentParameter
#print axioms Bong.BONG.adjacentOrderGap_even_of_spinorGroup_le_unit
#print axioms Bong.BONG.twoStepParity_of_spinorNormIsUnitBounded
#print axioms Bong.BONG.spinorNormIsUnitBounded_of_theoremThreeConditions
#print axioms Bong.BONG.beliTheoremThree

end BongTest.M105
