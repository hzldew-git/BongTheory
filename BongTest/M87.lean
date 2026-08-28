/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma43

/-!
# M87 Beli 2003, Lemma 4.3 smoke tests
-/

namespace BongTest.M87

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (X : BONG.OrthogonalBasisData q n) (i : Fin n) :
    X.value i ≠ 0 :=
  X.value_ne_zero i

example (X : BONG.OrthogonalBasisData q n) (b : BONG V q L n)
    (h : X.IsRealizedBy b) : X.HasAdjacentBONGs :=
  X.hasAdjacentBONGs_of_isRealizedBy h

example (X : BONG.OrthogonalBasisData q n) (h : X.HasGoodRealization) :
    X.HasAdjacentBONGs ∧ X.HasWeakTwoStepOrder :=
  X.conditions_of_hasGoodRealization h

variable [BeliLemma43ConstructionLaws.{u, v} K]

example (X : BONG.OrthogonalBasisData q n) :
    X.HasGoodRealization ↔
      X.HasAdjacentBONGs ∧ X.HasWeakTwoStepOrder :=
  X.hasGoodRealization_iff

example (b : BONG V q L n) (hgood : b.IsGood) :
    ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
        (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
      b.IsPutTogether M.toOrthogonalDecomposition c ∧
        BONG.AllBinaryComponentsImproper M c :=
  b.beliLemma43_iii hgood

variable [BONGStructuralLaws.{u, v} K]

example (X : BONG.OrthogonalBasisData q n) :
    X.HasPropertyARealization ↔
      X.HasAdjacentBONGs ∧ X.HasStrictTwoStepOrder :=
  X.hasPropertyARealization_iff

#print axioms Bong.BONG.OrthogonalBasisData.value_ne_zero
#print axioms Bong.BONG.OrthogonalBasisData.hasAdjacentBONGs_of_isRealizedBy
#print axioms Bong.BONG.OrthogonalBasisData.hasGoodRealization_iff
#print axioms Bong.BONG.OrthogonalBasisData.hasPropertyARealization_iff
#print axioms Bong.BONG.beliLemma43_iii

end

end BongTest.M87
