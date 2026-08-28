/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightBoundary
import Bong.Bong.Beli2019Lemma69TypeIRightSecondary
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint

/-!
# Beli (2019), Lemma 6.9(i): the complete type-I right pivot

The concrete right form of Lemma 6.3 supplies the comparison boundary.  An
interior maximal pivot has a strictly positive secondary candidate, while
the terminal pivot is handled by the odd adjacent-product argument.  These
two branches close the target alpha estimate without a paper-specific law.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target alpha at the maximal type-I right pivot is at most one. -/
theorem beli2019Lemma69_i_typeI_rightPivotAlpha
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b) :
    b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  have hlastBound := D.profile.lastDifference.bound
  let p : Fin (n + 1) := ⟨P.pivot, by
    have hpivotLast := P.pivot_le_last_previous
    omega⟩
  by_contra hnot
  have hpivotAlpha : 1 < b.alphaValue p := by
    simpa only [p] using lt_of_not_ge hnot
  have hboundary := lemma69_i_typeI_rightBoundary_gt_cutoff
    a b D C hfirst P hdefect (by simpa only [p] using hpivotAlpha)
  have hle :=
    beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_secondary_case
      (alphaV := alpha) (alphaW := alpha)
      a b D C hfirst P hdefect hboundary (by
        intro hi hsecondary
        by_cases hendpoint : P.pivot + 1 = D.profile.last
        · exact lemma69_i_typeI_rightPivotAlpha_of_secondary_of_endpoint
            (alphaV := alpha) (alphaW := alpha)
            a b D C hfirst P hendpoint hi hsecondary
        · have hanchorEven : Even D.anchor := by
            by_cases heq : D.profile.first = D.anchor
            · rw [← heq, hfirst]
              exact ⟨0, by omega⟩
            · have hlt : D.profile.first < D.anchor :=
                lt_of_le_of_ne D.profile.first_le_anchor heq
              simpa only [hfirst, Nat.sub_zero] using
                (D.profile.leftProfile hlt).1
          have hlastDistance : Even (D.profile.last - D.anchor) := by
            exact (D.profile.rightProfile (by
              have hanchorRight := C.anchor_le_right
              have hnextPivot := P.next_le_pivot
              have hpivotLast := P.pivot_le_last_previous
              omega)).1
          have hlastEven : Even D.profile.last := by
            rcases hanchorEven with ⟨d, hd⟩
            rcases hlastDistance with ⟨e, he⟩
            exact ⟨d + e, by
              have hanchorLast := D.profile.anchor_le_last
              omega⟩
          have hpivotNextEven : Even (P.pivot + 1) := by
            rcases P.pivot_odd with ⟨d, hd⟩
            exact ⟨d + 1, by omega⟩
          have hpivotInterior : P.pivot + 2 < D.profile.last := by
            have hpivotLast := P.pivot_le_last_previous
            rcases hpivotNextEven with ⟨d, hd⟩
            rcases hlastEven with ⟨e, he⟩
            omega
          have hpositive :=
            lemma69_i_typeI_rightPivot_secondary_pos_of_interior
              (alphaV := alpha) (alphaW := alpha)
              a b D C hfirst P hpivotInterior hi
          exact (not_le_of_gt hpositive hsecondary).elim)
  exact (not_le_of_gt hpivotAlpha) (by simpa only [p] using hle)

end BONG.GoodBONG

end Bong
