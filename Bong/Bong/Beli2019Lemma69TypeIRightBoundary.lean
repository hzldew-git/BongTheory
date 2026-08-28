/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma63Right

/-!
# Beli (2019), Lemma 6.9(i): the concrete right boundary

The right-end form of Lemma 6.3 identifies the representation invariant just
after the last unequal order with the target alpha.  Target endpoint
monotonicity then puts that alpha strictly above the right-pivot cutoff.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Under `beta_p > 1`, the comparison defect immediately after the last
unequal order lies strictly above the right-pivot cutoff. -/
theorem lemma69_i_typeI_rightBoundary_gt_cutoff
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b)
    (hpivotAlpha : 1 < b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩) :
    (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
      a.truncatedPrefixDefect b 1
        (D.profile.last + 1) (D.profile.last + 1) := by
  have hlastBound := D.profile.lastDifference.bound
  have hpivotLtLast : P.pivot < D.profile.last := by
    have hpivotLast := P.pivot_le_last_previous
    rcases P.pivot_odd with ⟨d, hd⟩
    omega
  by_cases hfull : D.profile.last + 1 = n + 2
  · have htop : a.truncatedPrefixDefect b 1
        (D.profile.last + 1) (D.profile.last + 1) = ⊤ := by
      simpa only [hfull] using a.truncatedPrefixDefect_full_eq_top b
    rw [htop]
    exact WithTop.coe_lt_top _
  · have hboundaryBound : D.profile.last + 1 < n + 2 := by omega
    let boundary : RepresentationIndex (n + 2) (n + 2) :=
      ⟨D.profile.last + 1, by omega, hboundaryBound, by omega⟩
    let p : Fin (n + 1) := ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      omega⟩
    let lastAlpha : Fin (n + 1) := ⟨D.profile.last, by omega⟩
    have hsuffix : ∀ k, boundary.val ≤ k → k < n + 2 →
        a.orderSequence.entryOrZero k =
          b.orderSequence.entryOrZero k := by
      intro k hk hkn
      exact D.profile.lastDifference.after k (by
        simp only [boundary] at hk
        omega) hkn
    have hright := a.beli2019Lemma63_sameRank_right b hdefect
      boundary hsuffix
    have hcomparison : (b.alphaValue lastAlpha : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1
          (D.profile.last + 1) (D.profile.last + 1) := by
      have hcondition := hdefect boundary
      rw [a.coe_representationAlphaValue b boundary, hright] at hcondition
      have halphaIndex :
          (⟨D.profile.last + 1 - 1, by omega⟩ : Fin (n + 1)) =
            lastAlpha := by
        apply Fin.ext
        simp only [lastAlpha]
        omega
      simpa only [boundary, halphaIndex] using hcondition
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hlastDistance : Even (D.profile.last - D.anchor) := by
      have hanchorLast : D.anchor < D.profile.last := by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        have hpivotLast := P.pivot_le_last_previous
        omega
      exact (D.profile.rightProfile hanchorLast).1
    have hpivotNextEven : Even (P.pivot + 1) := by
      rcases P.pivot_odd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hpivotNextDistance : Even (P.pivot + 1 - D.anchor) := by
      rcases hpivotNextEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega⟩
    have htargetLast := C.target_from_anchor D.profile.last
      D.profile.anchor_le_last le_rfl hlastDistance
    have htargetPivotNext := C.target_from_anchor (P.pivot + 1) (by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega)
      (by
        omega) hpivotNextDistance
    have htargetEvenEq :
        b.orderSequence.entryOrZero D.profile.last =
          b.orderSequence.entryOrZero (P.pivot + 1) :=
      htargetLast.trans htargetPivotNext.symm
    have hpivotLastAlpha : p ≤ lastAlpha := by
      change p.val ≤ lastAlpha.val
      simp only [p, lastAlpha]
      have hpivotLast := P.pivot_le_last_previous
      omega
    have hendpoint := b.alphaLeftEndpoint_monotone hpivotLastAlpha
    unfold alphaLeftEndpoint at hendpoint
    have hpivotOrder : b.order p.castSucc =
        b.orderSequence.entryOrZero P.pivot := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      apply congrArg b.order
      apply Fin.ext
      rfl
    have hlastOrder : b.order lastAlpha.castSucc =
        b.orderSequence.entryOrZero D.profile.last := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      apply congrArg b.order
      apply Fin.ext
      rfl
    rw [hpivotOrder, hlastOrder, htargetEvenEq] at hendpoint
    have hpivotAlpha' : 1 < b.alphaValue p := by
      simpa only [p] using hpivotAlpha
    have hcut : b.typeIRightPivotCutoff P.pivot <
        b.alphaValue lastAlpha := by
      unfold typeIRightPivotCutoff
      push_cast
      linarith
    have hcutTop : (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        (b.alphaValue lastAlpha : WithTop ℚ) := by
      exact_mod_cast hcut
    exact hcutTop.trans_le hcomparison

end BONG.GoodBONG

end Bong
