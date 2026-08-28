/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightDefect
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 6.9(i): the type-I right-pivot alpha

This module closes the candidate analysis at the maximal right pivot once the
right comparison boundary and the interior secondary candidate are supplied.
The half-gap branch forces the target alpha to vanish, while capped-defect
propagation excludes the primary branch.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The representation index immediately after the odd type-I right pivot. -/
def typeIRightPivotIndex
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (P : Lemma69TypeIRightPivotData a b D C) :
    RepresentationIndex (n + 2) (n + 2) where
  val := P.pivot + 1
  pos := by
    rcases P.pivot_odd with ⟨d, hd⟩
    omega
  lt_large := by
    have hpivotLast := P.pivot_le_last_previous
    have hlastBound := D.profile.lastDifference.bound
    omega
  le_small := by
    have hpivotLast := P.pivot_le_last_previous
    have hlastBound := D.profile.lastDifference.bound
    omega

/-- Candidate elimination at the right pivot, conditional on the right
boundary seed and a proof that every nonpositive optional secondary
candidate already forces the desired alpha bound. -/
theorem beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_secondary_case
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b)
    (hboundary :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b 1
          (D.profile.last + 1) (D.profile.last + 1))
    (hsecondary : ∀ hi :
        1 < (typeIRightPivotIndex a b D C P).val ∧
          (typeIRightPivotIndex a b D C P).val + 1 < n + 2,
      a.representationSecondaryDefect b
          (typeIRightPivotIndex a b D C P) hi ≤ 0 →
        b.alphaValue ⟨P.pivot, by
          have hpivotLast := P.pivot_le_last_previous
          have hlastBound := D.profile.lastDifference.bound
          omega⟩ ≤ 1) :
    b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  have hlastBound := D.profile.lastDifference.bound
  have hpivotLast := P.pivot_le_last_previous
  have hpivotLtLast : P.pivot < D.profile.last := by
    rcases P.pivot_odd with ⟨d, hd⟩
    omega
  have hpivotBound : P.pivot < n + 1 := by omega
  have hpivotEntryBound : P.pivot < n + 2 := by omega
  have hpivotNextBound : P.pivot + 1 < n + 2 := by omega
  let p : Fin (n + 1) := ⟨P.pivot, hpivotBound⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    typeIRightPivotIndex a b D C P
  have hidxVal : idx.val = P.pivot + 1 := rfl
  have hidxPred : idx.val - 1 = P.pivot := by
    rw [hidxVal]
    omega
  have hpivotOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst P.pivot (by
      have hnextPivot := P.next_le_pivot
      omega) hpivotLtLast P.pivot_odd
  have hsum : b.orderSequence.prefixSum idx.val =
      a.orderSequence.prefixSum idx.val + 1 := by
    simpa only [idx, typeIRightPivotIndex] using
      lemma69_i_typeI_rightPivot_prefixSum a b D C hfirst P
  by_contra hnot
  have hpivotAlpha : 1 < b.alphaValue p := by
    simpa only [p] using lt_of_not_ge hnot
  have hcommon := lemma69_i_typeI_rightCommon_of_boundary
    (alphaV := alphaV) (alphaW := alphaW)
    a b D C hfirst P hpivotAlpha hboundary
  have htarget := lemma69_i_typeI_rightTargetLocal_gt_cutoff
    (alphaW := alphaW) a b D C hfirst P hpivotAlpha
    P.pivot le_rfl hpivotLtLast P.pivot_odd
  have htargetReverse :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        b.truncatedPrefixDefect b (-1) (P.pivot + 2) P.pivot := by
    rw [b.truncatedPrefixDefect_comm b (-1) (P.pivot + 2) P.pivot]
    exact htarget
  have hdom := a.truncatedPrefixDefect_domination b b
    1 (-1) (P.pivot + 2) (P.pivot + 2) P.pivot
  have hcritical :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b (-1) (P.pivot + 2) P.pivot :=
    (lt_min hcommon htargetReverse).trans_le (by simpa using hdom)
  have hprimaryFalse
      (hprimary : a.representationPrimaryDefect b idx ≤ 0) : False := by
    have hprimaryDefectLe :
        a.truncatedPrefixDefect b (-1) (idx.val + 1) (idx.val - 1) ≤
          (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) := by
      unfold representationPrimaryDefect at hprimary
      let z := a.truncatedPrefixDefect b (-1)
        (idx.val + 1) (idx.val - 1)
      have hz : z ≠ ⊤ := by
        intro htop
        rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
          (idx.val - 1) = z by rfl, htop] at hprimary
        simp at hprimary
      obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hz
      rw [show a.truncatedPrefixDefect b (-1) (idx.val + 1)
          (idx.val - 1) = z by rfl, ← hd] at hprimary ⊢
      norm_cast at hprimary ⊢
      push_cast at hprimary ⊢
      have hrightOrder : a.order ⟨idx.val, idx.lt_large⟩ =
          a.orderSequence.entryOrZero (P.pivot + 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          hpivotNextBound]
        apply congrArg a.order
        apply Fin.ext
        exact hidxVal
      have hleftOrder :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.orderSequence.entryOrZero P.pivot := by
        rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          hpivotEntryBound]
        apply congrArg b.order
        apply Fin.ext
        exact hidxPred
      rw [hrightOrder, hleftOrder] at hprimary
      have hnextOrder :
          (a.orderSequence.entryOrZero (P.pivot + 1) : ℚ) =
            (b.orderSequence.entryOrZero (P.pivot + 1) : ℚ) - 1 := by
        norm_cast
        omega
      unfold typeIRightPivotCutoff
      push_cast
      linarith
    have hindexOne : idx.val + 1 = P.pivot + 2 := by
      rw [hidxVal]
    rw [hindexOne, hidxPred] at hprimaryDefectLe
    exact (not_le_of_gt hcritical) hprimaryDefectLe
  have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    (alphaV := alphaV) (alphaW := alphaW) b idx.val
    (by simp only [idx, typeIRightPivotIndex]; omega)
    (by simp only [idx, typeIRightPivotIndex]; omega) hsum
  have hA := hdefect idx
  rw [hzeroDefect] at hA
  rw [a.coe_representationAlphaValue b idx,
    a.representationAlpha_eq_min_halfGap_prime b idx] at hA
  rcases min_le_iff.mp hA with hhalf | hprime
  · unfold representationHalfGap at hhalf
    norm_cast at hhalf
    simp only [Rat.divInt_eq_div] at hhalf
    have hnextOrder :
        b.order ⟨idx.val, by have := idx.le_small; omega⟩ =
          a.order ⟨idx.val, idx.lt_large⟩ + 1 := by
      have hbEntry : b.order ⟨idx.val, by have := idx.le_small; omega⟩ =
          b.orderSequence.entryOrZero (idx.val) :=
        (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (show idx.val < n + 2 by exact idx.lt_large)).symm
      have haEntry : a.order ⟨idx.val, idx.lt_large⟩ =
          a.orderSequence.entryOrZero idx.val :=
        (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          idx.lt_large).symm
      rw [hbEntry, haEntry, hidxVal]
      exact hpivotOrders.2
    have hgapUpper : b.orderGap p ≤
        1 - 2 * (ramificationIndex K : Int) := by
      unfold orderGap
      have hpCast : p.castSucc =
          (⟨idx.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [p, Fin.val_castSucc]
        exact hidxPred.symm
      have hpSucc : p.succ =
          (⟨idx.val, idx.lt_large⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [p, Fin.val_succ]
        exact hidxVal.symm
      rw [hpCast, hpSucc]
      have hdiffQ :
          ((a.order ⟨idx.val, idx.lt_large⟩ -
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
              Int) : ℚ) ≤ -(2 * (ramificationIndex K : ℚ)) := by
        linarith [hhalf]
      have hdiffInt :
          a.order ⟨idx.val, idx.lt_large⟩ -
              b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ ≤
            -(2 * (ramificationIndex K : Int)) := by
        exact_mod_cast hdiffQ
      have htargetCurrent :
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
            b.order p.castSucc := by
        apply congrArg b.order
        apply Fin.ext
        simp only [p, Fin.val_castSucc]
        exact hidxPred
      rw [htargetCurrent]
      omega
    have hgapLower : -(2 * (ramificationIndex K : Int)) ≤
        b.orderGap p := by
      have h := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e p.castSucc
        (Nat.succ_lt_succ p.isLt)
      change -(2 * (ramificationIndex K : Int)) ≤ b.orderGap p at h
      exact h
    have hgapEq : b.orderGap p =
        -(2 * (ramificationIndex K : Int)) := by
      by_contra hne
      have hoddGap : Odd (b.orderGap p) := by
        refine ⟨-(ramificationIndex K : Int), ?_⟩
        omega
      have hgapTwo : b.orderGap p ≤
          2 * (ramificationIndex K : Int) := by
        have hePos := ramificationIndex_pos (K := K)
        omega
      have halphaGap := (b.alpha_p3 p hgapTwo).2.mpr (Or.inr hoddGap)
      have halphaNonneg := (b.alpha_p2 p).1
      have hePos := ramificationIndex_pos (K := K)
      rw [halphaGap] at halphaNonneg
      have hgapNonneg : 0 ≤ b.orderGap p := by
        exact_mod_cast halphaNonneg
      omega
    have halphaZero := (b.alpha_p2 p).2.mpr hgapEq
    linarith
  · by_cases hi : 1 < idx.val ∧ idx.val + 1 < n + 2
    · rw [a.representationAlphaPrime_eq_min_primary_secondary b idx hi]
        at hprime
      rcases min_le_iff.mp hprime with hprimary | hsecondaryLe
      · exact hprimaryFalse hprimary
      · have hle := hsecondary hi hsecondaryLe
        exact (not_le_of_gt hpivotAlpha) (by simpa only [p] using hle)
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b idx hi]
        at hprime
      exact hprimaryFalse hprime

/-- Candidate elimination at the right pivot when the optional secondary
candidate is known to be strictly positive. -/
theorem beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b)
    (hboundary :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b 1
          (D.profile.last + 1) (D.profile.last + 1))
    (hsecondary : ∀ hi :
        1 < (typeIRightPivotIndex a b D C P).val ∧
          (typeIRightPivotIndex a b D C P).val + 1 < n + 2,
      (0 : WithTop ℚ) < a.representationSecondaryDefect b
        (typeIRightPivotIndex a b D C P) hi) :
    b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  apply beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_secondary_case
    (alphaV := alphaV) (alphaW := alphaW)
    a b D C hfirst P hdefect hboundary
  intro hi hsecondaryLe
  exact (not_le_of_gt (hsecondary hi) hsecondaryLe).elim

end BONG.GoodBONG

end Bong
