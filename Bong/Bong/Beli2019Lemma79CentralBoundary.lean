/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTrigger
import Bong.Bong.Beli2019Lemma79PointwiseComplete
import Bong.Bong.Beli2019Lemma79RightTailGapTwoTypeIInitial
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAlpha
import Bong.Bong.Beli2019Lemma79EvenTypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma69TypeILeftValue
import Bong.Bong.Beli2019Lemma69TypeICentralTerminalComplete
import Bong.Bong.Beli2019AdjacentCappedDefect
import Bong.Bong.Beli2019Remark616RightMixedGeneral
import Bong.Bong.Beli2019Lemma78Defect
import Bong.Bong.Beli2019Remark613TypeIIRightAlphaLocal
import Bong.Bong.Beli2019Remark613TypeIIIRightAlphaLocal

/-!
# Beli (2019), Lemma 7.9: the first common boundary

This file isolates the arithmetic at the paper's boundary `i = u`.  The
premise supplied by Lemma 2.18 first forces the adjacent target-alpha sum.
The unchanged suffix gives `A_u = beta_u`, while the last changed order is
one or two above the source order.  The remaining profile calculation is
therefore the single lower bound

`beta_(u-1) - delta <= A_(u-1)`.

The type-I gap-two branch is discharged completely below, including the
coincident-switch case `t = t' = u`.
-/

namespace Bong

open Dyadic

universe u v

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]

/-- The last unequal coordinate of two fixed equal-rank sequences is unique. -/
theorem IsLastDifferenceAt.eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} {i j : Nat}
    (hi : IsLastDifferenceAt x y i) (hj : IsLastDifferenceAt x y j) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hj.ne (hi.after j hij hj.bound)
  · exact hi.ne (hj.after i hji hi.bound)

end BeliOrderSequence

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The first Lemma 2.18 premise at a common boundary forces the adjacent
target-alpha sum used in the profile calculation. -/
theorem firstBoundary_targetAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfirst :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  have hpreviousBound : b.representationAlpha c i.previous ≤
      (b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : WithTop ℚ) := by
    calc
      b.representationAlpha c i.previous =
          (b.representationAlphaValue c i.previous : WithTop ℚ) := by
            rw [b.coe_representationAlphaValue c i.previous]
      _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) :=
        hdefectBC i.previous
      _ ≤ b.prefixAlphaCap (i.val - 1) :=
        b.truncatedPrefixDefect_le_leftCap c 1 (i.val - 1) (i.val - 1)
      _ = (b.alphaValue ⟨i.val - 2, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : WithTop ℚ) := by
        rw [b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) (by
          have := i.lt_large
          omega)]
        congr 2
  have hcurrentCap : b.prefixAlphaCap i.val =
      (b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : WithTop ℚ) :=
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : WithTop ℚ) +
          (b.alphaValue ⟨i.val - 2, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : WithTop ℚ) := by
    exact hfirst.trans_le (add_le_add hcurrentCap.le hpreviousBound)
  rw [add_comm] at hsumTop
  exact_mod_cast hsumTop

/-- Generic assembly of the first-boundary trigger once the preceding
representation alpha has the profile-specific shifted lower bound. -/
theorem centralAlphaTrigger_of_firstBoundary_shift
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (last : Nat)
    (hlast : BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last)
    (hboundary : i.val = last + 1)
    (delta : Int)
    (hgap : b.orderSequence.entryOrZero last =
      a.orderSequence.entryOrZero last + delta)
    (hpreviousLower :
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - (delta : ℚ) ≤
        a.representationAlphaValue b i.previous)
    (hfirst :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hsuffix : ∀ k, currentIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hlast.after k
    · simp only [currentIdx, CentralRepresentationIndex.current] at hk
      omega
    · exact hkn
  have hcurrent := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition currentIdx hsuffix
  have hmiddle :
      (b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) =
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) + (delta : ℚ) := by
    have hlastBound : last < n + 2 := hlast.bound
    have hgapOrder : b.order ⟨last, hlastBound⟩ =
        a.order ⟨last, hlastBound⟩ + delta := by
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order]
      exact hgap
    have hgapOrderQ : (b.order ⟨last, hlastBound⟩ : ℚ) =
        (a.order ⟨last, hlastBound⟩ : ℚ) + (delta : ℚ) := by
      exact_mod_cast hgapOrder
    simpa only [hboundary, show last + 1 - 1 = last by omega] using hgapOrderQ
  have hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hlast.after i.val (by omega) i.lt_large
  have hsum := firstBoundary_targetAlphaSum b c hdefectBC i hfirst
  apply a.centralAlphaTrigger_of_shiftedMiddleOrder_of_alphaSum
    b i (delta : ℚ) hpreviousLower
  · simpa only [currentIdx, CentralRepresentationIndex.current] using hcurrent
  · exact hmiddle
  · exact hcurrentOrder
  · exact hsum

set_option maxHeartbeats 5000000 in
/-- Lemma 6.9(i) at the last unequal coordinate in the gap-one branch.

The proof is independent of the three profiles.  The target adjacent defect
is bounded below by Remark 1.1 and transferred across the first common
suffix by Remark 6.16.  The half-gap and optional secondary candidates are
nonnegative by P2 and two-step monotonicity.  Since the preceding comparison
prefixes have order difference one, condition 2.1(ii) then forces the
representation alpha to be zero. -/
theorem firstBoundary_gapOne_previousAlpha_eq_zero_of_secondaryCoefficient
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (last : Nat)
    (hlast : BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last)
    (hboundary : i.val = last + 1)
    (hgapOne : b.orderSequence.entryOrZero last =
      a.orderSequence.entryOrZero last + 1)
    (hsecondaryCoefficient :
      ∀ hi : 1 < last ∧ last + 1 < n + 2,
        0 ≤ a.orderSequence.entryOrZero last +
            a.orderSequence.entryOrZero (last + 1) -
          b.orderSequence.entryOrZero (last - 2) -
            b.orderSequence.entryOrZero (last - 1))
    (hbetaOne : b.alphaValue ⟨last - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = 1) :
    a.representationAlphaValue b i.previous = 0 := by
  let idx : RepresentationIndex (n + 2) (n + 2) := i.previous
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hlastPos : 0 < last := by
    have := i.one_lt
    omega
  have hlastBound : last < n + 2 := hlast.bound
  have hidxVal : idx.val = last := by
    simp only [idx, CentralRepresentationIndex.previous, hboundary]
    omega
  have hnextVal : nextIdx.val = last + 1 := by
    simp only [nextIdx, CentralRepresentationIndex.current, hboundary]
  have hsuffix : ∀ k, nextIdx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply hlast.after k
    · omega
    · exact hkn
  have hnextAlpha := a.beli2019Lemma63_sameRank_right_value
    b hab.defectCondition nextIdx hsuffix
  have hprefixAfter :=
    hlast.prefixSum_add_totalGap_eq_after 2 htotal (last + 1)
      (by omega) (by omega)
  have hsum : b.orderSequence.prefixSum idx.val =
      a.orderSequence.prefixSum idx.val + 1 := by
    rw [hidxVal]
    rw [a.orderSequence.prefixSum_succ,
      b.orderSequence.prefixSum_succ] at hprefixAfter
    omega
  let previousAlpha : Fin (n + 1) := ⟨last - 1, by omega⟩
  have hbeta : b.alphaValue previousAlpha = 1 := by
    simpa only [previousAlpha] using hbetaOne
  have hHalf : 0 ≤ a.representationHalfGap b idx := by
    have hgapLower := b.orderGap_ge_neg_two_mul_e previousAlpha
    have hgapNe : b.orderGap previousAlpha ≠
        -(2 * (ramificationIndex K : Int)) := by
      intro hgapEq
      have hzero := (b.alpha_p2 previousAlpha).2.mpr hgapEq
      rw [hbeta] at hzero
      norm_num at hzero
    have hgapStrict : -(2 * (ramificationIndex K : Int)) <
        b.orderGap previousAlpha := by
      omega
    have hcross : -(2 * (ramificationIndex K : Int)) ≤
        a.orderSequence.entryOrZero last -
          b.orderSequence.entryOrZero (last - 1) := by
      unfold orderGap at hgapStrict
      rw [← b.orderSequence_entryOrZero_eq_order previousAlpha.succ,
        ← b.orderSequence_entryOrZero_eq_order previousAlpha.castSucc]
        at hgapStrict
      simp only [Fin.val_succ, Fin.val_castSucc, previousAlpha] at hgapStrict
      have hpreviousSucc : last - 1 + 1 = last := by omega
      rw [hpreviousSucc] at hgapStrict
      omega
    unfold representationHalfGap
    have hcrossOrder : -(2 * (ramificationIndex K : Int)) ≤
        a.order ⟨idx.val, idx.lt_large⟩ -
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      change -(2 * (ramificationIndex K : Int)) ≤
        a.orderSequence.entryOrZero idx.val -
          b.orderSequence.entryOrZero (idx.val - 1)
      simpa only [hidxVal] using hcross
    norm_cast
    have hcrossOrderQ : -(2 * (ramificationIndex K : ℚ)) ≤
        ((a.order ⟨idx.val, idx.lt_large⟩ -
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) :
          ℚ) := by
      exact_mod_cast hcrossOrder
    push_cast at hcrossOrderQ
    push_cast at ⊢
    simp only [Rat.divInt_eq_div] at ⊢
    push_cast at ⊢
    linarith [hcrossOrderQ]
  have hPrimary : 0 ≤ a.representationPrimaryDefect b idx := by
    have hadjacent := b.order_sub_add_alpha_le_cappedAdjacent previousAlpha
    rw [hbeta] at hadjacent
    let previousOrder : Fin (n + 2) := ⟨last - 1, by omega⟩
    let currentOrder : Fin (n + 2) := ⟨last, hlastBound⟩
    have hpCast : previousAlpha.castSucc = previousOrder := by
      apply Fin.ext
      rfl
    have hpSucc : previousAlpha.succ = currentOrder := by
      apply Fin.ext
      simp only [Fin.val_succ, previousAlpha, currentOrder]
      omega
    rw [hpCast, hpSucc] at hadjacent
    have hplusTwo : last - 1 + 2 = last + 1 := by omega
    have hpreviousEntry : b.order previousOrder =
        b.orderSequence.entryOrZero (last - 1) := by
      rw [b.orderSequence.entryOrZero_of_lt (by omega)]
      rfl
    have hcurrentEntry : b.order currentOrder =
        b.orderSequence.entryOrZero last := by
      rw [b.orderSequence.entryOrZero_of_lt hlastBound]
      rfl
    rw [hpreviousEntry, hcurrentEntry] at hadjacent
    have hadjacent' :
        (((((b.orderSequence.entryOrZero (last - 1) -
            b.orderSequence.entryOrZero last : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ)) ≤
          b.truncatedPrefixDefect b (-1) (last - 1) (last + 1) := by
      simpa only [previousAlpha, hplusTwo] using hadjacent
    have htransfer := a.beli2019Remark616_rightMixedPrefix_at
      b b hab.defectCondition nextIdx hnextAlpha (-1) (last - 1)
    have htargetSource :
        b.truncatedPrefixDefect b (-1) (last - 1) (last + 1) ≤
          a.truncatedPrefixDefect b (-1) (last + 1) (last - 1) := by
      rw [b.truncatedPrefixDefect_comm b (-1) (last - 1) (last + 1)]
      have htargetSourceRaw :
          b.truncatedPrefixDefect b (-1) nextIdx.val (last - 1) ≤
            a.truncatedPrefixDefect b (-1) nextIdx.val (last - 1) := by
        rw [htransfer]
        exact min_le_left _ _
      simpa only [hnextVal] using htargetSourceRaw
    have hmixed := hadjacent'.trans htargetSource
    unfold representationPrimaryDefect
    let crossQ : ℚ := ((a.order ⟨idx.val, idx.lt_large⟩ -
      b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ)
    let lowerQ : ℚ :=
      ((b.orderSequence.entryOrZero (last - 1) -
        b.orderSequence.entryOrZero last : Int) : ℚ) + 1
    have hmixedIdx :
        (lowerQ : WithTop ℚ) ≤
          a.truncatedPrefixDefect b (-1) (idx.val + 1) (idx.val - 1) := by
      simpa only [lowerQ, hidxVal] using hmixed
    have hzeroQ : crossQ + lowerQ = 0 := by
      dsimp only [crossQ, lowerQ]
      push_cast
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      simp only [Fin.val_mk]
      rw [hidxVal, hgapOne]
      push_cast
      ring
    change (0 : WithTop ℚ) ≤
      (crossQ : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (idx.val + 1) (idx.val - 1)
    calc
      (0 : WithTop ℚ) = (crossQ : WithTop ℚ) + (lowerQ : WithTop ℚ) := by
        exact_mod_cast hzeroQ.symm
      _ ≤ _ := by gcongr
  have hSecondary : ∀ hi : 1 < idx.val ∧ idx.val + 1 < n + 2,
      0 ≤ a.representationSecondaryDefect b idx hi := by
    intro hi
    have hiLast : 1 < last ∧ last + 1 < n + 2 := by
      simpa only [hidxVal] using hi
    have hcoefficientRaw := hsecondaryCoefficient hiLast
    have hcoefficient :
        0 ≤ a.order ⟨idx.val, idx.lt_large⟩ +
            a.order ⟨idx.val + 1, hi.2⟩ -
          b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      simp only [Fin.val_mk]
      rw [hidxVal]
      exact hcoefficientRaw
    have hdefect := a.truncatedPrefixDefect_nonneg
      b 1 (idx.val + 2) (idx.val - 2)
    unfold representationSecondaryDefect
    have hcoefficientTop : (0 : WithTop ℚ) ≤
        (((a.order ⟨idx.val, idx.lt_large⟩ +
            a.order ⟨idx.val + 1, hi.2⟩ -
          b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
            b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) :
          ℚ) : WithTop ℚ) := by
      exact_mod_cast hcoefficient
    exact add_nonneg hcoefficientTop hdefect
  have hnonnegative : 0 ≤ a.representationAlpha b idx :=
    a.representationAlpha_nonneg_of_candidates b idx
      hHalf hPrimary hSecondary
  have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    b idx.val idx.lt_large.le idx.le_small hsum
  have hupper := hab.defectCondition idx
  rw [hzeroDefect] at hupper
  have hlower : (0 : WithTop ℚ) ≤
      (a.representationAlphaValue b idx : WithTop ℚ) := by
    rw [a.coe_representationAlphaValue b idx]
    exact hnonnegative
  have htop : (a.representationAlphaValue b idx : WithTop ℚ) = 0 :=
    le_antisymm hupper hlower
  have hvalue : a.representationAlphaValue b idx = 0 := by
    exact_mod_cast htop
  simpa only [idx] using hvalue

/-- A convenient profile-free specialization: opposite one-unit shifts at
the last two unequal coordinates imply the required secondary coefficient
by two-step monotonicity. -/
theorem firstBoundary_gapOne_previousAlpha_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (last : Nat)
    (hlast : BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last)
    (hboundary : i.val = last + 1)
    (hgapOne : b.orderSequence.entryOrZero last =
      a.orderSequence.entryOrZero last + 1)
    (hpreviousOne : a.orderSequence.entryOrZero (last - 1) =
      b.orderSequence.entryOrZero (last - 1) + 1)
    (hbetaOne : b.alphaValue ⟨last - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = 1) :
    a.representationAlphaValue b i.previous = 0 := by
  apply firstBoundary_gapOne_previousAlpha_eq_zero_of_secondaryCoefficient
    a b hab htotal i last hlast hboundary hgapOne
  · intro hi
    have hlastBound := hlast.bound
    have htargetTwoStep := b.orderSequence.entryOrZero_le_of_evenGap
      (last - 2) last (by omega) hlastBound ⟨1, by omega⟩
    have hsourceTwoStep := a.orderSequence.entryOrZero_le_of_evenGap
      (last - 1) (last + 1) (by omega) hi.2 ⟨1, by omega⟩
    omega
  · exact hbetaOne

set_option maxHeartbeats 7000000 in
/- The type-II first-boundary gap-one calculation.  The terminal branch
uses the constant middle interval and the core value `beta = 1`; the
nonterminal branch uses the alternating right profile. -/
theorem beli2019Lemma79_typeII_firstBoundary_gapOne_data
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1) :
    a.representationAlphaValue b i.previous = 0 ∧
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = 1 := by
  have hlastPos : 0 < D.outer.last := by
    have := i.one_lt
    omega
  have hlastBound : D.outer.last < n + 2 :=
    D.outer.lastDifference.bound
  by_cases hterminal :
      D.outer.last = D.outer.transition.firstTwo - 1
  · have hbetaBoundary :=
      a.beli2019Lemma69_i_typeII_targetBoundary_eq_one b D
    have hbetaLast : b.alphaValue ⟨D.outer.last - 1, by omega⟩ = 1 := by
      have hfin : (⟨D.outer.last - 1, by omega⟩ : Fin (n + 1)) =
      ⟨D.outer.transition.firstTwo - 2, by
            have hbound := D.outer.transition.firstTwo_le_rank
            have hlong := D.long
            omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [hfin]
      exact hbetaBoundary
    have hzero :=
      firstBoundary_gapOne_previousAlpha_eq_zero_of_secondaryCoefficient
        a b hab htotal i D.outer.last D.outer.lastDifference
          hboundary hgapOne (by
            intro hi
            let T := b.orderSequence.entryOrZero
              D.outer.transition.lastZero
            have haLast : a.orderSequence.entryOrZero D.outer.last = T := by
              rw [hterminal, D.right_source]
            have haPrevious :
                a.orderSequence.entryOrZero (D.outer.last - 1) = T := by
              apply D.middle (D.outer.last - 1)
              · have hlong := D.long
                omega
              · have hlong := D.long
                omega
            have habPrevious :
                a.orderSequence.entryOrZero (D.outer.last - 1) =
                  b.orderSequence.entryOrZero (D.outer.last - 1) := by
              apply D.outer.transition.middle (D.outer.last - 1)
              · have hlong := D.long
                omega
              · have hlong := D.long
                omega
            have hbPrevious :
                b.orderSequence.entryOrZero (D.outer.last - 1) = T := by
              exact habPrevious.symm.trans haPrevious
            have hbPreviousTwo :
                b.orderSequence.entryOrZero (D.outer.last - 2) = T := by
              by_cases heq : D.outer.last - 2 =
                  D.outer.transition.lastZero
              · rw [heq]
              · have hleftLe : D.outer.transition.lastZero ≤
                    D.outer.last - 2 := by
                  have hlong := D.long
                  omega
                have hleftLt : D.outer.transition.lastZero <
                    D.outer.last - 2 :=
                      lt_of_le_of_ne hleftLe (Ne.symm heq)
                have haPreviousTwo :
                    a.orderSequence.entryOrZero (D.outer.last - 2) = T := by
                  apply D.middle (D.outer.last - 2) hleftLt
                  have hlong := D.long
                  omega
                have habPreviousTwo :
                    a.orderSequence.entryOrZero (D.outer.last - 2) =
                      b.orderSequence.entryOrZero (D.outer.last - 2) := by
                  apply D.outer.transition.middle
                    (D.outer.last - 2) hleftLt
                  have hlong := D.long
                  omega
                exact habPreviousTwo.symm.trans haPreviousTwo
            have hsourceTwoStep :=
              a.orderSequence.entryOrZero_le_of_evenGap
                (D.outer.last - 1) (D.outer.last + 1)
                (by omega) hi.2 ⟨1, by omega⟩
            omega)
          hbetaLast
    refine ⟨hzero, ?_⟩
    have hfin : (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) =
        ⟨D.outer.last - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
    exact hbetaLast
  · have hrightLt : D.outer.transition.firstTwo - 1 <
        D.outer.last := by
      exact lt_of_le_of_ne D.outer.right_le_last (Ne.symm hterminal)
    rcases D.outer.right_even_distance with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    have hpreviousRight : D.outer.transition.firstTwo - 1 ≤
        D.outer.last - 1 := by omega
    have hpreviousFromTransition : D.outer.transition.firstTwo ≤
        D.outer.last - 1 := by omega
    have hpreviousOdd : Odd
        ((D.outer.last - 1) -
          (D.outer.transition.firstTwo - 1)) := by
      exact ⟨d - 1, by omega⟩
    have horders := D.outer.source_rightOdd_eq_target_add_one
      D.no_gap_two (D.outer.last - 1) hpreviousRight
        (by omega) hpreviousOdd
    have hbeta :=
      a.beli2019Remark613_typeII_targetRightAlpha_eq_one_local
        b D hab.orderCondition hab.defectCondition htotal
          (D.outer.last - 1) hpreviousFromTransition (by omega)
          hpreviousOdd
    have hzero := firstBoundary_gapOne_previousAlpha_eq_zero
      a b hab htotal i D.outer.last D.outer.lastDifference
        hboundary hgapOne horders hbeta
    refine ⟨hzero, ?_⟩
    have hfin : (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) =
        ⟨D.outer.last - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
    exact hbeta

/- In type II, the preceding shifted lower bound is exact in the
gap-one branch. -/
theorem beli2019Lemma79_typeII_firstBoundary_gapOne_previousLower
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1) :
    b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - 1 ≤
      a.representationAlphaValue b i.previous := by
  have hdata := beli2019Lemma79_typeII_firstBoundary_gapOne_data
    a b D hab htotal i hboundary hgapOne
  rw [hdata.1, hdata.2]
  norm_num

/- Complete type-II gap-one trigger at the first common boundary. -/
theorem beli2019Lemma79_typeII_firstBoundary_gapOne_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1)
    (hpremise :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  apply centralAlphaTrigger_of_firstBoundary_shift
    a b c hab hdefectBC i D.outer.last D.outer.lastDifference
      hboundary 1 hgapOne
  · exact beli2019Lemma79_typeII_firstBoundary_gapOne_previousLower
      a b D hab htotal i hboundary hgapOne
  · exact hpremise

set_option maxHeartbeats 8000000 in
/- The type-III first-boundary gap-one calculation, uniformly covering
the overlapping and nonoverlapping central gap. -/
theorem beli2019Lemma79_typeIII_firstBoundary_gapOne_data
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1) :
    a.representationAlphaValue b i.previous = 0 ∧
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = 1 := by
  have hlastPos : 0 < D.outer.last := by
    have := i.one_lt
    omega
  have hlastBound : D.outer.last < n + 2 :=
    D.outer.lastDifference.bound
  let center : Fin (n + 1) :=
    ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩
  by_cases hterminal :
      D.outer.last = D.outer.transition.firstTwo - 1
  · have hlastCenter :
        D.outer.last = D.outer.transition.lastZero + 1 := by
      rw [hterminal, D.adjacent]
      omega
    have hbetaCenter : b.alphaValue center = 1 := by
      by_cases hoverlap : a.orderGap center = 1
      · have hraw :=
          a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
            b D hab.orderCondition hab.defectCondition htotal (by
              simpa only [center] using hoverlap)
        simpa only [center] using hraw
      · have hraw := a.beli2019Lemma78_alphas_and_gap_local
          b D hfirst hab.orderCondition hab.defectCondition htotal (by
            simpa only [center] using hoverlap) hinitial
        simpa only [center] using hraw.2.1
    have hbetaLast : b.alphaValue ⟨D.outer.last - 1, by omega⟩ = 1 := by
      have hfin : (⟨D.outer.last - 1, by omega⟩ : Fin (n + 1)) =
          center := by
        apply Fin.ext
        simp only [center, Fin.val_mk]
        omega
      rw [hfin]
      exact hbetaCenter
    have hzero :=
      firstBoundary_gapOne_previousAlpha_eq_zero_of_secondaryCoefficient
        a b hab htotal i D.outer.last D.outer.lastDifference
          hboundary hgapOne (by
            intro hi
            have hiCenter :
                1 < D.outer.transition.lastZero + 1 ∧
                  D.outer.transition.lastZero + 1 + 1 < n + 2 := by
              omega
            have hpositive :=
              a.lemma69_typeIII_secondaryCoefficient_pos
                b D hfirst hiCenter
            rw [← a.orderSequence_entryOrZero_eq_order,
              ← a.orderSequence_entryOrZero_eq_order,
              ← b.orderSequence_entryOrZero_eq_order,
              ← b.orderSequence_entryOrZero_eq_order] at hpositive
            simp only [Fin.val_mk] at hpositive
            simpa only [hlastCenter] using hpositive.le)
          hbetaLast
    refine ⟨hzero, ?_⟩
    have hfin : (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) =
        ⟨D.outer.last - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
    exact hbetaLast
  · have hrightLt : D.outer.transition.firstTwo - 1 <
        D.outer.last :=
      lt_of_le_of_ne D.outer.right_le_last (Ne.symm hterminal)
    rcases D.outer.right_even_distance with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    have hpreviousRight : D.outer.transition.firstTwo - 1 ≤
        D.outer.last - 1 := by omega
    have hpreviousFromTransition : D.outer.transition.firstTwo ≤
        D.outer.last - 1 := by omega
    have hpreviousOdd : Odd
        ((D.outer.last - 1) -
          (D.outer.transition.firstTwo - 1)) :=
      ⟨d - 1, by omega⟩
    have horders := D.outer.source_rightOdd_eq_target_add_one
      D.no_gap_two (D.outer.last - 1) hpreviousRight
        (by omega) hpreviousOdd
    have hbeta : b.alphaValue ⟨D.outer.last - 1, by omega⟩ = 1 := by
      by_cases hoverlap : a.orderGap center = 1
      · exact a.beli2019Remark613_typeIII_overlap_targetRightAlpha_eq_one_local
          b D hab.orderCondition hab.defectCondition htotal (by
            simpa only [center] using hoverlap)
          (D.outer.last - 1) hpreviousFromTransition (by omega)
            hpreviousOdd
      · exact a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_local
          b D hfirst hab.orderCondition hab.defectCondition htotal (by
            simpa only [center] using hoverlap) hinitial
          (D.outer.last - 1) hpreviousFromTransition (by omega)
            hpreviousOdd
    have hzero := firstBoundary_gapOne_previousAlpha_eq_zero
      a b hab htotal i D.outer.last D.outer.lastDifference
        hboundary hgapOne horders hbeta
    refine ⟨hzero, ?_⟩
    have hfin : (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) =
        ⟨D.outer.last - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
    exact hbeta

/- In type III, the preceding shifted lower bound is exact in the
gap-one branch. -/
theorem beli2019Lemma79_typeIII_firstBoundary_gapOne_previousLower
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1) :
    b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - 1 ≤
      a.representationAlphaValue b i.previous := by
  have hdata := beli2019Lemma79_typeIII_firstBoundary_gapOne_data
    a b D hfirst hinitial hab htotal i hboundary hgapOne
  rw [hdata.1, hdata.2]
  norm_num

/- Complete type-III gap-one trigger at the first common boundary. -/
theorem beli2019Lemma79_typeIII_firstBoundary_gapOne_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero D.outer.last + 1)
    (hpremise :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  apply centralAlphaTrigger_of_firstBoundary_shift
    a b c hab hdefectBC i D.outer.last D.outer.lastDifference
      hboundary 1 hgapOne
  · exact beli2019Lemma79_typeIII_firstBoundary_gapOne_previousLower
      a b D hfirst hinitial hab htotal i hboundary hgapOne
  · exact hpremise

set_option maxHeartbeats 6000000 in
/-- Type I supplies the two alternating order shifts and the exact
`beta_(u-1) = 1` input needed by the profile-independent gap-one lemma. -/
theorem beli2019Lemma79_typeI_firstBoundary_gapOne_previousAlpha_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.profile.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1) :
    a.representationAlphaValue b i.previous = 0 := by
  rcases lemma67TypeICanonicalData a b D hfirst with ⟨C⟩
  have hlastPos : 0 < D.profile.last := by
    have := i.one_lt
    omega
  have hrightLast : C.rightSwitch < D.profile.last := by
    by_contra hnot
    have hrightLe := C.right_le_last
    have heq : C.rightSwitch = D.profile.last := by omega
    have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
    have hdistance : Even (D.profile.last - D.anchor) := by
      rcases C.right_even with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hsource := C.source_to_right D.profile.last
      (C.anchor_le_right.trans_eq heq) (by rw [← heq]) hdistance
    have htarget := C.target_from_anchor D.profile.last
      (C.anchor_le_right.trans_eq heq) le_rfl hdistance
    have hanchorGap := D.anchor_gap
    omega
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hpreviousOdd : Odd (D.profile.last - 1) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousRight : C.rightSwitch < D.profile.last - 1 := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst (D.profile.last - 1) hpreviousRight
      (by omega) hpreviousOdd
  have hbeta := beli2019Remark613_typeI_targetRightAlpha_eq_one
    a b D C hfirst hrightLast hab.defectCondition
      (D.profile.last - 1) hpreviousRight (by omega) hpreviousOdd
  apply firstBoundary_gapOne_previousAlpha_eq_zero
    a b hab htotal i D.profile.last D.profile.lastDifference
      hboundary hgapOne
  · exact horders.1
  · simpa only using hbeta

/-- In the type-I gap-one branch, the preceding shifted lower bound is
exact: both sides are zero after subtracting one from `beta_(u-1)`. -/
theorem beli2019Lemma79_typeI_firstBoundary_gapOne_previousLower
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.profile.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1) :
    b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - 1 ≤
      a.representationAlphaValue b i.previous := by
  rcases lemma67TypeICanonicalData a b D hfirst with ⟨C⟩
  have hrightLast : C.rightSwitch < D.profile.last := by
    by_contra hnot
    have hrightLe := C.right_le_last
    have heq : C.rightSwitch = D.profile.last := by omega
    have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
    have hdistance : Even (D.profile.last - D.anchor) := by
      rcases C.right_even with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hsource := C.source_to_right D.profile.last
      (C.anchor_le_right.trans_eq heq) (by rw [← heq]) hdistance
    have htarget := C.target_from_anchor D.profile.last
      (C.anchor_le_right.trans_eq heq) le_rfl hdistance
    have hanchorGap := D.anchor_gap
    omega
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hpreviousOdd : Odd (D.profile.last - 1) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousRight : C.rightSwitch < D.profile.last - 1 := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hbeta := beli2019Remark613_typeI_targetRightAlpha_eq_one
    a b D C hfirst hrightLast hab.defectCondition
      (D.profile.last - 1) hpreviousRight (by omega) hpreviousOdd
  have hzero :=
    beli2019Lemma79_typeI_firstBoundary_gapOne_previousAlpha_eq_zero
      a b D hfirst hab htotal i hboundary hgapOne
  rw [hzero]
  have hindex : i.val - 2 = D.profile.last - 1 := by omega
  have hfin : (⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : Fin (n + 1)) =
      ⟨D.profile.last - 1, by
        have hbound := D.profile.lastDifference.bound
        omega⟩ := by
    apply Fin.ext
    exact hindex
  rw [hfin, hbeta]
  norm_num

/-- Complete type-I gap-one trigger at the first common boundary. -/
theorem beli2019Lemma79_typeI_firstBoundary_gapOne_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.profile.last + 1)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1)
    (hpremise :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  apply centralAlphaTrigger_of_firstBoundary_shift
    a b c hab hdefectBC i D.profile.last D.profile.lastDifference
      hboundary 1 hgapOne
  · exact beli2019Lemma79_typeI_firstBoundary_gapOne_previousLower
      a b D hfirst hab htotal i hboundary hgapOne
  · exact hpremise

/-- In the type-I gap-two branch, the preceding representation alpha is at
least `beta_(u-1) - 2`.  This includes both `t < t' = u` and
`t = t' = u`. -/
theorem beli2019Lemma79_typeI_firstBoundary_gapTwo_previousLower
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.profile.last + 1) :
    b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - 2 ≤
      a.representationAlphaValue b i.previous := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let C := I.canonical
  have hlastPos : 0 < D.profile.last := by
    have := i.one_lt
    omega
  have hlastBound : D.profile.last < n + 2 :=
    D.profile.lastDifference.bound
  let idx : RepresentationIndex (n + 2) (n + 2) := i.previous
  have hidxVal : idx.val = D.profile.last := by
    simp only [idx, CentralRepresentationIndex.previous, hboundary]
    omega
  have hidxEven : Even idx.val := by
    simpa only [hidxVal] using I.last_even
  by_cases hcoincident : C.leftSwitch = D.profile.last
  · have hleftPos : 0 < C.leftSwitch := by omega
    have hleftTwo : 2 ≤ C.leftSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    have hnext : C.leftSwitch + 1 < n + 2 := by
        rw [hcoincident, ← hboundary]
        exact i.lt_large
    have hAraw := beli2019Lemma69_ii_typeI_sourceLeftValue
      a b D C hfirst hnext hab.defectCondition idx (by
        rw [hidxVal]
        omega) (by
        exact (hidxVal.trans hcoincident.symm).le) hidxEven
    have hA : a.representationAlphaValue b idx =
        a.alphaValue ⟨D.profile.last - 1, by omega⟩ := by
      apply WithTop.coe_injective
      rw [a.coe_representationAlphaValue b idx, hAraw]
      congr 2
      apply Fin.ext
      simp only [hidxVal]
    have hbeta := beli2019Lemma79_typeI_leftSwitch_alphaClose
      a b D C hfirst hab.defectCondition hleftTwo
    have hbeta' : b.alphaValue ⟨D.profile.last - 1, by omega⟩ ≤
        a.alphaValue ⟨D.profile.last - 1, by omega⟩ + 2 := by
      simpa only [hcoincident] using hbeta
    rw [hA]
    have hindex : i.val - 2 = D.profile.last - 1 := by omega
    simpa only [hindex] using (show
      b.alphaValue ⟨D.profile.last - 1, by omega⟩ - 2 ≤
        a.alphaValue ⟨D.profile.last - 1, by omega⟩ by linarith)
  · have hleftLt : C.leftSwitch < D.profile.last := by
      have hleftLe : C.leftSwitch ≤ D.profile.last := by
        rw [← I.rightSwitch_eq_last]
        exact C.left_le_anchor.trans C.anchor_le_right
      exact lt_of_le_of_ne hleftLe hcoincident
    have hleftPrevious : C.leftSwitch ≤ idx.val - 1 := by
      rcases C.left_even with ⟨d, hd⟩
      rcases I.last_even with ⟨e, he⟩
      simp only [hidxVal]
      omega
    have hpreviousRight : idx.val - 1 < C.rightSwitch := by
      rw [I.rightSwitch_eq_last, hidxVal]
      omega
    have hAraw :=
      (lemma69_typeI_central_values_from_conditions_complete
        a b D C hfirst hab.orderCondition hab.defectCondition idx
          hleftPrevious hpreviousRight).2 hidxEven
    have hA : a.representationAlphaValue b idx =
        a.alphaValue ⟨D.profile.last - 1, by omega⟩ := by
      apply WithTop.coe_injective
      rw [a.coe_representationAlphaValue b idx, hAraw]
      congr 2
      apply Fin.ext
      simp only [hidxVal]
    have hbetaRaw :=
      beli2019Lemma79_typeI_central_even_alphaShift_complete
        a b D C hfirst hab.orderCondition hab.defectCondition idx
          hidxEven hleftPrevious hpreviousRight
    have hbeta : b.alphaValue ⟨D.profile.last - 1, by omega⟩ =
        a.alphaValue ⟨D.profile.last - 1, by omega⟩ + 2 := by
      simpa only [hidxVal] using hbetaRaw
    rw [hA]
    have hindex : i.val - 2 = D.profile.last - 1 := by omega
    have hfin :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : Fin (n + 1)) =
          ⟨D.profile.last - 1, by omega⟩ := by
      apply Fin.ext
      exact hindex
    rw [hfin, hbeta]
    linarith

/-- Complete type-I gap-two trigger at the first common boundary. -/
theorem beli2019Lemma79_typeI_firstBoundary_gapTwo_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.profile.last + 1)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hpremise :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  apply centralAlphaTrigger_of_firstBoundary_shift
    a b c hab hdefectBC i D.profile.last D.profile.lastDifference
      hboundary 2 hgapTwo
  · exact beli2019Lemma79_typeI_firstBoundary_gapTwo_previousLower
      a b D hfirst hab hgapTwo i hboundary
  · exact hpremise

/- The normalized Lemma 6.7 classification supplies the first-boundary
trigger in every profile.  Type I splits according to whether the last
order rises by one or two; types II and III have the exact one-unit rise. -/
theorem Lemma79NormalizedClassification.firstBoundary_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (last : Nat)
    (hlast : BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last)
    (hboundary : i.val = last + 1)
    (hpremise :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    a.centralAlphaTrigger b i := by
  cases D with
  | typeI E hfirst =>
      have hlastEq : last = E.profile.last :=
        hlast.eq E.profile.lastDifference
      have hboundaryE : i.val = E.profile.last + 1 := by
        simpa only [hlastEq] using hboundary
      rcases beli2019Lemma79_typeI_caseEight_lastGap a b E with
        hgapOne | hgapTwo
      · exact beli2019Lemma79_typeI_firstBoundary_gapOne_trigger
          a b c E hfirst hab hdefectBC htotal i hboundaryE hgapOne
            hpremise
      · exact beli2019Lemma79_typeI_firstBoundary_gapTwo_trigger
          a b c E hfirst hab hdefectBC i hboundaryE hgapTwo hpremise
  | typeII E _hfirst =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hboundaryE : i.val = E.outer.last + 1 := by
        simpa only [hlastEq] using hboundary
      have hgapOne := beli2019Lemma79_typeII_caseEight_lastGap a b E
      exact beli2019Lemma79_typeII_firstBoundary_gapOne_trigger
        a b c E hab hdefectBC htotal i hboundaryE hgapOne hpremise
  | typeIII E hfirst hinitial =>
      have hlastEq : last = E.outer.last :=
        hlast.eq E.outer.lastDifference
      have hboundaryE : i.val = E.outer.last + 1 := by
        simpa only [hlastEq] using hboundary
      have hgapOne := beli2019Lemma79_typeIII_caseEight_lastGap a b E
      exact beli2019Lemma79_typeIII_firstBoundary_gapOne_trigger
        a b c E hfirst hinitial hab hdefectBC htotal i hboundaryE
          hgapOne hpremise

end BONG.GoodBONG

end Bong
