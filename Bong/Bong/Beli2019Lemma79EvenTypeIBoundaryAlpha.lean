/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftValueLocal
import Bong.Bong.Beli2019Lemma69TypeINeighbor
import Bong.Bong.Beli2019Lemma79EvenTypeIAlphaShift

/-!
# Beli (2019), Lemma 7.9(ii), case 3: alpha at the first type-I switch

The target gap at the first canonical switch is odd and at most `2e + 1`.
Below `2e` Lemma 2.7(iii) identifies alpha with the gap; in the remaining
case Lemma 2.7(ii) identifies it with the half-gap.  Both cases put the
target alpha within two units of the source alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target gap at a positive first type-I switch is at most `2e + 1`. -/
theorem lemma79_typeI_leftSwitch_gap_le_twoE_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch) :
    b.orderGap ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ ≤ 2 * (ramificationIndex K : Int) + 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hpreviousSucc : previous.succ =
      (⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨C.leftSwitch - 2, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hskip := lemma76_leftSwitch_skip a b D C hleftPos
  have hgapLower := b.orderGap_ge_neg_two_mul_e previous
  let current : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hcurrentSucc : current.succ =
      (⟨C.leftSwitch, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have hcurrentCast : current.castSucc =
      (⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  change b.orderGap current ≤ 2 * (ramificationIndex K : Int) + 1
  unfold orderGap at hgapLower ⊢
  rw [hpreviousSucc, hpreviousCast] at hgapLower
  rw [hcurrentSucc, hcurrentCast]
  have hskip' : b.order ⟨C.leftSwitch, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ =
      b.order ⟨C.leftSwitch - 2, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ + 1 := by
    simpa only using hskip
  omega

set_option maxHeartbeats 2000000 in
-- The proof separates the two arithmetic branches of Lemma 2.7.
/-- At the first canonical type-I switch the target alpha is at most the
source alpha plus two. -/
theorem beli2019Lemma79_typeI_leftSwitch_alphaClose
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hleftTwo : 2 ≤ C.leftSwitch) :
    b.alphaValue ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ ≤
      a.alphaValue ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ + 2 := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let p : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  let switchIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.leftSwitch, hleftPos, hleftBound, hleftBound.le⟩
  have hpCast : p.castSucc =
      (⟨C.leftSwitch - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hsourceFormulaRaw := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefect switchIdx (by
      simp only [switchIdx]
      omega) (by simp only [switchIdx]; exact le_rfl) (by
        simpa only [switchIdx] using C.left_even)
  have hsourceFormula : a.alphaValue p =
      (a.orderGap p : ℚ) + 1 := by
    unfold orderGap
    rw [hpSucc, hpCast]
    simpa only [switchIdx, p] using hsourceFormulaRaw
  have htargetPrevious := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hsourceLeft := C.source_to_anchor C.leftSwitch
    C.left_le_anchor C.left_even
  have htargetLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hleftShift : b.order ⟨C.leftSwitch, hleftBound⟩ =
      a.order ⟨C.leftSwitch, hleftBound⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero C.leftSwitch =
      a.orderSequence.entryOrZero C.leftSwitch + 2
    omega
  have hgapShift : b.orderGap p = a.orderGap p + 3 := by
    unfold orderGap
    rw [hpSucc, hpCast, hleftShift]
    have htargetPrevious' :
        b.order ⟨C.leftSwitch - 1, by omega⟩ =
          a.order ⟨C.leftSwitch - 1, by omega⟩ - 1 := by
      simpa only using htargetPrevious
    rw [htargetPrevious']
    ring
  have hodd : Odd (b.orderGap p) := by
    simpa only [p] using
      lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  have hupper : b.orderGap p ≤
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [p] using
      lemma79_typeI_leftSwitch_gap_le_twoE_add_one
        a b D C hleftPos
  by_cases hle : b.orderGap p ≤ 2 * (ramificationIndex K : Int)
  · have htargetFormula :=
      (b.beli2009Lemma27_iii p hle).2.mpr (Or.inr hodd)
    have hgapShiftQ : (b.orderGap p : ℚ) =
        (a.orderGap p : ℚ) + 3 := by
      exact_mod_cast hgapShift
    rw [htargetFormula, hsourceFormula, hgapShiftQ]
    linarith
  · have hlarge : 2 * (ramificationIndex K : Int) < b.orderGap p :=
      lt_of_not_ge hle
    have hgapEq : b.orderGap p =
        2 * (ramificationIndex K : Int) + 1 := by omega
    have htargetFormula := b.beli2009Lemma27_ii p hlarge.le
    rw [htargetFormula, hsourceFormula]
    unfold halfGapValue
    have hgapShiftQ : (b.orderGap p : ℚ) =
        (a.orderGap p : ℚ) + 3 := by
      exact_mod_cast hgapShift
    have hgapEqQ : (b.orderGap p : ℚ) =
        2 * (ramificationIndex K : ℚ) + 1 := by
      exact_mod_cast hgapEq
    rw [hgapShiftQ] at hgapEqQ
    linarith

end BONG.GoodBONG

end Bong
