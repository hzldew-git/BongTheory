/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIFirstTargetValue
import Bong.Bong.Beli2019Lemma79TypeICaseOneProfile

/-!
# Beli (2019), Lemma 7.9(ii), case 1: the source prefix representation

At the exceptional first type-I switch, the preceding representation alpha
is `2e - 1`, while the first central target alpha is nonnegative.  Together
with the two-unit order shift, these values activate condition 2.1(iii) for
the prefix of the source BONG.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The first order inequality in condition 2.1(iii) at the exceptional
case-one boundary. -/
theorem beli2019Lemma79_typeI_caseOne_centralOrderTrigger
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ =
      2 * (ramificationIndex K : Int) + 1) :
    b.order ⟨i.val - 1,
      (Nat.sub_le i.val 1).trans_lt i.lt_large⟩ <
      a.order ⟨i.val + 1, by
        have hrightBound :=
          C.right_le_last.trans_lt D.profile.lastDifference.bound
        omega⟩ := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiPos := i.pos
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hnextBound : i.val + 1 < n + 2 := by omega
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let next : Fin (n + 2) := ⟨i.val + 1, hnextBound⟩
  have hiNextOdd : Odd (i.val + 1) := by
    rcases hiEven with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hnextGapRaw := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val + 1) hiNextOdd (by omega) (by
      rcases C.right_even with ⟨k, hk⟩
      rcases hiEven with ⟨l, hl⟩
      omega)
  have hnextGap : a.order next = b.order next + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order next,
      ← b.orderSequence_entryOrZero_eq_order next]
    simpa only [next] using hnextGapRaw
  have hadjacentRaw := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    current hnextBound
  have hadjacent : -(2 * (ramificationIndex K : Int)) ≤
      b.order next - b.order current := by
    change -(2 * (ramificationIndex K : Int)) ≤
      b.order next - b.order current at hadjacentRaw
    exact hadjacentRaw
  have hpSucc : p.succ = current := by
    apply Fin.ext
    simp only [p, current, Fin.val_succ]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hgapOrder : b.order current -
      b.order ⟨i.val - 1, by omega⟩ =
        2 * (ramificationIndex K : Int) + 1 := by
    unfold orderGap at hgap
    rw [hpSucc, hpCast] at hgap
    exact hgap
  change b.order ⟨i.val - 1, by omega⟩ < a.order next
  omega

/-- The condition 2.1(iii) order trigger at the exceptional boundary,
including coincident and terminal type-I switches. -/
theorem beli2019Lemma79_typeI_caseOne_centralOrderTrigger_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hnextBound : i.val + 1 < n + 2)
    (hgap : b.orderGap ⟨i.val - 1, by omega⟩ =
      2 * (ramificationIndex K : Int) + 1) :
    b.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, hnextBound⟩ := by
  by_cases hstrict : C.leftSwitch < C.rightSwitch
  · exact beli2019Lemma79_typeI_caseOne_centralOrderTrigger
      a b D C hfirst hstrict i hleft hgap
  · have hcoincident : C.leftSwitch = C.rightSwitch := by
      have hle := C.left_le_anchor.trans C.anchor_le_right
      omega
    have hiPos := i.pos
    let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let previous : Fin (n + 2) := ⟨i.val - 1, by omega⟩
    let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
    let next : Fin (n + 2) := ⟨i.val + 1, hnextBound⟩
    have hadjacentRaw := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
      current hnextBound
    have hadjacent : -(2 * (ramificationIndex K : Int)) ≤
        b.order next - b.order current := by
      simpa only [current, next, GoodBONG.order] using hadjacentRaw
    have hpSucc : p.succ = current := by
      apply Fin.ext
      simp only [p, current, Fin.val_succ]
      omega
    have hpCast : p.castSucc = previous := by
      apply Fin.ext
      rfl
    have hgapOrder : b.order current - b.order previous =
        2 * (ramificationIndex K : Int) + 1 := by
      unfold orderGap at hgap
      rw [hpSucc, hpCast] at hgap
      exact hgap
    have hnextLower : b.order previous + 1 ≤ b.order next := by
      linarith [hgapOrder, hadjacent]
    clear hadjacentRaw hgap
    by_cases hrightLast : C.rightSwitch < D.profile.last
    · have hnextRaw := lemma69_v_typeI_next_source_target_order
        a b D C hfirst hrightLast
      have hnextRaw' :
          a.orderSequence.entryOrZero (i.val + 1) =
            b.orderSequence.entryOrZero (i.val + 1) + 1 := by
        rw [hleft, hcoincident]
        exact hnextRaw
      have hnextOrder : a.order next = b.order next + 1 := by
        rw [← a.orderSequence_entryOrZero_eq_order next,
          ← b.orderSequence_entryOrZero_eq_order next]
        simpa only [next] using hnextRaw'
      change b.order previous < a.order next
      calc
        b.order previous < b.order next :=
          Int.lt_iff_add_one_le.mpr hnextLower
        _ < b.order next + 1 := Int.lt_add_one_iff.mpr le_rfl
        _ = a.order next := hnextOrder.symm
    · have hrightEq : C.rightSwitch = D.profile.last := by
        have hle := C.right_le_last
        omega
      have hnextRaw := D.profile.lastDifference.after
        (i.val + 1) (by omega) hnextBound
      have hnextOrder : a.order next = b.order next := by
        rw [← a.orderSequence_entryOrZero_eq_order next,
          ← b.orderSequence_entryOrZero_eq_order next]
        simpa only [next] using hnextRaw
      change b.order previous < a.order next
      exact (Int.lt_iff_add_one_le.mpr hnextLower).trans_eq hnextOrder.symm

set_option maxHeartbeats 3000000 in
-- The trigger calculation transports three dependent boundary indices.
/-- Condition 2.1(iii) represents the exceptional source prefix occurring in
Lemma 7.9(ii), case 1. -/
theorem beli2019Lemma79_typeI_caseOne_sourcePrefixRepresentation
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hcentral : a.CentralRepresentationConditions b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hnextBound : i.val + 1 < n + 2)
    (hgap : b.orderGap ⟨i.val - 1, by omega⟩ =
      2 * (ramificationIndex K : Int) + 1) :
    DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiRight : i.val ≤ C.rightSwitch := by
    rw [hleft]
    exact C.left_le_anchor.trans C.anchor_le_right
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨k, hk⟩
    have hiPos := i.pos
    omega
  have hleftPos : 0 < C.leftSwitch := by omega
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, by omega⟩
  have hjCurrent : j.val ≤ n + 2 := by
    simp only [j]
    omega
  have hjPrevious : j.previous = i := by
    cases i
    rfl
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  have hcurrentGapRaw := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven (by omega) hiRight
  have hcurrentGap : b.order current = a.order current + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order current,
      ← a.orderSequence_entryOrZero_eq_order current]
    simpa only [current] using hcurrentGapRaw
  have hpSucc : p.succ = current := by
    apply Fin.ext
    simp only [p, current, Fin.val_succ]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hgapOrder : b.order current -
      b.order ⟨i.val - 1, by omega⟩ =
        2 * (ramificationIndex K : Int) + 1 := by
    unfold orderGap at hgap
    rw [hpSucc, hpCast] at hgap
    exact hgap
  have horderTrigger :=
    beli2019Lemma79_typeI_caseOne_centralOrderTrigger_complete
      a b D C hfirst i hleft hnextBound hgap
  have hpreviousTarget := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hpreviousTarget' : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ - 1 := by
    simpa only [hleft] using hpreviousTarget
  have hsourceAlphaFormula := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefect i (by omega) (by omega) hiEven
  have hsourceAlpha : a.alphaValue p =
      2 * (ramificationIndex K : ℚ) - 1 := by
    push_cast at hsourceAlphaFormula
    have hgapQ : (a.order current : ℚ) -
        (a.order ⟨i.val - 1, by omega⟩ : ℚ) =
        2 * (ramificationIndex K : ℚ) - 2 := by
      have hgapOrderQ : ((b.order current -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) =
          2 * (ramificationIndex K : ℚ) + 1 := by
        exact_mod_cast hgapOrder
      push_cast at hgapOrderQ
      have hcurrentGapQ : (b.order current : ℚ) =
          (a.order current : ℚ) + 2 := by
        exact_mod_cast hcurrentGap
      have hpreviousTargetQ :
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) =
            (a.order ⟨i.val - 1, by omega⟩ : ℚ) - 1 := by
        exact_mod_cast hpreviousTarget'
      linarith
    simpa only [p, current] using hsourceAlphaFormula.trans (by
      rw [hgapQ]
      ring)
  have hpreviousValueRaw :=
    beli2019Lemma69_ii_typeI_sourceLeftValue_complete
      a b D C hfirst hdefect i (by omega) (by omega) hiEven
  have hpreviousValue : a.representationAlphaValue b j.previous =
      2 * (ramificationIndex K : ℚ) - 1 := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b j.previous, hjPrevious]
    rw [hpreviousValueRaw]
    exact_mod_cast hsourceAlpha
  have hcurrentValue :=
    a.beli2019Lemma69_ii_typeI_firstTargetValue_complete
      b D C hfirst hleftPos horder hdefect (j.current hjCurrent) (by
        simp only [j, CentralRepresentationIndex.current]
        omega)
  have hcurrentNonneg : 0 ≤
      a.representationAlphaValue b (j.current hjCurrent) := by
    rw [hcurrentValue]
    exact (b.alpha_p2 _).1
  have htrigger : a.centralAlphaTrigger b j := by
    constructor
    · simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega]
        using horderTrigger
    · unfold centralAdjustedAlpha
      rw [dif_pos hjCurrent]
      norm_cast
      push_cast
      rw [hpreviousValue]
      have hcurrentGapQ : (b.order current : ℚ) =
          (a.order current : ℚ) + 2 := by
        exact_mod_cast hcurrentGap
      simpa only [j, current, CentralRepresentationIndex.current,
        Nat.add_one_sub_one] using
        (show 2 * (ramificationIndex K : ℚ) + (a.order current : ℚ) <
            (2 * (ramificationIndex K : ℚ) - 1) +
              ((b.order current : ℚ) +
                a.representationAlphaValue b (j.current hjCurrent)) by
          linarith)
  have hrepresented := hcentral j htrigger
  simpa only [j, Nat.add_one_sub_one] using hrepresented

end BONG.GoodBONG

end Bong
