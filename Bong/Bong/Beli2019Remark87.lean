/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma66
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Remark 8.7

This file records the consequences used throughout Section 8 when three
consecutive BONG orders have equal outer entries.  Corollary 2.3 supplies the
endpoint and half-gap identities, Lemma 6.6 supplies parity, and Lemma 7.4(iii)
computes the two bracketed adjacent defects.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The first value in the three-term window of Remark 8.7. -/
def remark87PreviousValue (p : Fin (N + 1)) : Fin (N + 3) :=
  ⟨p.1, by omega⟩

/-- The middle value in the three-term window of Remark 8.7. -/
def remark87MiddleValue (p : Fin (N + 1)) : Fin (N + 3) :=
  ⟨p.1 + 1, by omega⟩

/-- The last value in the three-term window of Remark 8.7. -/
def remark87NextValue (p : Fin (N + 1)) : Fin (N + 3) :=
  ⟨p.1 + 2, by omega⟩

/-- The alpha index immediately before the middle value. -/
def remark87PreviousAlpha (p : Fin (N + 1)) : Fin (N + 2) :=
  ⟨p.1, by omega⟩

/-- The alpha index immediately after the middle value. -/
def remark87CurrentAlpha (p : Fin (N + 1)) : Fin (N + 2) :=
  ⟨p.1 + 1, by omega⟩

/-- All consequences collected in the unnumbered display conventionally
referred to as Remark 8.7. -/
structure Beli2019Remark87Consequences
    (b : GoodBONG q L (N + 3)) (p : Fin (N + 1)) : Prop where
  previous_middle_modEq : Int.ModEq 2
    (b.order (remark87PreviousValue p))
    (b.order (remark87MiddleValue p))
  middle_next_modEq : Int.ModEq 2
    (b.order (remark87MiddleValue p))
    (b.order (remark87NextValue p))
  leftEndpoint_eq :
    b.alphaLeftEndpoint (remark87PreviousAlpha p) =
      b.alphaLeftEndpoint (remark87CurrentAlpha p)
  rightEndpoint_eq :
    b.alphaRightEndpoint (remark87PreviousAlpha p) =
      b.alphaRightEndpoint (remark87CurrentAlpha p)
  currentAlpha_eq :
    b.alphaValue (remark87CurrentAlpha p) =
      ((b.order (remark87PreviousValue p) -
        b.order (remark87MiddleValue p) : Int) : ℚ) +
        b.alphaValue (remark87PreviousAlpha p)
  previousAlpha_eq :
    b.alphaValue (remark87PreviousAlpha p) =
      ((b.order (remark87MiddleValue p) -
        b.order (remark87NextValue p) : Int) : ℚ) +
        b.alphaValue (remark87CurrentAlpha p)
  attainsHalfGap_iff :
    b.AttainsHalfGap (remark87PreviousAlpha p) ↔
      b.AttainsHalfGap (remark87CurrentAlpha p)
  alphaSum_le_twoE :
    b.alphaValue (remark87PreviousAlpha p) +
        b.alphaValue (remark87CurrentAlpha p) ≤
      2 * (ramificationIndex K : ℚ)
  alphaSum_eq_twoE_iff :
    b.alphaValue (remark87PreviousAlpha p) +
          b.alphaValue (remark87CurrentAlpha p) =
        2 * (ramificationIndex K : ℚ) ↔
      b.AttainsHalfGap (remark87PreviousAlpha p)
  previousCappedDefect_eq :
    b.truncatedPrefixDefect b (-1) p.1 (p.1 + 2) =
      (b.alphaValue (remark87CurrentAlpha p) : WithTop ℚ)
  currentCappedDefect_eq :
    b.truncatedPrefixDefect b (-1) (p.1 + 1) (p.1 + 3) =
      (b.alphaValue (remark87PreviousAlpha p) : WithTop ℚ)
  currentAlpha_le_previousRawDefect :
    (b.alphaValue (remark87CurrentAlpha p) : WithTop ℚ) ≤
      b.adjacentDefect (remark87PreviousAlpha p)
  previousAlpha_le_currentRawDefect :
    (b.alphaValue (remark87PreviousAlpha p) : WithTop ℚ) ≤
      b.adjacentDefect (remark87CurrentAlpha p)

/-- Beli (2019), Remark 8.7, in zero-based indexing. -/
theorem beli2019Remark87
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3)) (p : Fin (N + 1))
    (houter :
      b.order (remark87PreviousValue p) =
        b.order (remark87NextValue p)) :
    Beli2019Remark87Consequences b p := by
  let previousValue := remark87PreviousValue p
  let middleValue := remark87MiddleValue p
  let nextValue := remark87NextValue p
  let previousAlpha := remark87PreviousAlpha p
  let currentAlpha := remark87CurrentAlpha p
  have hpreviousValue : previousAlpha.castSucc = previousValue := by
    apply Fin.ext
    rfl
  have hmiddleFromPrevious : previousAlpha.succ = middleValue := by
    apply Fin.ext
    rfl
  have hmiddleFromCurrent : currentAlpha.castSucc = middleValue := by
    apply Fin.ext
    rfl
  have hnextValue : currentAlpha.succ = nextValue := by
    apply Fin.ext
    rfl
  have hsum :
      b.adjacentOrderSum previousAlpha =
        b.adjacentOrderSum currentAlpha := by
    unfold adjacentOrderSum
    rw [hpreviousValue, hmiddleFromPrevious, hmiddleFromCurrent, hnextValue]
    rw [houter]
    ring
  have hcor := b.beli2009Corollary23 previousAlpha currentAlpha
    (by change p.1 ≤ p.1 + 1; omega) hsum
  have hleft :
      b.alphaLeftEndpoint previousAlpha =
        b.alphaLeftEndpoint currentAlpha :=
    (hcor.leftEndpoint_eq currentAlpha (by
      change p.1 ≤ p.1 + 1
      omega) le_rfl).symm
  have hright :
      b.alphaRightEndpoint previousAlpha =
        b.alphaRightEndpoint currentAlpha :=
    (hcor.rightEndpoint_eq currentAlpha (by
      change p.1 ≤ p.1 + 1
      omega) le_rfl).symm
  have hcurrentAlpha :
      b.alphaValue currentAlpha =
        ((b.order previousValue - b.order middleValue : Int) : ℚ) +
          b.alphaValue previousAlpha := by
    have h := hleft
    unfold alphaLeftEndpoint at h
    rw [hpreviousValue, hmiddleFromCurrent] at h
    push_cast at h ⊢
    linarith
  have hpreviousAlpha :
      b.alphaValue previousAlpha =
        ((b.order middleValue - b.order nextValue : Int) : ℚ) +
          b.alphaValue currentAlpha := by
    have h := hright
    unfold alphaRightEndpoint at h
    rw [hmiddleFromPrevious, hnextValue] at h
    push_cast at h ⊢
    linarith
  have hhalf :
      b.AttainsHalfGap previousAlpha ↔ b.AttainsHalfGap currentAlpha :=
    (hcor.attainsHalfGap_iff currentAlpha (by
      change p.1 ≤ p.1 + 1
      omega) le_rfl).symm
  have hhalfSum :
      b.halfGapValue previousAlpha + b.halfGapValue currentAlpha =
        2 * (ramificationIndex K : ℚ) := by
    unfold halfGapValue orderGap
    rw [hpreviousValue, hmiddleFromPrevious, hmiddleFromCurrent, hnextValue]
    rw [houter]
    push_cast
    ring
  have hsumLe :
      b.alphaValue previousAlpha + b.alphaValue currentAlpha ≤
        2 * (ramificationIndex K : ℚ) := by
    calc
      b.alphaValue previousAlpha + b.alphaValue currentAlpha ≤
          b.halfGapValue previousAlpha + b.halfGapValue currentAlpha :=
        add_le_add (b.alphaValue_le_halfGapValue previousAlpha)
          (b.alphaValue_le_halfGapValue currentAlpha)
      _ = 2 * (ramificationIndex K : ℚ) := hhalfSum
  have hsumEq :
      b.alphaValue previousAlpha + b.alphaValue currentAlpha =
          2 * (ramificationIndex K : ℚ) ↔
        b.AttainsHalfGap previousAlpha := by
    constructor
    · intro heq
      unfold AttainsHalfGap
      apply le_antisymm (b.alphaValue_le_halfGapValue previousAlpha)
      apply le_of_not_gt
      intro hlt
      have hcurrentLe := b.alphaValue_le_halfGapValue currentAlpha
      have hstrict := add_lt_add_of_lt_of_le hlt hcurrentLe
      rw [heq, hhalfSum] at hstrict
      exact (lt_irrefl _ hstrict)
    · intro hprev
      have hcurrent : b.AttainsHalfGap currentAlpha := hhalf.mp hprev
      unfold AttainsHalfGap at hprev hcurrent
      rw [hprev, hcurrent, hhalfSum]
  have hpreviousCapped :
      b.truncatedPrefixDefect b (-1) p.1 (p.1 + 2) =
        (b.alphaValue currentAlpha : WithTop ℚ) := by
    have hlower := b.order_sub_add_alpha_le_cappedAdjacent previousAlpha
    rw [hpreviousValue, hmiddleFromPrevious] at hlower
    have hlower' :
        (b.alphaValue currentAlpha : WithTop ℚ) ≤
          b.truncatedPrefixDefect b (-1) p.1 (p.1 + 2) := by
      rw [hcurrentAlpha]
      simpa only [previousAlpha, remark87PreviousAlpha] using hlower
    have hupper := b.truncatedPrefixDefect_le_rightCap b (-1)
      p.1 (p.1 + 2)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hupper
    have hindex :
        (⟨p.1 + 2 - 1, by omega⟩ : Fin (N + 2)) = currentAlpha := by
      apply Fin.ext
      dsimp only [currentAlpha, remark87CurrentAlpha]
      omega
    rw [hindex] at hupper
    exact le_antisymm hupper hlower'
  have hcurrentCapped :
      b.truncatedPrefixDefect b (-1) (p.1 + 1) (p.1 + 3) =
        (b.alphaValue previousAlpha : WithTop ℚ) := by
    have hlower := b.order_sub_add_alpha_le_cappedAdjacent currentAlpha
    rw [hmiddleFromCurrent, hnextValue] at hlower
    have hlower' :
        (b.alphaValue previousAlpha : WithTop ℚ) ≤
          b.truncatedPrefixDefect b (-1) (p.1 + 1) (p.1 + 3) := by
      rw [hpreviousAlpha]
      simpa only [currentAlpha, remark87CurrentAlpha,
        show p.1 + 1 + 2 = p.1 + 3 by omega] using hlower
    have hupper := b.truncatedPrefixDefect_le_leftCap b (-1)
      (p.1 + 1) (p.1 + 3)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hupper
    have hindex :
        (⟨p.1 + 1 - 1, by omega⟩ : Fin (N + 2)) = previousAlpha := by
      apply Fin.ext
      dsimp only [previousAlpha, remark87PreviousAlpha]
      omega
    rw [hindex] at hupper
    exact le_antisymm hupper hlower'
  have hpreviousRaw :
      (b.alphaValue currentAlpha : WithTop ℚ) ≤
        b.adjacentDefect previousAlpha := by
    rw [← hpreviousCapped]
    have hraw := b.truncatedPrefixDefect_le_defect b (-1) p.1 (p.1 + 2)
    exact hraw.trans_eq (by
      simpa only [previousAlpha, remark87PreviousAlpha] using
        b.defectOrder_prefixPair_eq_adjacentDefect previousAlpha)
  have hcurrentRaw :
      (b.alphaValue previousAlpha : WithTop ℚ) ≤
        b.adjacentDefect currentAlpha := by
    rw [← hcurrentCapped]
    have hraw := b.truncatedPrefixDefect_le_defect b (-1)
      (p.1 + 1) (p.1 + 3)
    exact hraw.trans_eq (by
      simpa only [currentAlpha, remark87CurrentAlpha] using
        b.defectOrder_prefixPair_eq_adjacentDefect currentAlpha)
  have h66 := b.beli2019Lemma66_i previousValue nextValue
    (by change p.1 ≤ p.1 + 2; omega)
    (by
      change Even (p.1 + 2 - p.1)
      refine ⟨1, ?_⟩
      omega) houter
  have hmiddleMod : Int.ModEq 2 (b.order middleValue)
      (b.order previousValue) :=
    h66.order_modEq middleValue
      (by change p.1 ≤ p.1 + 1; omega)
      (by change p.1 + 1 ≤ p.1 + 2; omega)
  have hpreviousMiddle : Int.ModEq 2 (b.order previousValue)
      (b.order middleValue) := hmiddleMod.symm
  have hmiddleNext : Int.ModEq 2 (b.order middleValue)
      (b.order nextValue) := by
    rw [← houter]
    exact hmiddleMod
  exact {
    previous_middle_modEq := hpreviousMiddle
    middle_next_modEq := hmiddleNext
    leftEndpoint_eq := hleft
    rightEndpoint_eq := hright
    currentAlpha_eq := hcurrentAlpha
    previousAlpha_eq := hpreviousAlpha
    attainsHalfGap_iff := hhalf
    alphaSum_le_twoE := hsumLe
    alphaSum_eq_twoE_iff := hsumEq
    previousCappedDefect_eq := hpreviousCapped
    currentCappedDefect_eq := hcurrentCapped
    currentAlpha_le_previousRawDefect := hpreviousRaw
    previousAlpha_le_currentRawDefect := hcurrentRaw }

end BONG.GoodBONG

end Bong
