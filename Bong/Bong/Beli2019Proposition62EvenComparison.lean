/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EvenFirst

/-!
# Beli (2019), Proposition 6.2: assembled even comparisons

The boundary formulas are translated into the direct-or-pair clause of the
order on `W`-sequences at every zero-based even coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The defining comparison for `W(a)` and `W(b)` at coordinate `2k`. -/
theorem weightSequence_compare_even
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) (k : Fin n) :
    a.weightSequence.value ⟨2 * k.val, by omega⟩ ≤
        b.weightSequence.value ⟨2 * k.val, by omega⟩ ∨
      ∃ hk : 0 < k.val,
        a.weightSequence.value ⟨2 * k.val, by omega⟩ +
            a.weightSequence.value ⟨2 * k.val + 1, by omega⟩ ≤
          b.weightSequence.value ⟨2 * k.val - 1, by omega⟩ +
            b.weightSequence.value ⟨2 * k.val, by omega⟩ := by
  have hkBound : k.val < n := k.isLt
  let i : RepresentationIndex (n + 1) (n + 1) := {
    val := k.val + 1
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hiCurrent : (⟨i.val - 1, by
      have := i.lt_large
      omega⟩ : Fin (n + 1)) = k.castSucc := by
    apply Fin.ext
    simp only [i, Fin.val_castSucc]
    omega
  have hiNext : (⟨i.val, i.lt_large⟩ : Fin (n + 1)) = k.succ := by
    apply Fin.ext
    simp only [i, Fin.val_succ]
  have hiAlpha : (⟨i.val - 1, by
      have := i.lt_large
      omega⟩ : Fin n) = k := by
    apply Fin.ext
    simp only [i]
    omega
  by_cases hk0 : k.val = 0
  · have hfirst : i.val = 1 := by
      simp only [i]
      omega
    have hdirect := a.representationWeightEvenDirect_of_first
      b horder hdefect i hfirst
    left
    unfold representationWeightEvenDirect at hdirect
    rw [hiCurrent, hiAlpha] at hdirect
    simpa only [a.weightSequence_even k, b.weightSequence_even k] using hdirect
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    have hi : 1 < i.val := by
      simp only [i]
      omega
    rcases a.representationWeightEven_direct_or_pair b horder hdefect i hi with
      hdirect | hpair
    · left
      unfold representationWeightEvenDirect at hdirect
      rw [hiCurrent, hiAlpha] at hdirect
      simpa only [a.weightSequence_even k, b.weightSequence_even k] using hdirect
    · right
      refine ⟨hkpos, ?_⟩
      let previous : Fin n := ⟨k.val - 1, by omega⟩
      have hpreviousSucc : previous.succ = k.castSucc := by
        apply Fin.ext
        simp only [previous, Fin.val_succ, Fin.val_castSucc]
        omega
      have hiPrevious : (⟨i.val - 2, by
          have := i.lt_large
          omega⟩ : Fin n) = previous := by
        apply Fin.ext
        simp only [i, previous]
        omega
      have hpreviousCoordinate :
          (⟨2 * previous.val + 1, by omega⟩ : Fin (2 * n)) =
            ⟨2 * k.val - 1, by omega⟩ := by
        apply Fin.ext
        simp only [previous]
        omega
      have hpairQ : (a.order k.castSucc : ℚ) + (a.order k.succ : ℚ) ≤
          2 * (b.order k.castSucc : ℚ) + b.alphaValue k -
            b.alphaValue previous := by
        unfold representationWeightEvenPair at hpair
        rw [hiCurrent, hiNext, hiAlpha, hiPrevious] at hpair
        exact hpair
      rw [a.weightSequence_even k, a.weightSequence_odd k,
        b.weightSequence_even k, ← hpreviousCoordinate,
        b.weightSequence_odd previous, hpreviousSucc]
      linarith

end BONG.GoodBONG

end Bong
