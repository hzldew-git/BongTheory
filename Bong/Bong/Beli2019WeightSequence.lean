/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SequenceDual
import Bong.Bong.Beli2006SectionThree

/-!
# Beli (2019), the `W`-sequence

This file formalizes the rational sequence
`W(L) = (R_1 + alpha_1, R_2 - alpha_1, ..., R_n - alpha_(n-1))`
from the end of Section 1.  A reusable interleaving construction separates
the finite-index arithmetic from Beli's alpha monotonicity property P1.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Alternate between two sequences of the same length. -/
def interleaveValue {n : Nat} (left right : Fin n → Gamma)
    (i : Fin (2 * n)) : Gamma :=
  if i.1 % 2 = 0 then
    left ⟨i.1 / 2, by omega⟩
  else
    right ⟨i.1 / 2, by omega⟩

/-- Interleaving two monotone sequences gives an element of `B_(2n)`. -/
def interleave {n : Nat} (left right : Fin n → Gamma)
    (leftMono : ∀ (i : Nat) (hi : i + 1 < n),
      left ⟨i, by omega⟩ ≤ left ⟨i + 1, hi⟩)
    (rightMono : ∀ (i : Nat) (hi : i + 1 < n),
      right ⟨i, by omega⟩ ≤ right ⟨i + 1, hi⟩) :
    BeliOrderSequence (2 * n) Gamma where
  value := interleaveValue left right
  twoStep := by
    intro i hi
    have hdiv : (i + 2) / 2 = i / 2 + 1 := by omega
    by_cases heven : i % 2 = 0
    · have hevenNext : (i + 2) % 2 = 0 := by omega
      rw [interleaveValue, if_pos heven, interleaveValue, if_pos hevenNext]
      have hmono := leftMono (i / 2) (by omega)
      simpa only [hdiv] using hmono
    · have hodd : i % 2 = 1 := by omega
      have hoddNext : (i + 2) % 2 = 1 := by omega
      rw [interleaveValue, if_neg heven, interleaveValue,
        if_neg (by omega : (i + 2) % 2 ≠ 0)]
      have hmono := rightMono (i / 2) (by omega)
      simpa only [hdiv] using hmono

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem interleave_value_even {n : Nat} (left right : Fin n → Gamma)
    (leftMono : ∀ (i : Nat) (hi : i + 1 < n),
      left ⟨i, by omega⟩ ≤ left ⟨i + 1, hi⟩)
    (rightMono : ∀ (i : Nat) (hi : i + 1 < n),
      right ⟨i, by omega⟩ ≤ right ⟨i + 1, hi⟩)
    (i : Fin n) :
    (interleave left right leftMono rightMono).value
      ⟨2 * i.1, by omega⟩ = left i := by
  simp [interleave, interleaveValue]

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem interleave_value_odd {n : Nat} (left right : Fin n → Gamma)
    (leftMono : ∀ (i : Nat) (hi : i + 1 < n),
      left ⟨i, by omega⟩ ≤ left ⟨i + 1, hi⟩)
    (rightMono : ∀ (i : Nat) (hi : i + 1 < n),
      right ⟨i, by omega⟩ ≤ right ⟨i + 1, hi⟩)
    (i : Fin n) :
    (interleave left right leftMono rightMono).value
      ⟨2 * i.1 + 1, by omega⟩ = right i := by
  change interleaveValue left right ⟨2 * i.1 + 1, by omega⟩ = right i
  have hmod : (2 * i.1 + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * i.1 + 1) / 2 = i.1 := by omega
  rw [interleaveValue, if_neg hmod]
  apply congrArg right
  exact Fin.ext hdiv

/-- Reversal sends an even interleaving position to the corresponding odd
position at the opposite end. -/
@[simp]
theorem reverseNegate_interleave_value_even {n : Nat}
    (left right : Fin n → Gamma)
    (leftMono : ∀ (i : Nat) (hi : i + 1 < n),
      left ⟨i, by omega⟩ ≤ left ⟨i + 1, hi⟩)
    (rightMono : ∀ (i : Nat) (hi : i + 1 < n),
      right ⟨i, by omega⟩ ≤ right ⟨i + 1, hi⟩)
    (i : Fin n) :
    (interleave left right leftMono rightMono).reverseNegate.value
      ⟨2 * i.1, by omega⟩ = -right (Fin.rev i) := by
  change -((interleave left right leftMono rightMono).value
    (Fin.rev ⟨2 * i.1, by omega⟩)) = -right (Fin.rev i)
  have hindex : Fin.rev (⟨2 * i.1, by omega⟩ : Fin (2 * n)) =
      ⟨2 * (Fin.rev i).1 + 1, by omega⟩ := by
    apply Fin.ext
    simp
    omega
  rw [hindex, interleave_value_odd]

/-- Reversal sends an odd interleaving position to the corresponding even
position at the opposite end. -/
@[simp]
theorem reverseNegate_interleave_value_odd {n : Nat}
    (left right : Fin n → Gamma)
    (leftMono : ∀ (i : Nat) (hi : i + 1 < n),
      left ⟨i, by omega⟩ ≤ left ⟨i + 1, hi⟩)
    (rightMono : ∀ (i : Nat) (hi : i + 1 < n),
      right ⟨i, by omega⟩ ≤ right ⟨i + 1, hi⟩)
    (i : Fin n) :
    (interleave left right leftMono rightMono).reverseNegate.value
      ⟨2 * i.1 + 1, by omega⟩ = -left (Fin.rev i) := by
  change -((interleave left right leftMono rightMono).value
    (Fin.rev ⟨2 * i.1 + 1, by omega⟩)) = -left (Fin.rev i)
  have hindex : Fin.rev (⟨2 * i.1 + 1, by omega⟩ : Fin (2 * n)) =
      ⟨2 * (Fin.rev i).1, by omega⟩ := by
    apply Fin.ext
    simp
    omega
  rw [hindex, interleave_value_even]

end BeliOrderSequence

namespace BONG.GoodBONG

open BeliOrderSequence

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- The rational-valued invariant `W(L)` from Beli (2019), Section 1. -/
noncomputable def weightSequence (b : GoodBONG q L (n + 1)) :
    BeliOrderSequence (2 * n) ℚ :=
  BeliOrderSequence.interleave
    b.alphaLeftEndpoint (fun i ↦ -b.alphaRightEndpoint i)
    (fun i hi ↦ (b.alpha_p1 ⟨i, by omega⟩ hi).1)
    (fun i hi ↦ neg_le_neg (b.alpha_p1 ⟨i, by omega⟩ hi).2)

@[simp]
theorem weightSequence_even (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.weightSequence.value ⟨2 * i.1, by omega⟩ =
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  simp [weightSequence, alphaLeftEndpoint]

@[simp]
theorem weightSequence_odd (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.weightSequence.value ⟨2 * i.1 + 1, by omega⟩ =
      (b.order i.succ : ℚ) - b.alphaValue i := by
  simp [weightSequence, alphaRightEndpoint]
  abel

/-- The `W`-sequence reverses and changes sign under lattice duality. -/
theorem exists_reverseDual_weightSequence
    [BONGStructuralLaws.{u, v} K] (b : GoodBONG q L (n + 1)) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) (n + 1),
      c.weightSequence = b.weightSequence.reverseNegate := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, _, _, horders, halphas⟩
  refine ⟨c, ?_⟩
  apply BeliOrderSequence.ext
  funext i
  rcases Nat.mod_two_eq_zero_or_one i.1 with heven | hodd
  · let j : Fin n := ⟨i.1 / 2, by omega⟩
    have hindex : i = ⟨2 * j.1, by
        simp only [j]
        omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    rw [c.weightSequence_even, horders j.castSucc, halphas j]
    unfold weightSequence
    rw [BeliOrderSequence.reverseNegate_interleave_value_even]
    simp only [alphaRightEndpoint]
    rw [Fin.rev_castSucc]
    push_cast
    ring
  · let j : Fin n := ⟨i.1 / 2, by omega⟩
    have hindex : i = ⟨2 * j.1 + 1, by
        simp only [j]
        omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    rw [c.weightSequence_odd, horders j.succ, halphas j]
    unfold weightSequence
    rw [BeliOrderSequence.reverseNegate_interleave_value_odd]
    simp only [alphaLeftEndpoint]
    rw [Fin.rev_succ]
    push_cast
    ring

end BONG.GoodBONG

end Bong
