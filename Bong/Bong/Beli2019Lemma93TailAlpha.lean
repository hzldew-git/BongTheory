/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailDefect

/-!
# Beli (2019), Lemma 9.3: alpha domination under head deletion

Every candidate defining the alpha invariant of a projected tail is the
shift of a candidate already present in the original good BONG.  Taking
finite minima gives `α_(i+1) ≤ α_i(tail)`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

@[simp]
theorem valueUnit_goodTail (b : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) :
    b.tail.valueUnit i = b.valueUnit i.succ := by
  change b.toBONG.tail.valueUnit i = b.toBONG.valueUnit i.succ
  exact b.toBONG.valueUnit_tail_general i

@[simp]
theorem order_goodTail (b : GoodBONG q L (n + 2))
    (i : Fin (n + 1)) :
    b.tail.order i = b.order i.succ := by
  change b.toBONG.tail.order i = b.toBONG.order i.succ
  exact b.toBONG.order_tail i

@[simp]
theorem adjacentProduct_tail (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.tail.adjacentProduct i = b.adjacentProduct i.succ := by
  unfold adjacentProduct
  rw [b.valueUnit_goodTail i.castSucc, b.valueUnit_goodTail i.succ]
  congr 3

@[simp]
theorem adjacentDefect_tail (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.tail.adjacentDefect i = b.adjacentDefect i.succ := by
  unfold adjacentDefect
  rw [b.adjacentProduct_tail i]

@[simp]
theorem halfGapCandidate_tail (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.tail.halfGapCandidate i = b.halfGapCandidate i.succ := by
  unfold halfGapCandidate
  rw [b.order_goodTail i.succ, b.order_goodTail i.castSucc]
  congr 4

@[simp]
theorem leftDefectCandidate_tail (b : GoodBONG q L (n + 2))
    (i j : Fin n) :
    b.tail.leftDefectCandidate i j =
      b.leftDefectCandidate i.succ j.succ := by
  unfold leftDefectCandidate
  rw [b.order_goodTail i.succ, b.order_goodTail j.castSucc,
    b.adjacentDefect_tail j]
  congr 4

@[simp]
theorem rightDefectCandidate_tail (b : GoodBONG q L (n + 2))
    (i j : Fin n) :
    b.tail.rightDefectCandidate i j =
      b.rightDefectCandidate i.succ j.succ := by
  unfold rightDefectCandidate
  rw [b.order_goodTail j.succ, b.order_goodTail i.castSucc,
    b.adjacentDefect_tail j]
  congr 4

/-- The shifted original alpha is bounded by the corresponding projected-tail
alpha. -/
theorem alpha_shift_le_tail (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.alpha i.succ ≤ b.tail.alpha i := by
  unfold alpha
  apply Finset.le_min'
  intro y hy
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
  · rw [b.halfGapCandidate_tail i]
    exact b.alpha_le_halfGapCandidate i.succ
  · rw [b.leftDefectCandidate_tail i j]
    exact b.alpha_le_leftDefectCandidate
      (Fin.succ_le_succ_iff.mpr hji)
  · rw [b.rightDefectCandidate_tail i j]
    exact b.alpha_le_rightDefectCandidate
      (Fin.succ_le_succ_iff.mpr hij)

/-- Rational-valued form used by the tail defect comparison. -/
theorem alphaValue_shift_le_tail (b : GoodBONG q L (n + 2)) (i : Fin n) :
    (b.alphaValue i.succ : WithTop ℚ) ≤
      (b.tail.alphaValue i : WithTop ℚ) := by
  simpa only [b.coe_alphaValue i.succ, b.tail.coe_alphaValue i] using
    b.alpha_shift_le_tail i

end BONG.GoodBONG

end Bong
