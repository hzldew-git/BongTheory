/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Early

/-!
# Beli (2019), Lemma 9.3: monotonicity after deleting equal heads

The proof of Lemma 9.3 first observes that the shifted original comparison
invariant is never larger than the comparison invariant of the two projected
tails.  Raw defects are unchanged because the equal heads contribute a square,
while removing an endpoint can only enlarge an alpha cap.
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

/-- Every shifted original prefix alpha cap is at most the corresponding tail
cap, including the two endpoint cases. -/
theorem prefixAlphaCap_shift_le_tail_general
    (a : GoodBONG q L (n + 2)) (i : Nat) (hile : i ≤ n + 1) :
    a.prefixAlphaCap (i + 1) ≤ a.tail.prefixAlphaCap i := by
  by_cases hzero : i = 0
  · subst i
    rw [a.tail.prefixAlphaCap_zero]
    exact le_top
  by_cases hinterior : i < n + 1
  · exact a.prefixAlphaCap_shift_le_tail a.alphaValue_shift_le_tail
      i (by omega) hinterior
  · have hlast : i = n + 1 := by omega
    subst i
    rw [a.tail.prefixAlphaCap_last]
    exact le_top

/-- General unequal-prefix form of the capped-defect monotonicity used in
Lemma 9.3. -/
theorem truncatedPrefixDefect_shift_le_tail_general
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0) (ε : Kˣ)
    (i j : Nat) (hile : i ≤ n + 1) (hjle : j ≤ n + 1) :
    a.truncatedPrefixDefect b ε (i + 1) (j + 1) ≤
      a.tail.truncatedPrefixDefect b.tail ε i j := by
  unfold truncatedPrefixDefect
  rw [a.defectOrder_shiftedPrefixes_eq_tail b hhead ε i j hile hjle]
  exact min_le_min le_rfl
    (min_le_min
      (a.prefixAlphaCap_shift_le_tail_general i hile)
      (b.prefixAlphaCap_shift_le_tail_general j hjle))

/-- The shifted original primary comparison candidate is no larger than the
tail primary candidate. -/
theorem representationPrimaryDefect_shift_le_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.representationPrimaryDefect b i.tailShift ≤
      a.tail.representationPrimaryDefect b.tail i := by
  have hilarge := i.lt_large
  have hipos := i.pos
  have hdefect := a.truncatedPrefixDefect_shift_le_tail_general
    b hhead (-1) (i.val + 1) (i.val - 1) (by omega) (by omega)
  unfold representationPrimaryDefect
  rw [a.order_goodTail, b.order_goodTail]
  have htarget : i.val + 1 + 1 = i.tailShift.val + 1 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 1 + 1 = i.tailShift.val - 1 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, hsourceIndex]
  exact add_le_add_right hdefect _

/-- At an interior tail boundary, the shifted original secondary candidate is
no larger than the tail secondary candidate. -/
theorem representationSecondaryDefect_shift_le_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hinterior : 1 < i.val ∧ i.val + 1 < n + 1) :
    a.representationSecondaryDefect b i.tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val]
          omega⟩ ≤
      a.tail.representationSecondaryDefect b.tail i hinterior := by
  have hilarge := i.lt_large
  have hdefect := a.truncatedPrefixDefect_shift_le_tail_general
    b hhead 1 (i.val + 2) (i.val - 2) (by omega) (by omega)
  unfold representationSecondaryDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  have htarget : i.val + 2 + 1 = i.tailShift.val + 2 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 2 + 1 = i.tailShift.val - 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have htargetNextIndex :
      (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex :
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex, hsourceIndex]
  exact add_le_add_right hdefect _

/-- Beli (2019), Lemma 9.3, proof line `A_i^* ≥ A_i`: deleting equal heads
can only increase the comparison invariant. -/
theorem representationAlpha_shift_le_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.representationAlpha b i.tailShift ≤
      a.tail.representationAlpha b.tail i := by
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i]
  apply le_min
  · rw [a.representationHalfGap_tail_eq_shift b i]
    exact a.representationAlpha_le_halfGap b i.tailShift
  · by_cases hinterior : 1 < i.val ∧ i.val + 1 < n + 1
    · rw [a.tail.representationAlphaPrime_eq_min_primary_secondary
        b.tail i hinterior]
      apply le_min
      · exact (a.representationAlpha_le_prime b i.tailShift).trans
          ((a.representationAlphaPrime_le_primaryDefect b i.tailShift).trans
            (a.representationPrimaryDefect_shift_le_tail b hhead i))
      · have horiginalInterior :
            1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
          simp only [RepresentationIndex.tailShift_val]
          omega
        exact (a.representationAlpha_le_prime b i.tailShift).trans
          ((a.representationAlphaPrime_le_secondaryDefect
              b i.tailShift horiginalInterior).trans
            (a.representationSecondaryDefect_shift_le_tail
              b hhead i hinterior))
    · rw [a.tail.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i hinterior]
      exact (a.representationAlpha_le_prime b i.tailShift).trans
        ((a.representationAlphaPrime_le_primaryDefect b i.tailShift).trans
          (a.representationPrimaryDefect_shift_le_tail b hhead i))

/-- To establish the equality required at an important index in Lemma 9.3,
it is enough to prove the paper's nontrivial reverse inequality. -/
theorem representationAlpha_tail_eq_shift_of_tail_le_shift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hreverse : a.tail.representationAlpha b.tail i ≤
      a.representationAlpha b i.tailShift) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift :=
  le_antisymm hreverse (a.representationAlpha_shift_le_tail b hhead i)

end BONG.GoodBONG

end Bong
