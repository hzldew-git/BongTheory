/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlphaValueExt
import Bong.Bong.Beli2019Corollary811

/-!
# Localizing the first alpha at an initial ternary segment

The first alpha of a long good BONG is already the first alpha of its initial
ternary segment once every right-defect candidate beginning at the third pair
is bounded below by that ternary alpha.  This is the finite-minimum argument
used in Beli (2019), Lemma 9.10.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Localization of the first alpha at the literal initial ternary segment. -/
def initialTernaryFirstAlphaLocalization : AlphaLocalizationIndex (N + 2) where
  start := 0
  pivot := 0
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- If every candidate contributed by a pair outside the first ternary segment
is at least the first alpha of that segment, the global first alpha is exactly
the ternary one. -/
theorem firstAlphaValue_eq_initialTernary_of_outsideRightCandidate
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (w : BONG.SegmentWitness b.toBONG 0 3 (by omega))
    (houtside : ∀ j : Fin (N + 2), 2 ≤ j.1 →
      ((w.toGoodBONG b.good).alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        b.rightDefectCandidate (0 : Fin (N + 2)) j) :
    b.alphaValue (0 : Fin (N + 2)) =
      (w.toGoodBONG b.good).alphaValue (0 : Fin 2) := by
  let p := initialTernaryFirstAlphaLocalization (N := N)
  let first := w.toGoodBONG b.good
  have hpivot : p.pivotFin = (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocal := b.beli2009Lemma21_le_segmentAlpha p w
  rw [hpivot, hlocalPivot] at hglobalLeLocal
  have hglobalLeLocalValue :
      b.alphaValue (0 : Fin (N + 2)) ≤ first.alphaValue (0 : Fin 2) := by
    apply WithTop.coe_le_coe.mp
    rw [b.coe_alphaValue, first.coe_alphaValue]
    exact hglobalLeLocal
  apply le_antisymm
  · exact hglobalLeLocalValue
  · apply WithTop.coe_le_coe.mp
    rw [b.coe_alphaValue, first.coe_alphaValue]
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · have hlocal := first.alpha_le_halfGapCandidate p.localPivot
      have hsegment := b.segment_halfGapCandidate_local p w
      rw [hlocalPivot] at hlocal
      rw [hpivot, hlocalPivot] at hsegment
      rw [← hsegment]
      exact hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ (0 : Fin (N + 2)) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hjzero : j.1 = 0 := by
        change j.1 ≤ 0 at hji
        omega
      have hstart : p.start ≤ j.1 := by
        dsimp [p, initialTernaryFirstAlphaLocalization]
        omega
      have hstop : j.1 < p.stop := by
        dsimp [p, initialTernaryFirstAlphaLocalization]
        omega
      have hjpivot : j ≤ p.pivotFin := by
        simpa only [hpivot] using hji
      have hlocalIndex :
          p.localAdjacent j hstart hstop ≤ p.localPivot := by
        change j.1 - p.start ≤ p.pivot - p.start
        change j.1 ≤ p.pivot at hjpivot
        omega
      have hlocal := first.alpha_le_leftDefectCandidate hlocalIndex
      have hsegment := b.segment_leftDefectCandidate_local
        p w j hstart hstop hjpivot
      rw [hlocalPivot] at hlocal
      rw [hpivot, hlocalPivot] at hsegment
      rw [← hsegment]
      exact hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : (0 : Fin (N + 2)) ≤ j := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      by_cases hinside : j.1 < p.stop
      · have hstart : p.start ≤ j.1 := by
          dsimp [p, initialTernaryFirstAlphaLocalization]
          omega
        have hpivotj : p.pivotFin ≤ j := by
          simpa only [hpivot] using hij
        have hlocalIndex : p.localPivot ≤
            p.localAdjacent j hstart hinside := by
          change p.pivot - p.start ≤ j.1 - p.start
          change p.pivot ≤ j.1 at hpivotj
          omega
        have hlocal := first.alpha_le_rightDefectCandidate hlocalIndex
        have hsegment := b.segment_rightDefectCandidate_local
          p w j hstart hinside hpivotj
        rw [hlocalPivot] at hlocal
        rw [hpivot, hlocalPivot] at hsegment
        rw [← hsegment]
        exact hlocal
      · have hjTwo : 2 ≤ j.1 := by
          dsimp [p, initialTernaryFirstAlphaLocalization] at hinside
          omega
        rw [← first.coe_alphaValue]
        exact houtside j hjTwo

end BONG.GoodBONG

end Bong
