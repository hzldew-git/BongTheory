/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaCompression

/-!
# A proof of Beli (2009/2010), Lemma 2.1

`Beli2009AlphaMonotonicity` exposes the finite-minimum statement of Lemma 2.1
as a law.  This module discharges that law.  The candidates of a consecutive
segment are exactly the candidates in the corresponding localization block;
replacing a nonempty subset of a finite linearly ordered set by its minimum
does not alter the minimum of the whole set.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The half-gap candidate is preserved by passage to a consecutive
segment. -/
theorem segment_halfGapCandidate_local
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (w.toGoodBONG b.good).halfGapCandidate s.localPivot =
      b.halfGapCandidate s.pivotFin := by
  have hp := localAdjacent_pivot (n := n) s
  have hleft := b.segment_order_local_castSucc s w s.pivotFin
    s.start_le_pivot s.pivot_lt_stop
  have hright := b.segment_order_local_succ s w s.pivotFin
    s.start_le_pivot s.pivot_lt_stop
  rw [← hp]
  unfold halfGapCandidate
  rw [hleft, hright]

/-- The complete candidate set of a consecutive segment is exactly the
localization block in the ambient BONG. -/
theorem segment_alphaCandidates_eq_localizationBlock
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (w.toGoodBONG b.good).alphaCandidates s.localPivot =
      b.localizationBlockCandidates s := by
  classical
  ext x
  simp only [alphaCandidates, localizationBlockCandidates,
    Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro (hx | hx | hx)
    · exact Or.inl (hx.trans (b.segment_halfGapCandidate_local s w))
    · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
      have hjle : j ≤ s.localPivot :=
        (Finset.mem_filter.mp hj).2
      let g : Fin n := ⟨s.start + j.val, by
        have hjlt := j.isLt
        have hstop := s.stop_lt
        have hstart := s.start_le_pivot.trans s.pivot_lt_stop.le
        omega⟩
      have hgstart : s.start ≤ g.val := by
        simp only [g]
        omega
      have hgstop : g.val < s.stop := by
        have hjlt := j.isLt
        have hstart := s.start_le_pivot.trans s.pivot_lt_stop.le
        simp only [g]
        omega
      have hgpivot : g ≤ s.pivotFin := by
        change s.start + j.val ≤ s.pivot
        change j.val ≤ s.pivot - s.start at hjle
        have hstartPivot := s.start_le_pivot
        omega
      have hlocal : s.localAdjacent g hgstart hgstop = j := by
        apply Fin.ext
        simp only [AlphaLocalizationIndex.localAdjacent_val, g]
        omega
      have hcand := b.segment_leftDefectCandidate_local
        s w g hgstart hgstop hgpivot
      rw [hlocal] at hcand
      refine Or.inr (Or.inl (Finset.mem_image.mpr ⟨g, ?_, ?_⟩))
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ g, hgstart, hgpivot⟩
      · exact hcand.symm.trans hx
    · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
      have hjge : s.localPivot ≤ j :=
        (Finset.mem_filter.mp hj).2
      let g : Fin n := ⟨s.start + j.val, by
        have hjlt := j.isLt
        have hstop := s.stop_lt
        have hstart := s.start_le_pivot.trans s.pivot_lt_stop.le
        omega⟩
      have hgstart : s.start ≤ g.val := by
        simp only [g]
        omega
      have hgstop : g.val < s.stop := by
        have hjlt := j.isLt
        have hstart := s.start_le_pivot.trans s.pivot_lt_stop.le
        simp only [g]
        omega
      have hgpivot : s.pivotFin ≤ g := by
        change s.pivot ≤ s.start + j.val
        change s.pivot - s.start ≤ j.val at hjge
        have hstartPivot := s.start_le_pivot
        omega
      have hlocal : s.localAdjacent g hgstart hgstop = j := by
        apply Fin.ext
        simp only [AlphaLocalizationIndex.localAdjacent_val, g]
        omega
      have hcand := b.segment_rightDefectCandidate_local
        s w g hgstart hgstop hgpivot
      rw [hlocal] at hcand
      refine Or.inr (Or.inr (Finset.mem_image.mpr ⟨g, ?_, ?_⟩))
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ g, hgpivot, hgstop⟩
      · exact hcand.symm.trans hx
  · rintro (hx | hx | hx)
    · exact Or.inl (hx.trans (b.segment_halfGapCandidate_local s w).symm)
    · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
      have hjdata := (Finset.mem_filter.mp hj).2
      have hjstart : s.start ≤ j.val := hjdata.1
      have hjpivot : j ≤ s.pivotFin := hjdata.2
      have hjstop : j.val < s.stop := by
        change j.val ≤ s.pivot at hjpivot
        have hpivotStop := s.pivot_lt_stop
        omega
      let localIndex := s.localAdjacent j hjstart hjstop
      have hlocalPivot : localIndex ≤ s.localPivot := by
        change j.val - s.start ≤ s.pivot - s.start
        change j.val ≤ s.pivot at hjpivot
        omega
      have hcand := b.segment_leftDefectCandidate_local
        s w j hjstart hjstop hjpivot
      refine Or.inr (Or.inl (Finset.mem_image.mpr ⟨localIndex, ?_, ?_⟩))
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ localIndex, hlocalPivot⟩
      · exact hcand.trans hx
    · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
      have hjdata := (Finset.mem_filter.mp hj).2
      have hjpivot : s.pivotFin ≤ j := hjdata.1
      have hjstop : j.val < s.stop := hjdata.2
      have hjstart : s.start ≤ j.val := by
        change s.pivot ≤ j.val at hjpivot
        exact s.start_le_pivot.trans hjpivot
      let localIndex := s.localAdjacent j hjstart hjstop
      have hlocalPivot : s.localPivot ≤ localIndex := by
        change s.pivot - s.start ≤ j.val - s.start
        change s.pivot ≤ j.val at hjpivot
        omega
      have hcand := b.segment_rightDefectCandidate_local
        s w j hjstart hjstop hjpivot
      refine Or.inr (Or.inr (Finset.mem_image.mpr ⟨localIndex, ?_, ?_⟩))
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ localIndex, hlocalPivot⟩
      · exact hcand.trans hx

/-- Every localization-block candidate is an ambient alpha candidate. -/
theorem localizationBlockCandidates_subset_alphaCandidates
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n) :
    b.localizationBlockCandidates s ⊆ b.alphaCandidates s.pivotFin := by
  classical
  intro x hx
  simp only [localizationBlockCandidates, Finset.mem_insert,
    Finset.mem_union] at hx
  rcases hx with hx | hx | hx
  · rw [hx]
    exact b.halfGapCandidate_mem_alphaCandidates s.pivotFin
  · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
    have hjpivot := (Finset.mem_filter.mp hj).2.2
    rw [← hx]
    exact b.leftDefectCandidate_mem_alphaCandidates hjpivot
  · rcases Finset.mem_image.mp hx with ⟨j, hj, hx⟩
    have hjpivot := (Finset.mem_filter.mp hj).2.1
    rw [← hx]
    exact b.rightDefectCandidate_mem_alphaCandidates hjpivot

/-- Replacing a nonempty subset by its minimum preserves the minimum of the
ambient nonempty finite set. -/
theorem min_insert_subsetMin_sdiff_eq_min
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (a t : Finset α) (ha : a.Nonempty) (ht : t.Nonempty)
    (hta : t ⊆ a) :
    (insert (t.min' ht) (a \ t)).min'
        ⟨t.min' ht, Finset.mem_insert_self _ _⟩ =
      a.min' ha := by
  apply min_insert_sdiff_eq_min' a t ha (t.min' ht)
  · exact Finset.min'_le a (t.min' ht)
      (hta (Finset.min'_mem t ht))
  · intro y hy
    exact Finset.min'_le t y hy

/-- Beli (2009/2010), Lemma 2.1, proved from the concrete finite definition
of `alpha`. -/
theorem beli2009Lemma21_proved
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha s.pivotFin =
      (b.localizedReplacementCandidates s w).min'
        (b.localizedReplacementCandidates_nonempty s w) := by
  let segmentBONG := w.toGoodBONG b.good
  have hcandidates : segmentBONG.alphaCandidates s.localPivot =
      b.localizationBlockCandidates s :=
    b.segment_alphaCandidates_eq_localizationBlock s w
  have hblock : (b.localizationBlockCandidates s).Nonempty := by
    rw [← hcandidates]
    exact segmentBONG.alphaCandidates_nonempty s.localPivot
  have hlocalAlpha : segmentBONG.alpha s.localPivot =
      (b.localizationBlockCandidates s).min' hblock := by
    unfold alpha
    apply le_antisymm
    · apply Finset.le_min'
      intro x hx
      apply Finset.min'_le
      rw [hcandidates]
      exact hx
    · apply Finset.le_min'
      intro x hx
      apply Finset.min'_le
      rw [← hcandidates]
      exact hx
  have hglobalLeLocal :
      (b.alphaCandidates s.pivotFin).min'
          (b.alphaCandidates_nonempty s.pivotFin) ≤
        segmentBONG.alpha s.localPivot := by
    rw [hlocalAlpha]
    exact Finset.min'_le _ _
      (b.localizationBlockCandidates_subset_alphaCandidates s
        (Finset.min'_mem _ hblock))
  have hlocalLeBlock : ∀ y ∈ b.localizationBlockCandidates s,
      segmentBONG.alpha s.localPivot ≤ y := by
    intro y hy
    rw [hlocalAlpha]
    exact Finset.min'_le _ _ hy
  have hreplace := min_insert_sdiff_eq_min'
    (b.alphaCandidates s.pivotFin) (b.localizationBlockCandidates s)
    (b.alphaCandidates_nonempty s.pivotFin)
    (segmentBONG.alpha s.localPivot) hglobalLeLocal hlocalLeBlock
  unfold alpha localizedReplacementCandidates
  exact hreplace.symm

end BONG.GoodBONG

/-- The finite-minimum law used by the 2009 development is derivable and
therefore no longer belongs to the trust boundary. -/
noncomputable instance beli2009AlphaLocalizationLaws_proved :
    Beli2009AlphaLocalizationLaws.{u, v} K where
  localization := fun b s w ↦
    BONG.GoodBONG.beli2009Lemma21_proved b s w

end Bong
