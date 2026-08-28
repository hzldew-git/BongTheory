/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaMonotonicity
import Bong.Bong.Beli2006ReverseDualAlpha
import Bong.Bong.Prefix

/-!
# Beli (2009/2010), Lemma 2.4 and Corollary 2.5

This file formalizes compression of consecutive families of candidates in
the finite minimum defining `alpha`, derives both recursive formulas, and
records the duality and scaling statements of Remark 2.6.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

namespace AlphaLocalizationIndex

/-- A global adjacent index inside a localization block, expressed in local
coordinates. -/
def localAdjacent (s : AlphaLocalizationIndex n) (j : Fin n)
    (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    Fin (s.stop - s.start) :=
  ⟨j.1 - s.start, by omega⟩

@[simp]
theorem localAdjacent_val (s : AlphaLocalizationIndex n) (j : Fin n)
    (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (s.localAdjacent j hstart hstop).1 = j.1 - s.start :=
  rfl

end AlphaLocalizationIndex

namespace BONG.GoodBONG

/-- Replacing dominated members of a nonempty finite set by one lower member
does not change its minimum, provided the old minimum is below the new
member. -/
theorem min_insert_sdiff_eq_min'
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (s t : Finset α) (hs : s.Nonempty) (x : α)
    (hmin : s.min' hs ≤ x) (hdom : ∀ y ∈ t, x ≤ y) :
    (insert x (s \ t)).min' ⟨x, Finset.mem_insert_self _ _⟩ =
      s.min' hs := by
  apply le_antisymm
  · by_cases hm : s.min' hs ∈ t
    · exact (Finset.min'_le _ x (Finset.mem_insert_self _ _)).trans
        (hdom _ hm)
    · apply Finset.min'_le
      simp only [Finset.mem_insert, Finset.mem_sdiff]
      exact Or.inr ⟨Finset.min'_mem _ _, hm⟩
  · apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_sdiff] at hy
    rcases hy with rfl | ⟨hys, _⟩
    · exact hmin
    · exact Finset.min'_le _ _ hys

/-- Two nonempty finite sets have the same minimum when the first minimum is
below every member of the second and each member of the first dominates a
member of the second. -/
theorem min'_eq_min'_of_cover
    {α : Type*} [LinearOrder α]
    (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : ∀ y ∈ t, s.min' hs ≤ y)
    (hts : ∀ y ∈ s, ∃ x ∈ t, x ≤ y) :
    s.min' hs = t.min' ht := by
  apply le_antisymm
  · exact Finset.le_min' _ _ _ hst
  · obtain ⟨x, hxt, hxy⟩ := hts (s.min' hs) (Finset.min'_mem _ _)
    exact (Finset.min'_le _ _ hxt).trans hxy

/-- The left-hand family of candidates indexed by `start ≤ j ≤ pivot`. -/
noncomputable def leftCompressionBlock
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n) : Finset (WithTop ℚ) :=
  (Finset.univ.filter fun j : Fin n =>
      s.start ≤ j.1 ∧ j ≤ s.pivotFin).image
    (b.leftDefectCandidate i)

/-- The right-hand family of candidates indexed by `pivot ≤ j < stop`. -/
noncomputable def rightCompressionBlock
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n) : Finset (WithTop ℚ) :=
  (Finset.univ.filter fun j : Fin n =>
      s.pivotFin ≤ j ∧ j.1 < s.stop).image
    (b.rightDefectCandidate i)

/-- The value replacing a left family in Lemma 2.4(i). -/
noncomputable def leftCompressionValue
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) : ℚ :=
  ((b.order i.succ - b.order s.pivotFin.succ : Int) : ℚ) +
    (w.toGoodBONG b.good).alphaValue s.localPivot

/-- The value replacing a right family in Lemma 2.4(ii). -/
noncomputable def rightCompressionValue
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) : ℚ :=
  ((b.order s.pivotFin.castSucc - b.order i.castSucc : Int) : ℚ) +
    (w.toGoodBONG b.good).alphaValue s.localPivot

/-- Candidate set after the replacement in Lemma 2.4(i). -/
noncomputable def leftCompressedCandidates
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    Finset (WithTop ℚ) :=
  insert (b.leftCompressionValue s i w : WithTop ℚ)
    (b.alphaCandidates i \ b.leftCompressionBlock s i)

/-- Candidate set after the replacement in Lemma 2.4(ii). -/
noncomputable def rightCompressedCandidates
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    Finset (WithTop ℚ) :=
  insert (b.rightCompressionValue s i w : WithTop ℚ)
    (b.alphaCandidates i \ b.rightCompressionBlock s i)

/-- The common order gap occurring in all four terms of Corollary 2.5. -/
noncomputable def alphaGapValue
    (b : GoodBONG q L (n + 1)) (i : Fin n) : ℚ :=
  ((b.order i.succ - b.order i.castSucc : Int) : ℚ)

/-- The term `R_(i+1) - R_i + alpha_j` for an adjacent alpha index `j`. -/
noncomputable def neighborAlphaCandidate
    (b : GoodBONG q L (n + 1)) (i j : Fin n) : WithTop ℚ :=
  (b.alphaGapValue i + b.alphaValue j : ℚ)

/-- The valid predecessor and successor terms in Corollary 2.5.  At either
endpoint the nonexistent term is absent from this finite set. -/
noncomputable def neighborAlphaCandidates
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Finset (WithTop ℚ) :=
  (Finset.univ.filter fun j : Fin n =>
      j.1 + 1 = i.1 ∨ i.1 + 1 = j.1).image
    (b.neighborAlphaCandidate i)

/-- The boundary-aware four-term set in Corollary 2.5(i). -/
noncomputable def recursiveAlphaCandidates
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate i)
    (insert (b.leftDefectCandidate i i) (b.neighborAlphaCandidates i))

/-- Localization data for the prefix ending immediately before `alpha_i`.
It exists precisely when `alpha_i` has a predecessor. -/
def prefixAlphaLocalizationIndex
    (i : Fin (n + 1)) (hi : 0 < i.1) : AlphaLocalizationIndex (n + 1) where
  start := 0
  pivot := i.1 - 1
  stop := i.1
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- Localization data for the suffix beginning immediately after `alpha_i`.
It exists precisely when `alpha_i` has a successor. -/
def suffixAlphaLocalizationIndex
    (i : Fin (n + 1)) (hi : i.1 + 1 < n + 1) :
    AlphaLocalizationIndex (n + 1) where
  start := i.1 + 1
  pivot := i.1 + 1
  stop := n + 1
  start_le_pivot := le_rfl
  pivot_lt_stop := hi
  stop_lt := by omega

/-- Canonical prefix realization used in Corollary 2.5(ii). -/
noncomputable def prefixAlphaSegmentWitness
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) (hi : 0 < i.1) :
    BONG.SegmentWitness b.toBONG
      (prefixAlphaLocalizationIndex i hi).start
      (prefixAlphaLocalizationIndex i hi).length
      (prefixAlphaLocalizationIndex i hi).bound :=
  b.toBONG.segmentWitness _ _ _

/-- Canonical suffix realization used in Corollary 2.5(ii). -/
noncomputable def suffixAlphaSegmentWitness
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) :
    BONG.SegmentWitness b.toBONG
      (suffixAlphaLocalizationIndex i hi).start
      (suffixAlphaLocalizationIndex i hi).length
      (suffixAlphaLocalizationIndex i hi).bound :=
  b.toBONG.segmentWitness _ _ _

/-- The prefix-segment term in Corollary 2.5(ii). -/
noncomputable def prefixSegmentAlphaCandidate
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : 0 < i.1) : WithTop ℚ :=
  b.leftCompressionValue (prefixAlphaLocalizationIndex i hi) i
    (b.prefixAlphaSegmentWitness i hi)

/-- The suffix-segment term in Corollary 2.5(ii). -/
noncomputable def suffixSegmentAlphaCandidate
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) : WithTop ℚ :=
  b.rightCompressionValue (suffixAlphaLocalizationIndex i hi) i
    (b.suffixAlphaSegmentWitness i hi)

/-- The optional prefix term; it is empty at the left endpoint. -/
noncomputable def prefixSegmentAlphaCandidates
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    Finset (WithTop ℚ) :=
  if hi : 0 < i.1 then {b.prefixSegmentAlphaCandidate i hi} else ∅

/-- The optional suffix term; it is empty at the right endpoint. -/
noncomputable def suffixSegmentAlphaCandidates
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    Finset (WithTop ℚ) :=
  if hi : i.1 + 1 < n + 1 then
    {b.suffixSegmentAlphaCandidate i hi}
  else ∅

/-- The boundary-aware segment-recursive set in Corollary 2.5(ii). -/
noncomputable def segmentRecursiveAlphaCandidates
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate i)
    (insert (b.leftDefectCandidate i i)
      (b.prefixSegmentAlphaCandidates i ∪
        b.suffixSegmentAlphaCandidates i))

theorem recursiveAlphaCandidates_nonempty
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.recursiveAlphaCandidates i).Nonempty :=
  ⟨b.halfGapCandidate i, Finset.mem_insert_self _ _⟩

theorem segmentRecursiveAlphaCandidates_nonempty
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    (b.segmentRecursiveAlphaCandidates i).Nonempty :=
  ⟨b.halfGapCandidate i, Finset.mem_insert_self _ _⟩

theorem leftCompressedCandidates_nonempty
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (b.leftCompressedCandidates s i w).Nonempty :=
  ⟨(b.leftCompressionValue s i w : WithTop ℚ),
    Finset.mem_insert_self _ _⟩

theorem rightCompressedCandidates_nonempty
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i : Fin n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (b.rightCompressedCandidates s i w).Nonempty :=
  ⟨(b.rightCompressionValue s i w : WithTop ℚ),
    Finset.mem_insert_self _ _⟩

@[simp]
theorem segment_valueUnit_local_castSucc
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (w.toGoodBONG b.good).valueUnit
        (s.localAdjacent j hstart hstop).castSucc =
      b.valueUnit j.castSucc := by
  change w.bong.valueUnit _ = b.toBONG.valueUnit _
  rw [w.valueUnit_eq]
  congr 1
  apply Fin.ext
  change s.start + (j.1 - s.start) = j.1
  omega

@[simp]
theorem segment_valueUnit_local_succ
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (w.toGoodBONG b.good).valueUnit
        (s.localAdjacent j hstart hstop).succ =
      b.valueUnit j.succ := by
  change w.bong.valueUnit _ = b.toBONG.valueUnit _
  rw [w.valueUnit_eq]
  congr 1
  apply Fin.ext
  change s.start + (j.1 - s.start + 1) = j.1 + 1
  omega

@[simp]
theorem segment_adjacentDefect_local
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (w.toGoodBONG b.good).adjacentDefect
        (s.localAdjacent j hstart hstop) =
      b.adjacentDefect j := by
  unfold adjacentDefect adjacentProduct
  change defectOrder
      (-(w.bong.valueUnit _ * w.bong.valueUnit _)) =
    defectOrder (-(b.toBONG.valueUnit _ * b.toBONG.valueUnit _))
  rw [w.valueUnit_eq, w.valueUnit_eq]
  congr 4
  · apply Fin.ext
    change s.start + (j.1 - s.start) = j.1
    omega
  · apply Fin.ext
    change s.start + (j.1 - s.start + 1) = j.1 + 1
    omega

@[simp]
theorem segment_order_local_castSucc
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (w.toGoodBONG b.good).order
        (s.localAdjacent j hstart hstop).castSucc =
      b.order j.castSucc := by
  change w.bong.order _ = b.toBONG.order _
  rw [w.order_eq]
  congr 1
  apply Fin.ext
  change s.start + (j.1 - s.start) = j.1
  omega

@[simp]
theorem segment_order_local_succ
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop) :
    (w.toGoodBONG b.good).order
        (s.localAdjacent j hstart hstop).succ =
      b.order j.succ := by
  change w.bong.order _ = b.toBONG.order _
  rw [w.order_eq]
  congr 1
  apply Fin.ext
  change s.start + (j.1 - s.start + 1) = j.1 + 1
  omega

theorem localAdjacent_pivot
    (s : AlphaLocalizationIndex n) :
    s.localAdjacent s.pivotFin s.start_le_pivot s.pivot_lt_stop =
      s.localPivot := by
  apply Fin.ext
  rfl

theorem segment_leftDefectCandidate_local
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop)
    (hjpivot : j ≤ s.pivotFin) :
    (w.toGoodBONG b.good).leftDefectCandidate s.localPivot
        (s.localAdjacent j hstart hstop) =
      b.leftDefectCandidate s.pivotFin j := by
  have hp := localAdjacent_pivot (n := n) s
  have h₁ := b.segment_order_local_succ s w s.pivotFin
    s.start_le_pivot s.pivot_lt_stop
  have h₂ := b.segment_order_local_castSucc s w j hstart hstop
  have h₃ := b.segment_adjacentDefect_local s w j hstart hstop
  rw [← hp]
  unfold leftDefectCandidate
  rw [h₁, h₂, h₃]

theorem segment_rightDefectCandidate_local
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (j : Fin n) (hstart : s.start ≤ j.1) (hstop : j.1 < s.stop)
    (hpivotj : s.pivotFin ≤ j) :
    (w.toGoodBONG b.good).rightDefectCandidate s.localPivot
        (s.localAdjacent j hstart hstop) =
      b.rightDefectCandidate s.pivotFin j := by
  have hp := localAdjacent_pivot (n := n) s
  have h₁ := b.segment_order_local_succ s w j hstart hstop
  have h₂ := b.segment_order_local_castSucc s w s.pivotFin
    s.start_le_pivot s.pivot_lt_stop
  have h₃ := b.segment_adjacentDefect_local s w j hstart hstop
  rw [← hp]
  unfold rightDefectCandidate
  rw [h₁, h₂, h₃]

theorem left_shift_candidate
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i j : Fin n) :
    (((b.order i.succ - b.order s.pivotFin.succ : Int) : ℚ) :
        WithTop ℚ) + b.leftDefectCandidate s.pivotFin j =
      b.leftDefectCandidate i j := by
  unfold leftDefectCandidate
  rw [← add_assoc]
  congr 1
  norm_cast
  push_cast
  ring

theorem right_shift_candidate
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i j : Fin n) :
    (((b.order s.pivotFin.castSucc - b.order i.castSucc : Int) : ℚ) :
        WithTop ℚ) + b.rightDefectCandidate s.pivotFin j =
      b.rightDefectCandidate i j := by
  unfold rightDefectCandidate
  rw [← add_assoc]
  congr 1
  norm_cast
  push_cast
  ring

/-- Moving the left endpoint of a left-defect candidate only adds the
corresponding order difference. -/
theorem left_shift_candidate_at
    (b : GoodBONG q L (n + 1)) (i p j : Fin n) :
    (((b.order i.succ - b.order p.succ : Int) : ℚ) : WithTop ℚ) +
        b.leftDefectCandidate p j =
      b.leftDefectCandidate i j := by
  unfold leftDefectCandidate
  rw [← add_assoc]
  congr 1
  norm_cast
  push_cast
  ring

/-- Moving the right endpoint of a right-defect candidate only adds the
corresponding order difference. -/
theorem right_shift_candidate_at
    (b : GoodBONG q L (n + 1)) (i p j : Fin n) :
    (((b.order p.castSucc - b.order i.castSucc : Int) : ℚ) :
        WithTop ℚ) + b.rightDefectCandidate p j =
      b.rightDefectCandidate i j := by
  unfold rightDefectCandidate
  rw [← add_assoc]
  congr 1
  norm_cast
  push_cast
  ring

theorem leftCompressionValue_le_candidate
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i j : Fin n) (hpivoti : s.pivotFin ≤ i)
    (hstart : s.start ≤ j.1) (hjpivot : j ≤ s.pivotFin)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (b.leftCompressionValue s i w : WithTop ℚ) ≤
      b.leftDefectCandidate i j := by
  have hstop : j.1 < s.stop := by
    change j.1 < s.stop
    change j.1 ≤ s.pivot at hjpivot
    exact hjpivot.trans_lt s.pivot_lt_stop
  have hlocal : s.localAdjacent j hstart hstop ≤ s.localPivot := by
    change j.1 - s.start ≤ s.pivot - s.start
    change j.1 ≤ s.pivot at hjpivot
    omega
  have hα := (w.toGoodBONG b.good).alpha_le_leftDefectCandidate hlocal
  rw [← (w.toGoodBONG b.good).coe_alphaValue] at hα
  have hseg := b.segment_leftDefectCandidate_local s w j hstart hstop
    hjpivot
  have hadd := add_le_add_left hα
    ((((b.order i.succ - b.order s.pivotFin.succ : Int) : ℚ) :
      WithTop ℚ))
  rw [hseg] at hadd
  have hadd' :
      (((b.order i.succ - b.order s.pivotFin.succ : Int) : ℚ) :
          WithTop ℚ) +
          ((w.toGoodBONG b.good).alphaValue s.localPivot : WithTop ℚ) ≤
        (((b.order i.succ - b.order s.pivotFin.succ : Int) : ℚ) :
          WithTop ℚ) + b.leftDefectCandidate s.pivotFin j := by
    simpa only [add_comm] using hadd
  rw [b.left_shift_candidate s i j] at hadd'
  simpa only [leftCompressionValue, WithTop.coe_add] using hadd'

theorem rightCompressionValue_le_candidate
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (i j : Fin n) (hipivot : i ≤ s.pivotFin)
    (hpivotj : s.pivotFin ≤ j) (hstop : j.1 < s.stop)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (b.rightCompressionValue s i w : WithTop ℚ) ≤
      b.rightDefectCandidate i j := by
  have hstart : s.start ≤ j.1 := by
    change s.start ≤ j.1
    change s.pivot ≤ j.1 at hpivotj
    exact s.start_le_pivot.trans hpivotj
  have hlocal : s.localPivot ≤ s.localAdjacent j hstart hstop := by
    change s.pivot - s.start ≤ j.1 - s.start
    change s.pivot ≤ j.1 at hpivotj
    omega
  have hα := (w.toGoodBONG b.good).alpha_le_rightDefectCandidate hlocal
  rw [← (w.toGoodBONG b.good).coe_alphaValue] at hα
  have hseg := b.segment_rightDefectCandidate_local s w j hstart hstop
    hpivotj
  have hadd := add_le_add_left hα
    ((((b.order s.pivotFin.castSucc - b.order i.castSucc : Int) : ℚ) :
      WithTop ℚ))
  rw [hseg] at hadd
  have hadd' :
      (((b.order s.pivotFin.castSucc - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) +
          ((w.toGoodBONG b.good).alphaValue s.localPivot : WithTop ℚ) ≤
        (((b.order s.pivotFin.castSucc - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) + b.rightDefectCandidate s.pivotFin j := by
    simpa only [add_comm] using hadd
  rw [b.right_shift_candidate s i j] at hadd'
  simpa only [rightCompressionValue, WithTop.coe_add] using hadd'

/-- Two coefficient sequences differ by a common scalar.  The quadratic
spaces and lattices may be different; only the indexed BONG values enter. -/
def IsCoefficientScale
    (a : GoodBONG q L n) (b : GoodBONG r M n) (s : Kˣ) : Prop :=
  ∀ i, b.valueUnit i = s * a.valueUnit i

namespace IsCoefficientScale

theorem order
    {a : GoodBONG q L n} {b : GoodBONG r M n} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.order i = ordUnit K s + a.order i := by
  have hi := h i
  change b.toBONG.valueUnit i = s * a.toBONG.valueUnit i at hi
  change b.toBONG.order i = ordUnit K s + a.toBONG.order i
  rw [b.toBONG.order_eq_ordUnit, hi, ordUnit_mul,
    ← a.toBONG.order_eq_ordUnit]

theorem order_sub
    {a : GoodBONG q L n} {b : GoodBONG r M n} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i j : Fin n) :
    b.order i - b.order j = a.order i - a.order j := by
  rw [h.order i, h.order j]
  ring

theorem adjacentProduct
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (j : Fin n) :
    b.adjacentProduct j = a.adjacentProduct j * s ^ 2 := by
  unfold BONG.GoodBONG.adjacentProduct
  rw [h j.castSucc, h j.succ]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- Multiplication by a square leaves the embedded defect order unchanged. -/
theorem defectOrder_mul_square (x s : Kˣ) :
    BONG.GoodBONG.defectOrder (K := K) (x * s ^ 2) =
      BONG.GoodBONG.defectOrder (K := K) x := by
  unfold BONG.GoodBONG.defectOrder
  rw [quadraticDefect_mul_square]

theorem adjacentDefect
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (j : Fin n) :
    b.adjacentDefect j = a.adjacentDefect j := by
  unfold BONG.GoodBONG.adjacentDefect
  rw [h.adjacentProduct j, defectOrder_mul_square]

theorem halfGapCandidate
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.halfGapCandidate i = a.halfGapCandidate i := by
  unfold BONG.GoodBONG.halfGapCandidate
  rw [h.order_sub i.succ i.castSucc]

theorem leftDefectCandidate
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i j : Fin n) :
    b.leftDefectCandidate i j = a.leftDefectCandidate i j := by
  unfold BONG.GoodBONG.leftDefectCandidate
  rw [h.order_sub i.succ j.castSucc, h.adjacentDefect j]

theorem rightDefectCandidate
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i j : Fin n) :
    b.rightDefectCandidate i j = a.rightDefectCandidate i j := by
  unfold BONG.GoodBONG.rightDefectCandidate
  rw [h.order_sub j.succ i.castSucc, h.adjacentDefect j]

theorem alphaCandidates
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.alphaCandidates i = a.alphaCandidates i := by
  have hleft : b.leftDefectCandidate i = a.leftDefectCandidate i := by
    funext j
    exact h.leftDefectCandidate i j
  have hright : b.rightDefectCandidate i = a.rightDefectCandidate i := by
    funext j
    exact h.rightDefectCandidate i j
  unfold BONG.GoodBONG.alphaCandidates
  rw [h.halfGapCandidate i, hleft, hright]

theorem alpha
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.alpha i = a.alpha i := by
  unfold BONG.GoodBONG.alpha
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    rw [h.alphaCandidates i]
    exact hx
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    rw [← h.alphaCandidates i]
    exact hx

theorem alphaValue
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)} {s : Kˣ}
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.alphaValue i = a.alphaValue i := by
  have halpha := h.alpha i
  rw [← b.coe_alphaValue, ← a.coe_alphaValue] at halpha
  exact_mod_cast halpha

end IsCoefficientScale

/-- Beli (2009/2010), Remark 2.6 (scaling): multiplying every coefficient
by the same nonzero scalar leaves every `alpha` invariant. -/
theorem beli2009Remark26_scaling
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) (s : Kˣ)
    (h : a.IsCoefficientScale b s) (i : Fin n) :
    b.alphaValue i = a.alphaValue i :=
  h.alphaValue i

variable [Beli2009AlphaLocalizationLaws.{u, v} K]

theorem alpha_le_leftCompressionValue
    (b : GoodBONG q L (n + 2)) (s : AlphaLocalizationIndex (n + 1))
    (i : Fin (n + 1)) (hpivoti : s.pivotFin ≤ i)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i ≤ (b.leftCompressionValue s i w : WithTop ℚ) := by
  have hmono := b.alphaRightEndpoint_antitone hpivoti
  unfold alphaRightEndpoint at hmono
  push_cast at hmono
  have hloc := b.beli2009Lemma21_le_segmentAlpha s w
  rw [← b.coe_alphaValue,
    ← (w.toGoodBONG b.good).coe_alphaValue] at hloc
  have hlocQ :
      b.alphaValue s.pivotFin ≤
        (w.toGoodBONG b.good).alphaValue s.localPivot := by
    exact_mod_cast hloc
  have hresult :
      b.alphaValue i ≤ b.leftCompressionValue s i w := by
    unfold leftCompressionValue
    push_cast
    linarith
  rw [← b.coe_alphaValue]
  exact_mod_cast hresult

theorem alpha_le_rightCompressionValue
    (b : GoodBONG q L (n + 2)) (s : AlphaLocalizationIndex (n + 1))
    (i : Fin (n + 1)) (hipivot : i ≤ s.pivotFin)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i ≤ (b.rightCompressionValue s i w : WithTop ℚ) := by
  have hmono := b.alphaLeftEndpoint_monotone hipivot
  unfold alphaLeftEndpoint at hmono
  push_cast at hmono
  have hloc := b.beli2009Lemma21_le_segmentAlpha s w
  rw [← b.coe_alphaValue,
    ← (w.toGoodBONG b.good).coe_alphaValue] at hloc
  have hlocQ :
      b.alphaValue s.pivotFin ≤
        (w.toGoodBONG b.good).alphaValue s.localPivot := by
    exact_mod_cast hloc
  have hresult :
      b.alphaValue i ≤ b.rightCompressionValue s i w := by
    unfold rightCompressionValue
    push_cast
    linarith
  rw [← b.coe_alphaValue]
  exact_mod_cast hresult

omit [Beli2009AlphaLocalizationLaws K] in
theorem alpha_le_neighborAlphaCandidate
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hadjacent : j.1 + 1 = i.1 ∨ i.1 + 1 = j.1) :
    b.alpha i ≤ b.neighborAlphaCandidate i j := by
  rw [← b.coe_alphaValue]
  rcases hadjacent with hprev | hnext
  · have hji : j ≤ i := by
      change j.1 ≤ i.1
      omega
    have hmono := b.alphaRightEndpoint_antitone hji
    have hindex : j.succ = i.castSucc := by
      apply Fin.ext
      exact hprev
    unfold alphaRightEndpoint at hmono
    rw [hindex] at hmono
    have hresult :
        b.alphaValue i ≤ b.alphaGapValue i + b.alphaValue j := by
      unfold alphaGapValue
      push_cast
      linarith
    unfold neighborAlphaCandidate
    exact_mod_cast hresult
  · have hij : i ≤ j := by
      change i.1 ≤ j.1
      omega
    have hmono := b.alphaLeftEndpoint_monotone hij
    have hindex : i.succ = j.castSucc := by
      apply Fin.ext
      exact hnext
    unfold alphaLeftEndpoint at hmono
    rw [← hindex] at hmono
    have hresult :
        b.alphaValue i ≤ b.alphaGapValue i + b.alphaValue j := by
      unfold alphaGapValue
      push_cast
      linarith
    unfold neighborAlphaCandidate
    exact_mod_cast hresult

omit [Beli2009AlphaLocalizationLaws K] in
theorem predecessorNeighbor_le_leftDefectCandidate
    (b : GoodBONG q L (n + 2)) (i p j : Fin (n + 1))
    (hp : p.1 + 1 = i.1) (hjp : j ≤ p) :
    b.neighborAlphaCandidate i p ≤ b.leftDefectCandidate i j := by
  have hindex : p.succ = i.castSucc := by
    apply Fin.ext
    exact hp
  have hα := b.alpha_le_leftDefectCandidate (i := p) (j := j) hjp
  rw [← b.coe_alphaValue] at hα
  calc
    b.neighborAlphaCandidate i p =
        (((b.order i.succ - b.order p.succ : Int) : ℚ) : WithTop ℚ) +
          (b.alphaValue p : WithTop ℚ) := by
      unfold neighborAlphaCandidate alphaGapValue
      rw [← hindex]
      simp only [WithTop.coe_add]
    _ ≤ (((b.order i.succ - b.order p.succ : Int) : ℚ) :
          WithTop ℚ) + b.leftDefectCandidate p j :=
      by
        simpa only [add_comm] using
          (add_le_add_left hα
            ((((b.order i.succ - b.order p.succ : Int) : ℚ) :
              WithTop ℚ)))
    _ = b.leftDefectCandidate i j :=
      b.left_shift_candidate_at i p j

omit [Beli2009AlphaLocalizationLaws K] in
theorem successorNeighbor_le_rightDefectCandidate
    (b : GoodBONG q L (n + 2)) (i s j : Fin (n + 1))
    (hs : i.1 + 1 = s.1) (hsj : s ≤ j) :
    b.neighborAlphaCandidate i s ≤ b.rightDefectCandidate i j := by
  have hindex : i.succ = s.castSucc := by
    apply Fin.ext
    exact hs
  have hα := b.alpha_le_rightDefectCandidate (i := s) (j := j) hsj
  rw [← b.coe_alphaValue] at hα
  calc
    b.neighborAlphaCandidate i s =
        (((b.order s.castSucc - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) + (b.alphaValue s : WithTop ℚ) := by
      unfold neighborAlphaCandidate alphaGapValue
      rw [hindex]
      simp only [WithTop.coe_add]
    _ ≤ (((b.order s.castSucc - b.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) + b.rightDefectCandidate s j :=
      by
        simpa only [add_comm] using
          (add_le_add_left hα
            ((((b.order s.castSucc - b.order i.castSucc : Int) : ℚ) :
              WithTop ℚ)))
    _ = b.rightDefectCandidate i j :=
      b.right_shift_candidate_at i s j

theorem prefixSegmentAlphaCandidate_mem
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) (hi : 0 < i.1) :
    b.prefixSegmentAlphaCandidate i hi ∈
      b.prefixSegmentAlphaCandidates i := by
  classical
  simp [prefixSegmentAlphaCandidates, hi]

theorem suffixSegmentAlphaCandidate_mem
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) :
    b.suffixSegmentAlphaCandidate i hi ∈
      b.suffixSegmentAlphaCandidates i := by
  classical
  simp [suffixSegmentAlphaCandidates, hi]

theorem alpha_le_prefixSegmentAlphaCandidate
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) (hi : 0 < i.1) :
    b.alpha i ≤ b.prefixSegmentAlphaCandidate i hi := by
  have hpivot : (prefixAlphaLocalizationIndex i hi).pivotFin ≤ i := by
    change i.1 - 1 ≤ i.1
    omega
  exact b.alpha_le_leftCompressionValue
    (prefixAlphaLocalizationIndex i hi) i hpivot
    (b.prefixAlphaSegmentWitness i hi)

theorem alpha_le_suffixSegmentAlphaCandidate
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) :
    b.alpha i ≤ b.suffixSegmentAlphaCandidate i hi := by
  have hpivot : i ≤ (suffixAlphaLocalizationIndex i hi).pivotFin := by
    change i.1 ≤ i.1 + 1
    omega
  exact b.alpha_le_rightCompressionValue
    (suffixAlphaLocalizationIndex i hi) i hpivot
    (b.suffixAlphaSegmentWitness i hi)

theorem prefixSegmentAlphaCandidate_le_leftDefectCandidate
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hji : j < i) :
    b.prefixSegmentAlphaCandidate i (by omega) ≤
      b.leftDefectCandidate i j := by
  have hpivot : (prefixAlphaLocalizationIndex i (by omega)).pivotFin ≤ i := by
    change i.1 - 1 ≤ i.1
    omega
  have hstart : (prefixAlphaLocalizationIndex i (by omega)).start ≤ j.1 := by
    change 0 ≤ j.1
    omega
  have hjpivot :
      j ≤ (prefixAlphaLocalizationIndex i (by omega)).pivotFin := by
    change j.1 ≤ i.1 - 1
    omega
  exact b.leftCompressionValue_le_candidate
    (prefixAlphaLocalizationIndex i (by omega)) i j hpivot hstart hjpivot
    (b.prefixAlphaSegmentWitness i (by omega))

theorem suffixSegmentAlphaCandidate_le_rightDefectCandidate
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hij : i < j) :
    b.suffixSegmentAlphaCandidate i (by omega) ≤
      b.rightDefectCandidate i j := by
  have hpivot : i ≤ (suffixAlphaLocalizationIndex i (by omega)).pivotFin := by
    change i.1 ≤ i.1 + 1
    omega
  have hpivotj :
      (suffixAlphaLocalizationIndex i (by omega)).pivotFin ≤ j := by
    change i.1 + 1 ≤ j.1
    omega
  have hstop : j.1 < (suffixAlphaLocalizationIndex i (by omega)).stop := by
    change j.1 < n + 1
    exact j.isLt
  exact b.rightCompressionValue_le_candidate
    (suffixAlphaLocalizationIndex i (by omega)) i j hpivot hpivotj hstop
    (b.suffixAlphaSegmentWitness i (by omega))

/-- Beli (2009/2010), Lemma 2.4(i): exact left compression of the
candidate minimum. -/
theorem beli2009Lemma24_left
    (b : GoodBONG q L (n + 2)) (s : AlphaLocalizationIndex (n + 1))
    (i : Fin (n + 1)) (hpivoti : s.pivotFin ≤ i)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i =
      (b.leftCompressedCandidates s i w).min'
        (b.leftCompressedCandidates_nonempty s i w) := by
  have hmin := b.alpha_le_leftCompressionValue s i hpivoti w
  unfold alpha at hmin
  have hdom : ∀ y ∈ b.leftCompressionBlock s i,
      (b.leftCompressionValue s i w : WithTop ℚ) ≤ y := by
    intro y hy
    unfold leftCompressionBlock at hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    have hj' := (Finset.mem_filter.mp hj).2
    exact b.leftCompressionValue_le_candidate s i j hpivoti
      hj'.1 hj'.2 w
  have hreplace := min_insert_sdiff_eq_min'
    (b.alphaCandidates i) (b.leftCompressionBlock s i)
    (b.alphaCandidates_nonempty i)
    (b.leftCompressionValue s i w : WithTop ℚ) hmin hdom
  simpa only [alpha, leftCompressedCandidates] using hreplace.symm

/-- Beli (2009/2010), Lemma 2.4(ii): exact right compression of the
candidate minimum. -/
theorem beli2009Lemma24_right
    (b : GoodBONG q L (n + 2)) (s : AlphaLocalizationIndex (n + 1))
    (i : Fin (n + 1)) (hipivot : i ≤ s.pivotFin)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha i =
      (b.rightCompressedCandidates s i w).min'
        (b.rightCompressedCandidates_nonempty s i w) := by
  have hmin := b.alpha_le_rightCompressionValue s i hipivot w
  unfold alpha at hmin
  have hdom : ∀ y ∈ b.rightCompressionBlock s i,
      (b.rightCompressionValue s i w : WithTop ℚ) ≤ y := by
    intro y hy
    unfold rightCompressionBlock at hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    have hj' := (Finset.mem_filter.mp hj).2
    exact b.rightCompressionValue_le_candidate s i j hipivot
      hj'.1 hj'.2 w
  have hreplace := min_insert_sdiff_eq_min'
    (b.alphaCandidates i) (b.rightCompressionBlock s i)
    (b.alphaCandidates_nonempty i)
    (b.rightCompressionValue s i w : WithTop ℚ) hmin hdom
  simpa only [alpha, rightCompressedCandidates] using hreplace.symm

/- Beli (2009/2010), Corollary 2.5(i): `alpha_i` is the minimum of the
half-gap term, the local defect term, and the valid neighboring-alpha terms.
At the endpoints the nonexistent neighboring term is absent. -/
omit [Beli2009AlphaLocalizationLaws K] in
theorem beli2009Corollary25_i
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    b.alpha i =
      (b.recursiveAlphaCandidates i).min'
        (b.recursiveAlphaCandidates_nonempty i) := by
  unfold alpha
  apply min'_eq_min'_of_cover
  · intro y hy
    simp only [recursiveAlphaCandidates, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · simpa only [alpha] using b.alpha_le_halfGapCandidate i
    · simpa only [alpha] using
        b.alpha_le_leftDefectCandidate (i := i) (j := i) le_rfl
    · unfold neighborAlphaCandidates at hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hadjacent := (Finset.mem_filter.mp hj).2
      simpa only [alpha] using
        b.alpha_le_neighborAlphaCandidate i j hadjacent
  · intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · exact ⟨b.halfGapCandidate i, by simp [recursiveAlphaCandidates], le_rfl⟩
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ i := (Finset.mem_filter.mp hj).2
      by_cases h : j = i
      · subst j
        exact ⟨b.leftDefectCandidate i i,
          by simp [recursiveAlphaCandidates], le_rfl⟩
      · have hlt : j < i := lt_of_le_of_ne hji h
        let p : Fin (n + 1) := ⟨i.1 - 1, by omega⟩
        have hp : p.1 + 1 = i.1 := by
          dsimp [p]
          omega
        have hjp : j ≤ p := by
          change j.1 ≤ p.1
          dsimp [p]
          omega
        refine ⟨b.neighborAlphaCandidate i p, ?_,
          b.predecessorNeighbor_le_leftDefectCandidate i p j hp hjp⟩
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        unfold neighborAlphaCandidates
        apply Finset.mem_image.mpr
        refine ⟨p, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl hp
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : i ≤ j := (Finset.mem_filter.mp hj).2
      by_cases h : j = i
      · subst j
        exact ⟨b.leftDefectCandidate i i,
          by simp [recursiveAlphaCandidates], le_rfl⟩
      · have hlt : i < j := lt_of_le_of_ne hij (Ne.symm h)
        let s : Fin (n + 1) := ⟨i.1 + 1, by omega⟩
        have hs : i.1 + 1 = s.1 := by
          rfl
        have hsj : s ≤ j := by
          change s.1 ≤ j.1
          dsimp [s]
          omega
        refine ⟨b.neighborAlphaCandidate i s, ?_,
          b.successorNeighbor_le_rightDefectCandidate i s j hs hsj⟩
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        unfold neighborAlphaCandidates
        apply Finset.mem_image.mpr
        refine ⟨s, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr hs

/-- Beli (2009/2010), Corollary 2.5(ii): the neighboring-alpha terms may be
computed in the prefix and suffix BONGs.  The optional sets make the two
endpoint omissions part of the statement. -/
theorem beli2009Corollary25_ii
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    b.alpha i =
      (b.segmentRecursiveAlphaCandidates i).min'
        (b.segmentRecursiveAlphaCandidates_nonempty i) := by
  unfold alpha
  apply min'_eq_min'_of_cover
  · intro y hy
    simp only [segmentRecursiveAlphaCandidates, Finset.mem_insert,
      Finset.mem_union] at hy
    rcases hy with rfl | rfl | hy | hy
    · simpa only [alpha] using b.alpha_le_halfGapCandidate i
    · simpa only [alpha] using
        b.alpha_le_leftDefectCandidate (i := i) (j := i) le_rfl
    · unfold prefixSegmentAlphaCandidates at hy
      split at hy
      next hi =>
        have hy' := Finset.mem_singleton.mp hy
        subst y
        simpa only [alpha] using
          b.alpha_le_prefixSegmentAlphaCandidate i hi
      next => simp at hy
    · unfold suffixSegmentAlphaCandidates at hy
      split at hy
      next hi =>
        have hy' := Finset.mem_singleton.mp hy
        subst y
        simpa only [alpha] using
          b.alpha_le_suffixSegmentAlphaCandidate i hi
      next => simp at hy
  · intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · exact ⟨b.halfGapCandidate i,
        by simp [segmentRecursiveAlphaCandidates], le_rfl⟩
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ i := (Finset.mem_filter.mp hj).2
      by_cases h : j = i
      · subst j
        exact ⟨b.leftDefectCandidate i i,
          by simp [segmentRecursiveAlphaCandidates], le_rfl⟩
      · have hlt : j < i := lt_of_le_of_ne hji h
        refine ⟨b.prefixSegmentAlphaCandidate i (by omega), ?_,
          b.prefixSegmentAlphaCandidate_le_leftDefectCandidate i j hlt⟩
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        apply Finset.mem_union_left
        exact b.prefixSegmentAlphaCandidate_mem i (by omega)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : i ≤ j := (Finset.mem_filter.mp hj).2
      by_cases h : j = i
      · subst j
        exact ⟨b.leftDefectCandidate i i,
          by simp [segmentRecursiveAlphaCandidates], le_rfl⟩
      · have hlt : i < j := lt_of_le_of_ne hij (Ne.symm h)
        refine ⟨b.suffixSegmentAlphaCandidate i (by omega), ?_,
          b.suffixSegmentAlphaCandidate_le_rightDefectCandidate i j hlt⟩
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        apply Finset.mem_union_right
        exact b.suffixSegmentAlphaCandidate_mem i (by omega)

/-- Beli (2009/2010), Remark 2.6 (duality): a reverse-dual good BONG has
reversed inverse values, negated reversed orders, and reversed `alpha`s. -/
theorem beli2009Remark26_duality
    [BONGStructuralLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) (n + 1),
      (∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i) ∧
      (∀ i, c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)) ∧
      (∀ i, c.order i = -b.order (Fin.rev i)) ∧
      ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i) :=
  b.exists_reverseDual_with_alpha

end BONG.GoodBONG

end Bong
