/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715AlphaTypeII

/-!
# Beli (2019), Lemma 7.15: propagation of alpha equality

For an alpha index strictly after the boundary, all left-defect candidates
up to the boundary are compressed to one term using Beli (2009/2010), Lemma
2.4.  The compressed term is determined by the boundary alpha, while every
remaining term is determined by the exact common suffix.  This module makes
that argument independent of the type-I/type-II construction.
-/

namespace Bong

open Dyadic

universe u v

/-- The whole coefficient list, regarded as a localization segment whose
pivot is the boundary alpha index. -/
def lemma715FullAlphaLocalizationIndex {n : Nat} (s : Nat)
    (hs : s < n + 2) : AlphaLocalizationIndex (n + 2) where
  start := 0
  pivot := s
  stop := n + 2
  start_le_pivot := Nat.zero_le _
  pivot_lt_stop := hs
  stop_lt := by omega

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The canonical whole-list segment witness used for the compression. -/
noncomputable def lemma715FullAlphaSegmentWitness
    (b : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 2) :
    BONG.SegmentWitness b.toBONG
      (lemma715FullAlphaLocalizationIndex s hs).start
      (lemma715FullAlphaLocalizationIndex s hs).length
      (lemma715FullAlphaLocalizationIndex s hs).bound :=
  b.toBONG.segmentWitness _ _ _

/-- The alpha at the pivot of the whole-list segment is the original global
alpha at the same index. -/
theorem lemma715FullAlphaSegment_alphaValue
    (b : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 2) :
    let p := lemma715FullAlphaLocalizationIndex s hs
    let w := b.lemma715FullAlphaSegmentWitness s hs
    (w.toGoodBONG b.good).alphaValue p.localPivot =
      b.alphaValue ⟨s, hs⟩ := by
  dsimp only
  let p := lemma715FullAlphaLocalizationIndex s hs
  let w := b.lemma715FullAlphaSegmentWitness s hs
  let c := w.toGoodBONG b.good
  have hvalues : ∀ j, c.valueUnit j = b.valueUnit j := by
    intro j
    change w.bong.valueUnit j = b.valueUnit j
    rw [w.valueUnit_eq]
    congr 1
    apply Fin.ext
    simp [p, lemma715FullAlphaLocalizationIndex,
      BONG.SegmentWitness.sourceIndex]
  have halpha := c.alphaValue_eq_of_valueUnits_eq b hvalues p.localPivot
  have hindex : p.localPivot = (⟨s, hs⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  change c.alphaValue p.localPivot = b.alphaValue ⟨s, hs⟩
  rw [hindex]
  exact halpha

/-- Left candidates whose adjacent index lies strictly after the boundary. -/
noncomputable def lemma715StrictLeftCandidates
    (b : GoodBONG q L (n + 3)) (s : Nat) (i : Fin (n + 2)) :
    Finset (WithTop ℚ) :=
  (Finset.univ.filter fun j : Fin (n + 2) =>
      s < j.val ∧ j ≤ i).image (b.leftDefectCandidate i)

/-- All right candidates at the later alpha index. -/
noncomputable def lemma715RightCandidates
    (b : GoodBONG q L (n + 3)) (i : Fin (n + 2)) :
    Finset (WithTop ℚ) :=
  (Finset.univ.filter fun j : Fin (n + 2) => i ≤ j).image
    (b.rightDefectCandidate i)

/-- The canonical compressed candidate set for a later alpha. -/
noncomputable def lemma715PropagationAlphaCandidates
    (b : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) : Finset (WithTop ℚ) :=
  let p := lemma715FullAlphaLocalizationIndex s hs
  let w := b.lemma715FullAlphaSegmentWitness s hs
  insert (b.leftCompressionValue p i w : WithTop ℚ)
    (insert (b.halfGapCandidate i)
      (b.lemma715StrictLeftCandidates s i ∪
        b.lemma715RightCandidates i))

theorem lemma715PropagationAlphaCandidates_nonempty
    (b : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) :
    (b.lemma715PropagationAlphaCandidates s hs i).Nonempty := by
  let p := lemma715FullAlphaLocalizationIndex s hs
  let w := b.lemma715FullAlphaSegmentWitness s hs
  exact ⟨(b.leftCompressionValue p i w : WithTop ℚ),
    by simp [lemma715PropagationAlphaCandidates, p, w]⟩

/-- An order strictly inside the common suffix is determined by that suffix. -/
theorem order_eq_of_lemma715_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (j : Fin (n + 3)) (hj : s < j.val) :
    a.order j = b.order j := by
  change a.toBONG.order j = b.toBONG.order j
  rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (htail j hj)

/-- An adjacent defect whose left index is strictly inside the common suffix
is determined by that suffix. -/
theorem adjacentDefect_eq_of_lemma715_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (j : Fin (n + 2)) (hj : s < j.val) :
    a.adjacentDefect j = b.adjacentDefect j := by
  unfold adjacentDefect adjacentProduct
  rw [htail j.castSucc (by simpa using hj),
    htail j.succ (by simp; omega)]

/-- A left-defect candidate whose adjacent index lies strictly after the
boundary is determined by the common suffix. -/
theorem leftDefectCandidate_eq_of_lemma715_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i j : Fin (n + 2)) (hsi : s < i.val) (hsj : s < j.val) :
    a.leftDefectCandidate i j = b.leftDefectCandidate i j := by
  unfold leftDefectCandidate
  rw [a.order_eq_of_lemma715_strict_tail b s htail i.succ (by simp; omega),
    a.order_eq_of_lemma715_strict_tail b s htail j.castSucc
      (by simpa using hsj),
    a.adjacentDefect_eq_of_lemma715_strict_tail b s htail j hsj]

/-- Every right-defect candidate at a later alpha index is determined by the
common suffix. -/
theorem rightDefectCandidate_eq_of_lemma715_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i j : Fin (n + 2)) (hsi : s < i.val) (hij : i ≤ j) :
    a.rightDefectCandidate i j = b.rightDefectCandidate i j := by
  have hsj : s < j.val := lt_of_lt_of_le hsi hij
  unfold rightDefectCandidate
  rw [a.order_eq_of_lemma715_strict_tail b s htail j.succ (by simp; omega),
    a.order_eq_of_lemma715_strict_tail b s htail i.castSucc
      (by simpa using hsi),
    a.adjacentDefect_eq_of_lemma715_strict_tail b s htail j hsj]

/-- The half-gap candidate at a later alpha index is determined by the common
suffix. -/
theorem halfGapCandidate_eq_of_lemma715_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i : Fin (n + 2)) (hsi : s < i.val) :
    a.halfGapCandidate i = b.halfGapCandidate i := by
  unfold halfGapCandidate
  rw [a.order_eq_of_lemma715_strict_tail b s htail i.succ (by simp; omega),
    a.order_eq_of_lemma715_strict_tail b s htail i.castSucc
      (by simpa using hsi)]

/-- The compressed boundary contribution is determined by the boundary alpha
and the common suffix. -/
theorem leftCompressionValue_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) (hsi : s < i.val)
    (hboundary : a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.leftCompressionValue (lemma715FullAlphaLocalizationIndex s hs) i
        (a.lemma715FullAlphaSegmentWitness s hs) =
      b.leftCompressionValue (lemma715FullAlphaLocalizationIndex s hs) i
        (b.lemma715FullAlphaSegmentWitness s hs) := by
  have hboundaryValue : a.alphaValue ⟨s, hs⟩ =
      b.alphaValue ⟨s, hs⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_alphaValue, b.coe_alphaValue, hboundary]
  unfold leftCompressionValue
  rw [a.order_eq_of_lemma715_strict_tail b s htail i.succ (by simp; omega),
    a.order_eq_of_lemma715_strict_tail b s htail
      (lemma715FullAlphaLocalizationIndex s hs).pivotFin.succ (by
        change s < s + 1
        omega),
    a.lemma715FullAlphaSegment_alphaValue s hs,
    b.lemma715FullAlphaSegment_alphaValue s hs,
    hboundaryValue]

/-- The strict-left portion of the canonical propagation set is determined by
the common suffix. -/
theorem lemma715StrictLeftCandidates_eq_of_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i : Fin (n + 2)) (hsi : s < i.val) :
    a.lemma715StrictLeftCandidates s i =
      b.lemma715StrictLeftCandidates s i := by
  unfold lemma715StrictLeftCandidates
  apply Finset.image_congr
  intro j hj
  have hsj := (Finset.mem_filter.mp hj).2.1
  exact a.leftDefectCandidate_eq_of_lemma715_strict_tail b s htail
    i j hsi hsj

/-- The right portion of the canonical propagation set is determined by the
common suffix. -/
theorem lemma715RightCandidates_eq_of_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (i : Fin (n + 2)) (hsi : s < i.val) :
    a.lemma715RightCandidates i = b.lemma715RightCandidates i := by
  unfold lemma715RightCandidates
  apply Finset.image_congr
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  exact a.rightDefectCandidate_eq_of_lemma715_strict_tail b s htail
    i j hsi hij

/-- Equality of the boundary alpha and of the strict suffix identifies the
whole canonical candidate set at every later alpha index. -/
theorem lemma715PropagationAlphaCandidates_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) (hsi : s < i.val)
    (hboundary : a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.lemma715PropagationAlphaCandidates s hs i =
      b.lemma715PropagationAlphaCandidates s hs i := by
  dsimp only [lemma715PropagationAlphaCandidates]
  rw [a.leftCompressionValue_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
      b s hs i hsi hboundary htail,
    a.halfGapCandidate_eq_of_lemma715_strict_tail b s htail i hsi,
    a.lemma715StrictLeftCandidates_eq_of_strict_tail b s htail i hsi,
    a.lemma715RightCandidates_eq_of_strict_tail b s htail i hsi]

variable [Beli2006AlphaLaws.{u, v} K]

/-- Exact compressed formula for every alpha strictly after the boundary. -/
theorem alpha_eq_lemma715PropagationAlphaMin
    (b : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) (hsi : s < i.val) :
    b.alpha i =
      (b.lemma715PropagationAlphaCandidates s hs i).min'
        (b.lemma715PropagationAlphaCandidates_nonempty s hs i) := by
  let p := lemma715FullAlphaLocalizationIndex s hs
  let w := b.lemma715FullAlphaSegmentWitness s hs
  have hpivot : p.pivotFin ≤ i := by
    change s ≤ i.val
    omega
  unfold alpha
  apply min'_eq_min'_of_cover
  · intro y hy
    simp only [lemma715PropagationAlphaCandidates, p, w,
      Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | rfl | hy | hy
    · simpa only [alpha] using b.alpha_le_leftCompressionValue p i hpivot w
    · exact Finset.min'_le _ _ (b.halfGapCandidate_mem_alphaCandidates i)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji := (Finset.mem_filter.mp hj).2.2
      exact Finset.min'_le _ _
        (b.leftDefectCandidate_mem_alphaCandidates hji)
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij := (Finset.mem_filter.mp hj).2
      exact Finset.min'_le _ _
        (b.rightDefectCandidate_mem_alphaCandidates hij)
  · intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · exact ⟨b.halfGapCandidate i, by
        simp [lemma715PropagationAlphaCandidates], le_rfl⟩
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji := (Finset.mem_filter.mp hj).2
      by_cases hjs : j.val ≤ s
      · refine ⟨(b.leftCompressionValue p i w : WithTop ℚ), ?_, ?_⟩
        · simp [lemma715PropagationAlphaCandidates, p, w]
        · exact b.leftCompressionValue_le_candidate p i j hpivot
            (by simp [p, lemma715FullAlphaLocalizationIndex])
            (by
              change j.val ≤ s
              exact hjs)
            w
      · refine ⟨b.leftDefectCandidate i j, ?_, le_rfl⟩
        simp only [lemma715PropagationAlphaCandidates, Finset.mem_insert,
          Finset.mem_union]
        apply Or.inr
        apply Or.inr
        apply Or.inl
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, by omega, hji⟩, rfl⟩
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij := (Finset.mem_filter.mp hj).2
      refine ⟨b.rightDefectCandidate i j, ?_, le_rfl⟩
      simp only [lemma715PropagationAlphaCandidates, Finset.mem_insert,
        Finset.mem_union]
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, hij⟩, rfl⟩

/-- Beli (2009/2010), Lemma 2.4 propagation in the form used by Beli (2019),
Lemma 7.15: equality at the boundary and an exact common suffix imply equality
of every later alpha invariant. -/
theorem alpha_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hs : s < n + 2)
    (i : Fin (n + 2)) (hsi : s < i.val)
    (hboundary : a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j) :
    a.alpha i = b.alpha i := by
  rw [a.alpha_eq_lemma715PropagationAlphaMin s hs i hsi,
    b.alpha_eq_lemma715PropagationAlphaMin s hs i hsi]
  have hcandidates := a.lemma715PropagationAlphaCandidates_eq
    b s hs i hsi hboundary htail
  simpa only [hcandidates]

end BONG.GoodBONG

end Bong
