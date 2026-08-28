/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma93Ordinary

/-!
# Beli (2019), Lemma 9.3: low candidate bounds

The long case split in the proof does not normally identify every capped
defect before and after deleting the heads.  Instead it proves that the tail
value `A_i^*` lies below every candidate that can realize `A_i`.  This file
records that weaker, exact reduction.
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
  {L : Lattice K V} {M : Lattice K W} {n N : Nat}

private theorem representationIndex_eq_of_val_eq
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- At every noninitial tail boundary, it is enough to bound `A_i^*` by the
primary and, when present, secondary candidates defining the shifted `A_i`.
The half-gap candidate is identical after deleting equal heads. -/
theorem representationAlpha_tail_le_shift_of_le_candidates
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hprimary :
      a.tail.representationAlpha b.tail i ≤
        a.representationPrimaryDefect b i.tailShift)
    (hsecondary : ∀ hinterior : i.val + 1 < n + 1,
      a.tail.representationAlpha b.tail i ≤
        a.representationSecondaryDefect b i.tailShift
          ⟨by
            simp only [RepresentationIndex.tailShift_val]
            omega,
           by
            simp only [RepresentationIndex.tailShift_val]
            omega⟩) :
    a.tail.representationAlpha b.tail i ≤
      a.representationAlpha b i.tailShift := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i.tailShift]
  apply le_min
  · rw [← a.representationHalfGap_tail_eq_shift b i]
    exact a.tail.representationAlpha_le_halfGap b.tail i
  · by_cases hinterior : i.val + 1 < n + 1
    · have horiginalInterior :
          1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
        simp only [RepresentationIndex.tailShift_val]
        omega
      rw [a.representationAlphaPrime_eq_min_primary_secondary
        b i.tailShift horiginalInterior]
      exact le_min hprimary (hsecondary hinterior)
    · have horiginalNotInterior :
          ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
        simp only [RepresentationIndex.tailShift_val]
        omega
      rw [a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift horiginalNotInterior]
      exact hprimary

/-- At the first tail boundary, Lemma 8.12(ii) removes the apparent extra
secondary candidate in the shifted original invariant.  A bound by the
primary candidate is therefore sufficient. -/
theorem representationAlpha_tail_first_le_originalSecond_of_le_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hfirst : a.order (0 : Fin (N + 3)) =
      b.order (0 : Fin (N + 3)))
    (hprimary :
      a.tail.representationAlpha b.tail
          (firstRepresentationIndex N (N + 1)) ≤
        a.representationPrimaryDefect b
          (secondRepresentationIndex N (N + 1))) :
    a.tail.representationAlpha b.tail
        (firstRepresentationIndex N (N + 1)) ≤
      a.representationAlpha b
        (secondRepresentationIndex N (N + 1)) := by
  let first := firstRepresentationIndex N (N + 1)
  have hshift : first.tailShift = secondRepresentationIndex N (N + 1) := by
    apply representationIndex_eq_of_val_eq
    simp only [RepresentationIndex.tailShift_val, first,
      firstRepresentationIndex, secondRepresentationIndex]
  rw [a.beli2019Lemma812_ii b hfirst]
  apply le_min
  · calc
      a.tail.representationAlpha b.tail
          (firstRepresentationIndex N (N + 1)) ≤
          a.tail.representationHalfGap b.tail
            (firstRepresentationIndex N (N + 1)) :=
        a.tail.representationAlpha_le_halfGap b.tail _
      _ = a.representationHalfGap b
          (secondRepresentationIndex N (N + 1)) := by
        have hhalf := a.representationHalfGap_tail_eq_shift b first
        rw [hshift] at hhalf
        simpa only [first] using hhalf
      _ = a.secondRepresentationHalfGapFormula b :=
        a.representationHalfGap_second_eq_formula b
  · simpa only [representationPrimaryDefect_second_eq_formula] using hprimary

/-- Candidate-wise lower bounds produce the low reverse certificate.  This
is the reusable target for the individual numerical branches in Beli's
proof. -/
theorem Beli2019Lemma93LowReverseCertificate.ofCandidateBounds
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93NormalizedPair a b)
    (hprimary : ∀ (i : RepresentationIndex (N + 3) (N + 3))
      (_ : D.targetTransform.transformed.tail.IsCurrentEssential
          D.sourceTransform.transformed.tail i ∨
        D.targetTransform.transformed.tail.IsNextEssential
          D.sourceTransform.transformed.tail i)
      (_ : i.val ≤ 4),
      D.targetTransform.transformed.tail.representationAlpha
          D.sourceTransform.transformed.tail i ≤
        D.targetTransform.transformed.representationPrimaryDefect
          D.sourceTransform.transformed i.tailShift)
    (hsecondary : ∀ (i : RepresentationIndex (N + 3) (N + 3))
      (_ : D.targetTransform.transformed.tail.IsCurrentEssential
          D.sourceTransform.transformed.tail i ∨
        D.targetTransform.transformed.tail.IsNextEssential
          D.sourceTransform.transformed.tail i)
      (_ : 1 < i.val) (_ : i.val ≤ 4)
      (hinterior : i.val + 1 < N + 3),
      D.targetTransform.transformed.tail.representationAlpha
          D.sourceTransform.transformed.tail i ≤
        D.targetTransform.transformed.representationSecondaryDefect
          D.sourceTransform.transformed i.tailShift
            ⟨by
              simp only [RepresentationIndex.tailShift_val]
              omega,
             by
              simp only [RepresentationIndex.tailShift_val]
              omega⟩) :
    Beli2019Lemma93LowReverseCertificate a b D where
  reverseAtImportant i himportant hlow := by
    by_cases hone : i.val = 1
    · have hi : i = firstRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq
        simpa only [firstRepresentationIndex] using hone
      have hshift :
          (firstRepresentationIndex (N + 1) (N + 2)).tailShift =
            secondRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq
        simp only [RepresentationIndex.tailShift_val,
          firstRepresentationIndex, secondRepresentationIndex]
      have horder :
          D.targetTransform.transformed.order (0 : Fin (N + 4)) =
            D.sourceTransform.transformed.order (0 : Fin (N + 4)) := by
        unfold GoodBONG.order
        rw [D.targetTransform.transformed.toBONG.order_eq_ordUnit,
          D.sourceTransform.transformed.toBONG.order_eq_ordUnit]
        exact congrArg (ordUnit K) (by
          apply Units.ext
          exact D.headValue_eq)
      have hp := hprimary i himportant hlow
      rw [hi, hshift] at hp
      rw [hi, hshift]
      exact representationAlpha_tail_first_le_originalSecond_of_le_primary
        D.targetTransform.transformed D.sourceTransform.transformed horder hp
    · have hi : 1 < i.val := by
        have := i.pos
        omega
      exact representationAlpha_tail_le_shift_of_le_candidates
        D.targetTransform.transformed D.sourceTransform.transformed i hi
          (hprimary i himportant hlow)
          (hsecondary i himportant hi hlow)

end BONG.GoodBONG

end Bong
