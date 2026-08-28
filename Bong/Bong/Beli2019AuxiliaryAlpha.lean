/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainConditions

/-!
# Beli (2019), the auxiliary invariant `A'_i`

Section 2 introduces `A'_i` by deleting the half-gap candidate from `A_i`.
This file records that definition directly and proves the decomposition

`A_i = min ((R_(i+1) - S_i) / 2 + e) A'_i`.

These facts are the first algebraic layer in the proof of Lemma 2.16, which
identifies the original condition (iii) with the revised v2 condition (iii').
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Definition 5's candidate set for `A'_i`: the primary defect candidate
and, at an interior boundary, the secondary defect candidate. -/
noncomputable def representationAlphaPrimeCandidates
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) : Finset (WithTop ℚ) :=
  insert (a.representationPrimaryDefect b i)
    (if h : 1 < i.val ∧ i.val + 1 < m + 1 then
      {a.representationSecondaryDefect b i h}
    else ∅)

/-- The candidate set for `A'_i` is nonempty because it always contains the
primary defect candidate. -/
theorem representationAlphaPrimeCandidates_nonempty
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    (a.representationAlphaPrimeCandidates b i).Nonempty :=
  ⟨a.representationPrimaryDefect b i, Finset.mem_insert_self _ _⟩

/-- Beli (2019), Definition 5: the auxiliary invariant `A'_i`. -/
noncomputable def representationAlphaPrime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) : WithTop ℚ :=
  (a.representationAlphaPrimeCandidates b i).min'
    (a.representationAlphaPrimeCandidates_nonempty b i)

/-- The primary term is an upper bound for the minimum `A'_i`. -/
theorem representationAlphaPrime_le_primaryDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaPrime b i ≤ a.representationPrimaryDefect b i := by
  apply Finset.min'_le
  exact Finset.mem_insert_self _ _

/-- At an interior boundary, the secondary term is also an upper bound for
the minimum `A'_i`. -/
theorem representationAlphaPrime_le_secondaryDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i ≤
      a.representationSecondaryDefect b i hi := by
  apply Finset.min'_le
  simp [representationAlphaPrimeCandidates, hi]

/-- Definition 5's decomposition
`A_i = min ((R_(i+1) - S_i) / 2 + e) A'_i`. -/
theorem representationAlpha_eq_min_halfGap_prime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i =
      min (a.representationHalfGap b i) (a.representationAlphaPrime b i) := by
  unfold representationAlpha representationAlphaCandidates
    representationAlphaPrime representationAlphaPrimeCandidates
  rw [Finset.min'_insert]

/-- Removing the half-gap candidate can only increase the minimum. -/
theorem representationAlpha_le_prime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i ≤ a.representationAlphaPrime b i := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i]
  exact min_le_right _ _

/-- If the half-gap candidate is no smaller than `A'_i`, it is redundant. -/
theorem representationAlpha_eq_prime_of_prime_le_halfGap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (h : a.representationAlphaPrime b i ≤ a.representationHalfGap b i) :
    a.representationAlpha b i = a.representationAlphaPrime b i := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i, min_eq_right h]

/-- If the half-gap candidate is at most `A'_i`, it realizes `A_i`. -/
theorem representationAlpha_eq_halfGap_of_halfGap_le_prime
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (h : a.representationHalfGap b i ≤ a.representationAlphaPrime b i) :
    a.representationAlpha b i = a.representationHalfGap b i := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i, min_eq_left h]

end BONG.GoodBONG

end Bong
