/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Arithmetic

/-!
# Beli (2019), normal forms for `A'_i`

Definition 5 contains exactly two candidates at an interior boundary and
only the primary candidate at an endpoint.  These normal forms expose that
case distinction without unfolding the finite-set implementation in later
proofs.
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

/-- At an interior boundary, Definition 5 is the minimum of its primary
and secondary defect candidates. -/
theorem representationAlphaPrime_eq_min_primary_secondary
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i =
      min (a.representationPrimaryDefect b i)
        (a.representationSecondaryDefect b i hi) := by
  unfold representationAlphaPrime
  apply le_antisymm
  · apply le_min
    · apply Finset.min'_le
      simp [representationAlphaPrimeCandidates]
    · apply Finset.min'_le
      simp [representationAlphaPrimeCandidates, hi]
  · apply Finset.le_min'
    intro x hx
    simp [representationAlphaPrimeCandidates, hi] at hx
    rcases hx with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- At an endpoint, the nonexistent secondary candidate is ignored. -/
theorem representationAlphaPrime_eq_primary_of_not_interior
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : ¬(1 < i.val ∧ i.val + 1 < m + 1)) :
    a.representationAlphaPrime b i =
      a.representationPrimaryDefect b i := by
  have hi' : ¬(1 < i.val ∧ i.val < m) := by omega
  unfold representationAlphaPrime
  apply le_antisymm
  · apply Finset.min'_le
    simp [representationAlphaPrimeCandidates]
  · apply Finset.le_min'
    intro x hx
    simp [representationAlphaPrimeCandidates, hi, hi'] at hx
    simpa [hx]

/-- The primary candidate realizes `A'_i` precisely when it is no larger
than the secondary candidate. -/
theorem representationAlphaPrime_eq_primary_iff
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i =
        a.representationPrimaryDefect b i ↔
      a.representationPrimaryDefect b i ≤
        a.representationSecondaryDefect b i hi := by
  rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
  exact min_eq_left_iff

/-- The secondary candidate realizes `A'_i` precisely when it is no larger
than the primary candidate. -/
theorem representationAlphaPrime_eq_secondary_iff
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i =
        a.representationSecondaryDefect b i hi ↔
      a.representationSecondaryDefect b i hi ≤
        a.representationPrimaryDefect b i := by
  rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
  exact min_eq_right_iff

end BONG.GoodBONG

end Bong
