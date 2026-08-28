/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormGenerator
import Bong.Lattice.ScaleBasis

/-!
# Existence of scale generators

This file formalizes the finite-generation step used in O'Meara, Section 91C.
The pairings of a fixed integral basis generate the scale ideal.  Hence a
nonzero pairing of smallest order generates the whole scale ideal.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Finite basis pairings sufficient to generate the scale ideal. -/
noncomputable def scaleValueCandidates (q : QuadraticSpace K V)
    (L : Lattice K V) : Finset K := by
  classical
  exact (Finset.univ.product Finset.univ).image fun ij =>
    q.bilin (L.standardAmbientBasis ij.1) (L.standardAmbientBasis ij.2)

private theorem standardAmbientBasis_mem (L : Lattice K V)
    (i : Fin (Module.finrank K V)) : L.standardAmbientBasis i ∈ L := by
  change L.standardAmbientBasis i ∈ L.toSubmodule
  rw [← L.coe_standardIntegralBasis_apply i]
  exact (L.standardIntegralBasis i).property

/-- The finite basis-pairing candidates generate the scale ideal. -/
theorem scaleIdeal_eq_span_scaleValueCandidates
    (q : QuadraticSpace K V) (L : Lattice K V) :
    scaleIdeal q L =
      Submodule.span (IntegerRing K) (scaleValueCandidates q L : Set K) := by
  let I := Submodule.span (IntegerRing K) (scaleValueCandidates q L : Set K)
  apply le_antisymm
  · apply scaleIdeal_le_of_integralBasis L.standardIntegralBasis I
    intro i j
    apply Submodule.subset_span
    change q.bilin
        ((L.standardIntegralBasis i : L.toSubmodule) : V)
        ((L.standardIntegralBasis j : L.toSubmodule) : V) ∈
      scaleValueCandidates q L
    simp [scaleValueCandidates, L.coe_standardIntegralBasis_apply]
  · rw [Submodule.span_le]
    intro a ha
    change a ∈ scaleValueCandidates q L at ha
    simp only [scaleValueCandidates, Finset.mem_image] at ha
    rcases ha with ⟨ij, _, hia⟩
    rw [← hia]
    exact bilin_mem_scaleIdeal_of_mem q L
      (standardAmbientBasis_mem L ij.1)
      (standardAmbientBasis_mem L ij.2)

/-- Every scale candidate is the pairing of two actual lattice vectors. -/
theorem exists_pair_of_mem_scaleValueCandidates
    (q : QuadraticSpace K V) (L : Lattice K V) {a : K}
    (ha : a ∈ scaleValueCandidates q L) :
    ∃ x y : V, x ∈ L ∧ y ∈ L ∧ q.bilin x y = a := by
  classical
  simp only [scaleValueCandidates, Finset.mem_image] at ha
  rcases ha with ⟨ij, _, hia⟩
  exact ⟨L.standardAmbientBasis ij.1, L.standardAmbientBasis ij.2,
    standardAmbientBasis_mem L ij.1, standardAmbientBasis_mem L ij.2, hia⟩

/-- A positive-dimensional nondegenerate lattice has a nonzero basis pairing. -/
theorem exists_mem_scaleValueCandidates_ne_zero
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfin : 0 < Module.finrank K V) :
    ∃ a ∈ scaleValueCandidates q L, a ≠ 0 := by
  classical
  letI : Nonempty (Fin (Module.finrank K V)) :=
    Fin.pos_iff_nonempty.mp hfin
  by_contra hexists
  push Not at hexists
  have hpair : ∀ i j : Fin (Module.finrank K V),
      q.bilin (L.standardAmbientBasis i) (L.standardAmbientBasis j) = 0 := by
    intro i j
    exact hexists _ (by simp [scaleValueCandidates])
  have hmatrix : integralGramMatrix q L = 0 := by
    ext i j
    rw [integralGramMatrix_apply, hpair i j]
    rfl
  apply determinant_ne_zero q L
  rw [determinant, hmatrix, Matrix.det_zero]

/-- A pair of lattice vectors whose pairing generates the scale ideal. -/
def IsScaleGenerator (q : QuadraticSpace K V) (L : Lattice K V)
    (x y : V) : Prop :=
  x ∈ L ∧ y ∈ L ∧
    scaleIdeal q L = principalIdeal (K := K) (q.bilin x y)

theorem IsScaleGenerator.mem_left {q : QuadraticSpace K V}
    {L : Lattice K V} {x y : V} (h : IsScaleGenerator q L x y) : x ∈ L :=
  h.1

theorem IsScaleGenerator.mem_right {q : QuadraticSpace K V}
    {L : Lattice K V} {x y : V} (h : IsScaleGenerator q L x y) : y ∈ L :=
  h.2.1

theorem IsScaleGenerator.scaleIdeal_eq {q : QuadraticSpace K V}
    {L : Lattice K V} {x y : V} (h : IsScaleGenerator q L x y) :
    scaleIdeal q L = principalIdeal (K := K) (q.bilin x y) :=
  h.2.2

/-- Every positive-dimensional quadratic lattice has a nonzero scale
generator pair. -/
theorem exists_isScaleGenerator_of_finrank_pos
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfin : 0 < Module.finrank K V) :
    ∃ x y : V, IsScaleGenerator q L x y ∧ q.bilin x y ≠ 0 := by
  classical
  obtain ⟨a, ha, hane⟩ :=
    exists_mem_scaleValueCandidates_ne_zero q L hfin
  let S := (scaleValueCandidates q L).filter fun z => z ≠ 0
  have hS : S.Nonempty := ⟨a, by simp [S, ha, hane]⟩
  obtain ⟨m, hmS, hmin⟩ :=
    Finset.exists_min_image S (fun z => ord K z) hS
  have hm : m ∈ scaleValueCandidates q L := (Finset.mem_filter.mp hmS).1
  have hmne : m ≠ 0 := (Finset.mem_filter.mp hmS).2
  obtain ⟨x, y, hxL, hyL, hxy⟩ :=
    exists_pair_of_mem_scaleValueCandidates q L hm
  refine ⟨x, y, ⟨hxL, hyL, ?_⟩, ?_⟩
  · rw [hxy, scaleIdeal_eq_span_scaleValueCandidates]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro b hb
      change b ∈ scaleValueCandidates q L at hb
      by_cases hbne : b = 0
      · subst b
        exact Submodule.zero_mem _
      · apply mem_principalIdeal_of_ord_le hmne
        exact hmin b (by simp [S, hb, hbne])
    · rw [principalIdeal]
      apply Submodule.span_mono
      simpa using hm
  · rw [hxy]
    exact hmne

end Lattice

end Bong
