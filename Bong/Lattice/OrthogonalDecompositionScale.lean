/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan

/-!
# Scale ideals of finite orthogonal decompositions

For a two-component integral orthogonal decomposition, the scale ideal of
the ambient lattice is the supremum of the two component scale ideals.  This
is the scale analogue of the corresponding norm-ideal calculation and is the
ideal-theoretic input needed for Beli (2003), Corollary 4.4(iv).
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- To bound a scale ideal, it is enough to bound every pairing on the
lattice. -/
theorem scaleIdeal_le_of_bilin_mem
    (q : QuadraticSpace K V) (L : Lattice K V)
    (I : CoefficientIdeal (K := K))
    (h : ∀ x y : V, x ∈ L → y ∈ L → q.bilin x y ∈ I) :
    scaleIdeal q L ≤ I := by
  rw [scaleIdeal, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  exact h (p.1 : V) (p.2 : V) p.1.property p.2.property

namespace OrthogonalDecomposition

/-- The scale ideal of a two-component orthogonal decomposition is the
supremum of the component scale ideals. -/
theorem scaleIdeal_eq_sup_components_fin_two
    (D : OrthogonalDecomposition q L 2) :
    scaleIdeal q L =
      scaleIdeal (D.component 0).space (D.component 0).lattice ⊔
        scaleIdeal (D.component 1).space (D.component 1).lattice := by
  let C₀ := D.component 0
  let C₁ := D.component 1
  have hiSup :
      (⨆ i, (D.component i).ambientSubmodule) =
        C₀.ambientSubmodule ⊔ C₁.ambientSubmodule := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · exact _root_.le_sup_left
      · exact _root_.le_sup_right
    · exact _root_.sup_le
        (le_iSup (fun i ↦ (D.component i).ambientSubmodule) 0)
        (le_iSup (fun i ↦ (D.component i).ambientSubmodule) 1)
  have hsum : C₀.ambientSubmodule ⊔ C₁.ambientSubmodule = L.toSubmodule :=
    hiSup.symm.trans D.sum_eq
  apply le_antisymm
  · apply scaleIdeal_le_of_bilin_mem q L
    intro x y hx hy
    have hx' : x ∈ C₀.ambientSubmodule ⊔ C₁.ambientSubmodule := by
      rw [hsum]
      exact hx
    have hy' : y ∈ C₀.ambientSubmodule ⊔ C₁.ambientSubmodule := by
      rw [hsum]
      exact hy
    rw [Submodule.mem_sup] at hx' hy'
    obtain ⟨x₀, hx₀, x₁, hx₁, hxdecomp⟩ := hx'
    obtain ⟨y₀, hy₀, y₁, hy₁, hydecomp⟩ := hy'
    rcases hx₀ with ⟨x₀', hx₀', rfl⟩
    rcases hx₁ with ⟨x₁', hx₁', rfl⟩
    rcases hy₀ with ⟨y₀', hy₀', rfl⟩
    rcases hy₁ with ⟨y₁', hy₁', rfl⟩
    rw [← hxdecomp, ← hydecomp]
    simp only [map_add, LinearMap.add_apply]
    change
      (q.bilin (x₀' : V) (y₀' : V) + q.bilin (x₁' : V) (y₀' : V)) +
          (q.bilin (x₀' : V) (y₁' : V) +
            q.bilin (x₁' : V) (y₁' : V)) ∈
        scaleIdeal C₀.space C₀.lattice ⊔
          scaleIdeal C₁.space C₁.lattice
    rw [D.orthogonal 0 1 (by decide) x₀' y₁',
      D.orthogonal 1 0 (by decide) x₁' y₀']
    simp only [add_zero, zero_add]
    exact (scaleIdeal (C₀.space) C₀.lattice ⊔
      scaleIdeal (C₁.space) C₁.lattice).add_mem
        ((_root_.le_sup_left : scaleIdeal C₀.space C₀.lattice ≤
          scaleIdeal C₀.space C₀.lattice ⊔
            scaleIdeal C₁.space C₁.lattice)
          (bilin_mem_scaleIdeal_of_mem C₀.space C₀.lattice hx₀' hy₀'))
        ((_root_.le_sup_right : scaleIdeal C₁.space C₁.lattice ≤
          scaleIdeal C₀.space C₀.lattice ⊔
            scaleIdeal C₁.space C₁.lattice)
          (bilin_mem_scaleIdeal_of_mem C₁.space C₁.lattice hx₁' hy₁'))
  · apply _root_.sup_le
    · rw [scaleIdeal, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact bilin_mem_scaleIdeal_of_mem q L
        (D.component_ambientSubmodule_le 0 ⟨p.1, p.1.property, rfl⟩)
        (D.component_ambientSubmodule_le 0 ⟨p.2, p.2.property, rfl⟩)
    · rw [scaleIdeal, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact bilin_mem_scaleIdeal_of_mem q L
        (D.component_ambientSubmodule_le 1 ⟨p.1, p.1.property, rfl⟩)
        (D.component_ambientSubmodule_le 1 ⟨p.2, p.2.property, rfl⟩)

end OrthogonalDecomposition

end Lattice

end Bong
