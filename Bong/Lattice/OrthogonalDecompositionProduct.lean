/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.Product
import Bong.QuadraticSpace.OrthogonalSum

/-!
# Product realization of a two-component orthogonal decomposition

Every integral orthogonal decomposition with two components is the concrete
orthogonal product of its component lattices.  This is the lattice-level
form needed to commute an ambient orthogonal splitting with projection.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace OrthogonalDecomposition

variable (D : OrthogonalDecomposition q L 2)

/-- The two carrier spaces in a binary orthogonal decomposition are
complementary. -/
theorem pairCarriers_isCompl :
    IsCompl (D.component 0).carrier (D.component 1).carrier := by
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz₀ hz₁
    let z₀ : (D.component 0).carrier := ⟨z, hz₀⟩
    let z₁ : (D.component 1).carrier := ⟨z, hz₁⟩
    have hzero : z₀ = 0 := by
      apply (D.component 0).nondegenerate.1 z₀
      intro y
      change q.bilin (z : V) (y : V) = 0
      exact D.orthogonal 1 0 (by decide) z₁ y
    exact congrArg Subtype.val hzero
  · rw [codisjoint_iff]
    rw [← D.carrier_iSup_eq_top]
    apply le_antisymm
    · apply _root_.sup_le
      · exact le_iSup (fun i : Fin 2 ↦ (D.component i).carrier) 0
      · exact le_iSup (fun i : Fin 2 ↦ (D.component i).carrier) 1
    · apply iSup_le
      rw [Fin.forall_fin_two]
      exact ⟨_root_.le_sup_left, _root_.le_sup_right⟩

/-- The complementary-carrier equivalence, concretely `(x,y) ↦ x+y`. -/
noncomputable def pairToAmbientLinearEquiv :
    ((D.component 0).carrier × (D.component 1).carrier) ≃ₗ[K] V :=
  (D.component 0).carrier.prodEquivOfIsCompl
    (D.component 1).carrier D.pairCarriers_isCompl

@[simp]
theorem pairToAmbientLinearEquiv_apply
    (z : (D.component 0).carrier × (D.component 1).carrier) :
    D.pairToAmbientLinearEquiv z = (z.1 : V) + (z.2 : V) :=
  rfl

/-- The integral component sum is the supremum of the two ambient modules. -/
theorem pairAmbientSubmodule_sup_eq :
    (D.component 0).ambientSubmodule ⊔
        (D.component 1).ambientSubmodule = L.toSubmodule := by
  calc
    (D.component 0).ambientSubmodule ⊔
        (D.component 1).ambientSubmodule =
        ⨆ i : Fin 2, (D.component i).ambientSubmodule := by
      apply le_antisymm
      · apply _root_.sup_le
        · exact le_iSup (fun i : Fin 2 ↦
            (D.component i).ambientSubmodule) 0
        · exact le_iSup (fun i : Fin 2 ↦
            (D.component i).ambientSubmodule) 1
      · apply iSup_le
        rw [Fin.forall_fin_two]
        exact ⟨_root_.le_sup_left, _root_.le_sup_right⟩
    _ = L.toSubmodule := D.sum_eq

/-- A two-component decomposition is integrally isometric to the orthogonal
product of its component lattices. -/
noncomputable def pairProductLatticeIsometry :
    Isometry
      ((D.component 0).space.orthogonalSum (D.component 1).space)
      q
      (product (D.component 0).lattice (D.component 1).lattice)
      L where
  toLinearEquiv := D.pairToAmbientLinearEquiv
  map_bilin := by
    intro x y
    change q.bilin ((x.1 : V) + (x.2 : V))
        ((y.1 : V) + (y.2 : V)) =
      q.bilin (x.1 : V) (y.1 : V) +
        q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    rw [D.orthogonal 0 1 (by decide) x.1 y.2,
      D.orthogonal 1 0 (by decide) x.2 y.1]
    simp
  map_mem := by
    intro z
    rw [mem_product_iff]
    constructor
    · intro hz
      change D.pairToAmbientLinearEquiv z ∈ L.toSubmodule
      rw [← D.pairAmbientSubmodule_sup_eq, Submodule.mem_sup]
      refine ⟨(z.1 : V), ?_, (z.2 : V), ?_, rfl⟩
      · exact ⟨z.1, hz.1, rfl⟩
      · exact ⟨z.2, hz.2, rfl⟩
    · intro hz
      have hz' : D.pairToAmbientLinearEquiv z ∈
          (D.component 0).ambientSubmodule ⊔
            (D.component 1).ambientSubmodule := by
        rw [D.pairAmbientSubmodule_sup_eq]
        exact hz
      rw [Submodule.mem_sup] at hz'
      rcases hz' with ⟨x, ⟨x₀, hx₀, rfl⟩,
        y, ⟨y₁, hy₁, rfl⟩, hxy⟩
      have hpair : (x₀, y₁) = z := by
        apply D.pairToAmbientLinearEquiv.injective
        exact hxy
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact ⟨hx₀, hy₁⟩

@[simp]
theorem pairProductLatticeIsometry_apply_left
    (x : (D.component 0).carrier) :
    D.pairProductLatticeIsometry.toLinearEquiv (x, 0) = (x : V) := by
  change (x : V) + 0 = (x : V)
  simp

@[simp]
theorem pairProductLatticeIsometry_apply_right
    (y : (D.component 1).carrier) :
    D.pairProductLatticeIsometry.toLinearEquiv (0, y) = (y : V) := by
  change 0 + (y : V) = (y : V)
  simp

/-- Each factor of a two-component splitting of an `a`-modular lattice is
`a`-modular. -/
theorem component_modular_of_ambient {a : Kˣ}
    (hmodular : IsModular q L a) (i : Fin 2) :
    IsModular (D.component i).space (D.component i).lattice a := by
  have hproduct : IsModular
      ((D.component 0).space.orthogonalSum (D.component 1).space)
      (product (D.component 0).lattice (D.component 1).lattice) a :=
    hmodular.mapLatticeIsometry D.pairProductLatticeIsometry.symm
  fin_cases i
  · exact IsModular.left_of_orthogonalProduct hproduct
  · exact IsModular.right_of_orthogonalProduct hproduct

end OrthogonalDecomposition

end Lattice

end Bong
