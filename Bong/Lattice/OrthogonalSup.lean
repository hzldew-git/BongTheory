/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Orthogonal sums of quadratic sublattices

Two orthogonal components of an orthogonal decomposition may be amalgamated.
The resulting component is constructed from the corresponding orthogonal
product and the addition equivalence onto the sum of the two carriers.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace OrthogonalDecomposition

variable (D : OrthogonalDecomposition q L t) {i j : Fin t}

/-- Distinct component carriers have zero intersection. -/
theorem component_carrier_disjoint (hij : i ≠ j) :
    Disjoint (D.component i).carrier (D.component j).carrier := by
  rw [Submodule.disjoint_def]
  intro x hxi hxj
  let xi : (D.component i).carrier := ⟨x, hxi⟩
  have hxorth : ∀ y : (D.component i).carrier,
      q.bilin x (y : V) = 0 := by
    intro y
    exact q.isSymm.eq x (y : V) |>.trans
      (D.orthogonal i j hij y ⟨x, hxj⟩)
  have hzero : xi = 0 := (D.component i).nondegenerate.1 xi hxorth
  exact congrArg Subtype.val hzero

/-- The addition map from a pair of component carriers to the ambient
space. -/
def orthogonalSupMap :
    (D.component i).carrier × (D.component j).carrier →ₗ[K] V :=
  (D.component i).carrier.subtype.coprod (D.component j).carrier.subtype

/-- The carrier of the amalgamated component. -/
abbrev orthogonalSupCarrier : Submodule K V :=
  (D.orthogonalSupMap (i := i) (j := j)).range

/-- The addition equivalence from a pair of orthogonal carriers onto the
carrier of their orthogonal sum. -/
noncomputable def orthogonalSupEquiv (hij : i ≠ j) :=
  LinearEquiv.ofInjective
    (orthogonalSupMap D (i := i) (j := j)) (by
    intro x y hxy
    change (x.1 : V) + (x.2 : V) = (y.1 : V) + (y.2 : V) at hxy
    have hsum : (x.1 : V) - (y.1 : V) = (y.2 : V) - (x.2 : V) :=
      sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hxy)
    have hfirst : (x.1 : V) = (y.1 : V) := by
      apply sub_eq_zero.mp
      exact (Submodule.disjoint_def.mp (D.component_carrier_disjoint hij))
        ((x.1 : V) - (y.1 : V))
        (Submodule.sub_mem _ x.1.property y.1.property)
        (hsum ▸ Submodule.sub_mem _ y.2.property x.2.property)
    have hsecond : (x.2 : V) = (y.2 : V) := by
      rw [hfirst] at hxy
      exact add_left_cancel hxy
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond))

@[simp]
theorem coe_orthogonalSupEquiv
    (hij : i ≠ j)
    (x : (D.component i).carrier × (D.component j).carrier) :
    (orthogonalSupEquiv D hij x : V) =
      (x.1 : V) + (x.2 : V) :=
  rfl

/-- The restricted ambient form on the sum carrier is the transported
orthogonal-product form. -/
theorem orthogonalSup_bilin_eq (hij : i ≠ j) :
    q.bilin.restrict (D.orthogonalSupCarrier (i := i) (j := j)) =
      LinearMap.BilinForm.congr (orthogonalSupEquiv D hij)
        ((D.component i).space.orthogonalSum
          (D.component j).space).bilin := by
  let e := orthogonalSupEquiv D hij
  apply LinearMap.BilinForm.ext
  intro x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [LinearMap.BilinForm.congr_apply, e.symm_apply_apply,
    e.symm_apply_apply, QuadraticSpace.orthogonalSum_bilin_apply]
  change q.bilin ((x.1 : V) + (x.2 : V))
    ((y.1 : V) + (y.2 : V)) = _
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right,
    D.orthogonal i j hij, D.orthogonal j i hij.symm]
  change q.bilin (x.1 : V) (y.1 : V) + 0 +
    (0 + q.bilin (x.2 : V) (y.2 : V)) =
      q.bilin (x.1 : V) (y.1 : V) +
        q.bilin (x.2 : V) (y.2 : V)
  simp only [add_zero, zero_add]

/-- The sum of two distinct orthogonal nondegenerate component carriers is
nondegenerate. -/
theorem orthogonalSup_nondegenerate (hij : i ≠ j) :
    (q.bilin.restrict
      (D.orthogonalSupCarrier (i := i) (j := j))).Nondegenerate := by
  rw [D.orthogonalSup_bilin_eq hij]
  exact ((D.component i).space.orthogonalSum
    (D.component j).space).nondegenerate.congr
      (orthogonalSupEquiv D hij)

/-- The addition equivalence is a quadratic isometry from the concrete
orthogonal product. -/
noncomputable def orthogonalSupLatticeIsometry (hij : i ≠ j) :
    Isometry ((D.component i).space.orthogonalSum (D.component j).space)
      (q.restrict (D.orthogonalSupCarrier (i := i) (j := j))
        (D.orthogonalSup_nondegenerate hij))
      (product (D.component i).lattice (D.component j).lattice)
      (map (orthogonalSupEquiv D hij)
        (product (D.component i).lattice (D.component j).lattice)) where
  toLinearEquiv := orthogonalSupEquiv D hij
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    change q.bilin ((x.1 : V) + (x.2 : V))
      ((y.1 : V) + (y.2 : V)) = _
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right,
      D.orthogonal i j hij, D.orthogonal j i hij.symm]
    change q.bilin (x.1 : V) (y.1 : V) + 0 +
      (0 + q.bilin (x.2 : V) (y.2 : V)) =
        q.bilin (x.1 : V) (y.1 : V) +
          q.bilin (x.2 : V) (y.2 : V)
    simp only [add_zero, zero_add]
  map_mem x := (map_mem_map_iff _ _ x).symm

/-- Amalgamation of two distinct orthogonal components. -/
noncomputable def orthogonalSup (hij : i ≠ j) : QuadraticSublattice q where
  carrier := D.orthogonalSupCarrier (i := i) (j := j)
  nondegenerate := D.orthogonalSup_nondegenerate hij
  lattice := map (orthogonalSupEquiv D hij)
    (product (D.component i).lattice (D.component j).lattice)

/-- The dimension of an amalgamated component is the sum of the dimensions
of the original components. -/
theorem orthogonalSup_finrank (hij : i ≠ j) :
    Module.finrank K (D.orthogonalSup hij).carrier =
      Module.finrank K (D.component i).carrier +
        Module.finrank K (D.component j).carrier := by
  letI : Module.Finite K (D.component i).carrier :=
    (D.component i).lattice.moduleFinite
  letI : Module.Finite K (D.component j).carrier :=
    (D.component j).lattice.moduleFinite
  calc
    Module.finrank K (D.orthogonalSup hij).carrier =
        Module.finrank K
          ((D.component i).carrier × (D.component j).carrier) :=
      (orthogonalSupEquiv D hij).finrank_eq.symm
    _ = Module.finrank K (D.component i).carrier +
        Module.finrank K (D.component j).carrier :=
      Module.finrank_prod

/-- Amalgamating a positive-dimensional component with another component
produces a positive-dimensional component. -/
theorem orthogonalSup_finrank_pos_left (hij : i ≠ j)
    (hi : 0 < Module.finrank K (D.component i).carrier) :
    0 < Module.finrank K (D.orthogonalSup hij).carrier := by
  rw [D.orthogonalSup_finrank hij]
  exact Nat.lt_add_right _ hi

/-- The integral lattice underlying an amalgamated component is the sum of
the two original integral component lattices in the ambient space. -/
theorem orthogonalSup_ambientSubmodule (hij : i ≠ j) :
    (D.orthogonalSup hij).ambientSubmodule =
      (D.component i).ambientSubmodule ⊔
        (D.component j).ambientSubmodule := by
  ext x
  constructor
  · intro hx
    rw [QuadraticSublattice.mem_ambientSubmodule_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change ∃ z, z ∈ product (D.component i).lattice
        (D.component j).lattice ∧
      orthogonalSupEquiv D hij z = y at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hz' : z.1 ∈ (D.component i).lattice ∧
        z.2 ∈ (D.component j).lattice :=
      mem_product_iff.mp hz
    rw [Submodule.mem_sup]
    refine ⟨(z.1 : V), ⟨z.1, hz'.1, rfl⟩,
      (z.2 : V), ⟨z.2, hz'.2, rfl⟩, ?_⟩
    exact (D.coe_orthogonalSupEquiv hij z).symm.trans
      (congrArg Subtype.val hzy)
  · intro hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
    rw [QuadraticSublattice.mem_ambientSubmodule_iff] at hx₁ hx₂
    obtain ⟨y₁, hy₁, rfl⟩ := hx₁
    obtain ⟨y₂, hy₂, rfl⟩ := hx₂
    let z : (D.component i).carrier × (D.component j).carrier :=
      (y₁, y₂)
    let y := orthogonalSupEquiv D hij z
    refine ⟨y, ?_, ?_⟩
    · change y ∈ map (orthogonalSupEquiv D hij)
        (product (D.component i).lattice
          (D.component j).lattice)
      exact (map_mem_map_iff (orthogonalSupEquiv D hij) _ z).2
        (mem_product_iff.2 ⟨hy₁, hy₂⟩)
    · exact D.coe_orthogonalSupEquiv hij z

/-- An amalgamated pair remains orthogonal to every other component. -/
theorem orthogonalSup_orthogonal_component {k : Fin t}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : (D.orthogonalSup hij).carrier)
    (y : (D.component k).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  obtain ⟨z, hz⟩ := x.property
  change (z.1 : V) + (z.2 : V) = (x : V) at hz
  rw [← hz, LinearMap.BilinForm.add_left,
    D.orthogonal i k hik, D.orthogonal j k hjk, add_zero]

/-- Every other component remains orthogonal to an amalgamated pair. -/
theorem component_orthogonal_orthogonalSup {k : Fin t}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (x : (D.component k).carrier)
    (y : (D.orthogonalSup hij).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  exact q.isSymm.eq (x : V) (y : V) |>.trans
    (D.orthogonalSup_orthogonal_component hij hki.symm hkj.symm y x)

/-- Equal-scale modular components remain modular after amalgamation. -/
theorem IsModular.orthogonalSupComponents {a : Kˣ}
    {i j : Fin t} (hij : i ≠ j)
    (hi : IsModular (D.component i).space (D.component i).lattice a)
    (hj : IsModular (D.component j).space (D.component j).lattice a) :
    IsModular
      (OrthogonalDecomposition.orthogonalSup D hij).space
      (OrthogonalDecomposition.orthogonalSup D hij).lattice a := by
  exact (hi.orthogonalProduct hj).mapLatticeIsometry
    (OrthogonalDecomposition.orthogonalSupLatticeIsometry D hij)

end OrthogonalDecomposition

end Lattice

end Bong
