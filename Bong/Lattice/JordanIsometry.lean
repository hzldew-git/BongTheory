/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan
import Bong.Lattice.ModularIsometry

/-!
# Jordan decompositions under lattice isometry

An integral isometry transports quadratic sublattices, orthogonal
decompositions, and Jordan decompositions without changing their scale and
norm generators.  In particular, Beli's property A is an invariant of the
quadratic lattice, not of a chosen ambient realization.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace QuadraticSublattice

/-- The image carrier of a quadratic sublattice under a lattice isometry. -/
def mapCarrier (C : QuadraticSublattice q) (f : Isometry q r L M) :
    Submodule K W :=
  C.carrier.map f.toLinearEquiv.toLinearMap

/-- The restriction of the ambient equivalence to a sublattice carrier. -/
def mapCarrierEquiv (C : QuadraticSublattice q) (f : Isometry q r L M) :
    C.carrier ≃ₗ[K] C.mapCarrier f := by
  simpa only [mapCarrier] using f.toLinearEquiv.submoduleMap C.carrier

/-- A mapped nondegenerate carrier remains nondegenerate. -/
theorem mapCarrier_nondegenerate
    (C : QuadraticSublattice q) (f : Isometry q r L M) :
    (r.bilin.restrict (C.mapCarrier f)).Nondegenerate := by
  let e := C.mapCarrierEquiv f
  constructor
  · intro y hy
    have hy' : ∀ z : C.carrier,
        C.space.bilin (e.symm y) z = 0 := by
      intro z
      have h := hy (e z)
      change r.bilin (y : W) (f.toLinearEquiv (z : V)) = 0 at h
      have hmap := f.map_bilin (e.symm y : V) (z : V)
      rw [show f.toLinearEquiv (e.symm y : V) = (y : W) by
        exact congrArg Subtype.val (e.apply_symm_apply y)] at hmap
      rwa [hmap] at h
    have hzero : e.symm y = 0 := C.nondegenerate.1 (e.symm y) hy'
    apply e.symm.injective
    simpa only [map_zero] using hzero
  · intro y hy
    have hy' : ∀ z : C.carrier,
        C.space.bilin z (e.symm y) = 0 := by
      intro z
      have h := hy (e z)
      change r.bilin (f.toLinearEquiv (z : V)) (y : W) = 0 at h
      have hmap := f.map_bilin (z : V) (e.symm y : V)
      rw [show f.toLinearEquiv (e.symm y : V) = (y : W) by
        exact congrArg Subtype.val (e.apply_symm_apply y)] at hmap
      rwa [hmap] at h
    have hzero : e.symm y = 0 := C.nondegenerate.2 (e.symm y) hy'
    apply e.symm.injective
    simpa only [map_zero] using hzero

/-- The image of a quadratic sublattice under an integral isometry. -/
noncomputable def mapIsometry
    (C : QuadraticSublattice q) (f : Isometry q r L M) :
    QuadraticSublattice r where
  carrier := C.mapCarrier f
  nondegenerate := C.mapCarrier_nondegenerate f
  lattice := Lattice.map (C.mapCarrierEquiv f) C.lattice

/-- The restricted map is an integral isometry onto the mapped component. -/
noncomputable def mapLatticeIsometry
    (C : QuadraticSublattice q) (f : Isometry q r L M) :
    Isometry C.space (C.mapIsometry f).space C.lattice
      (C.mapIsometry f).lattice where
  toLinearEquiv := C.mapCarrierEquiv f
  map_bilin x y := f.map_bilin (x : V) (y : V)
  map_mem x := (Lattice.map_mem_map_iff (C.mapCarrierEquiv f) C.lattice x).symm

@[simp]
theorem coe_mapCarrierEquiv
    (C : QuadraticSublattice q) (f : Isometry q r L M)
    (x : C.carrier) :
    ((C.mapCarrierEquiv f x : C.mapCarrier f) : W) =
      f.toLinearEquiv (x : V) :=
  rfl

/-- Mapping a component and then embedding it in the target ambient space is
the same as mapping its original ambient integral module. -/
theorem ambientSubmodule_mapIsometry
    (C : QuadraticSublattice q) (f : Isometry q r L M) :
    (C.mapIsometry f).ambientSubmodule =
      C.ambientSubmodule.map
        (f.toLinearEquiv.toLinearMap.restrictScalars (IntegerRing K)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := (Lattice.mem_map_iff (C.mapCarrierEquiv f) C.lattice z).1 hz
    refine ⟨((C.mapCarrierEquiv f).symm z : C.carrier), ?_, ?_⟩
    · exact ⟨(C.mapCarrierEquiv f).symm z, hz', rfl⟩
    · change f.toLinearEquiv (((C.mapCarrierEquiv f).symm z : C.carrier) : V) =
        (z : W)
      exact congrArg Subtype.val ((C.mapCarrierEquiv f).apply_symm_apply z)
  · rintro ⟨y, ⟨x, hx, hxy⟩, hy⟩
    subst y
    refine ⟨C.mapCarrierEquiv f x, ?_, ?_⟩
    · exact (Lattice.map_mem_map_iff (C.mapCarrierEquiv f) C.lattice x).2 hx
    · change f.toLinearEquiv (x : V) = _
      exact hy

/-- Mapping preserves the field rank of a quadratic component. -/
theorem finrank_mapIsometry
    (C : QuadraticSublattice q) (f : Isometry q r L M) :
    finrank K (C.mapIsometry f).carrier = finrank K C.carrier :=
  (C.mapCarrierEquiv f).symm.finrank_eq

end QuadraticSublattice

namespace OrthogonalDecomposition

/-- Transport an integral orthogonal decomposition along a lattice isometry. -/
noncomputable def mapIsometry {t : Nat}
    (D : OrthogonalDecomposition q L t) (f : Isometry q r L M) :
    OrthogonalDecomposition r M t where
  component i := (D.component i).mapIsometry f
  orthogonal := by
    intro i j hij x y
    let x' : (D.component i).mapCarrier f := ⟨(x : W), x.property⟩
    let y' : (D.component j).mapCarrier f := ⟨(y : W), y.property⟩
    let xi : (D.component i).carrier :=
      ((D.component i).mapCarrierEquiv f).symm x'
    let yj : (D.component j).carrier :=
      ((D.component j).mapCarrierEquiv f).symm y'
    have h := D.orthogonal i j hij xi yj
    rw [← f.map_bilin] at h
    have hx : f.toLinearEquiv
        (xi : V) = (x : W) := by
      exact congrArg Subtype.val
        (((D.component i).mapCarrierEquiv f).apply_symm_apply x')
    have hy : f.toLinearEquiv
        (yj : V) = (y : W) := by
      exact congrArg Subtype.val
        (((D.component j).mapCarrierEquiv f).apply_symm_apply y')
    rwa [hx, hy] at h
  sum_eq := by
    simp_rw [QuadraticSublattice.ambientSubmodule_mapIsometry]
    rw [← Submodule.map_iSup]
    rw [D.sum_eq]
    exact congrArg Lattice.toSubmodule f.map_eq

@[simp]
theorem mapIsometry_component {t : Nat}
    (D : OrthogonalDecomposition q L t) (f : Isometry q r L M)
    (i : Fin t) :
    (D.mapIsometry f).component i = (D.component i).mapIsometry f :=
  rfl

end OrthogonalDecomposition

namespace JordanDecomposition

/-- Transport a Jordan decomposition along an integral isometry. -/
noncomputable def mapIsometry {t : Nat}
    (J : JordanDecomposition q L t) (f : Isometry q r L M) :
    JordanDecomposition r M t where
  toOrthogonalDecomposition := J.toOrthogonalDecomposition.mapIsometry f
  scaleGenerator := J.scaleGenerator
  normGenerator := J.normGenerator
  modular := by
    intro i
    exact (J.modular i).mapLatticeIsometry
      ((J.component i).mapLatticeIsometry f)
  scaleIdeal_eq := by
    intro i
    let g := (J.component i).mapLatticeIsometry f
    calc
      scaleIdeal ((J.component i).mapIsometry f).space
          ((J.component i).mapIsometry f).lattice =
          scaleIdeal (J.component i).space (J.component i).lattice := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K) (J.scaleGenerator i : K) :=
        J.scaleIdeal_eq i
  normIdeal_eq := by
    intro i
    let g := (J.component i).mapLatticeIsometry f
    calc
      normIdeal ((J.component i).mapIsometry f).space
          ((J.component i).mapIsometry f).lattice =
          normIdeal (J.component i).space (J.component i).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K) (J.normGenerator i : K) :=
        J.normIdeal_eq i
  scaleOrder_strict := J.scaleOrder_strict

@[simp]
theorem mapIsometry_componentRank {t : Nat}
    (J : JordanDecomposition q L t) (f : Isometry q r L M)
    (i : Fin t) :
    (J.mapIsometry f).componentRank i = J.componentRank i := by
  exact (J.component i).finrank_mapIsometry f

/-- Property A is preserved by an integral isometry. -/
theorem HasPropertyA.mapIsometry {t : Nat}
    {J : JordanDecomposition q L t} (hA : J.HasPropertyA)
    (f : Isometry q r L M) :
    (J.mapIsometry f).HasPropertyA := by
  constructor
  · intro i
    rw [J.mapIsometry_componentRank f i]
    exact hA.1 i
  · intro i j hij
    exact hA.2 hij

end JordanDecomposition

/-- Lattice-level property A is invariant under integral isometry. -/
theorem HasJordanPropertyA.mapIsometry
    (hA : HasJordanPropertyA q L) (f : Isometry q r L M) :
    HasJordanPropertyA r M := by
  rcases hA with ⟨t, J, hJ⟩
  exact ⟨t, J.mapIsometry f, hJ.mapIsometry f⟩

/-- The reverse implication, useful when changing to a concrete model. -/
theorem hasJordanPropertyA_isometry_iff
    (f : Isometry q r L M) :
    HasJordanPropertyA q L ↔ HasJordanPropertyA r M :=
  ⟨fun h ↦ h.mapIsometry f, fun h ↦ h.mapIsometry f.symm⟩

end Lattice

end Bong
