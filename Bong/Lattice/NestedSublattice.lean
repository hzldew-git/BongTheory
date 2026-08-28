/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularIsometry
import Bong.Lattice.NormGeneratorIsometry
import Bong.Lattice.Jordan

/-!
# Nested quadratic sublattices

A quadratic sublattice of the restricted space carried by another quadratic
sublattice is canonically a quadratic sublattice of the original space.  This
file supplies that lift together with the exact integral isometry.  It is the
bookkeeping needed to flatten O'Meara's recursive orthogonal-complement
construction into components in one ambient quadratic space.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

namespace QuadraticSublattice

/-- The carrier of a nested sublattice, viewed in the original space. -/
def nestedCarrier (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) : Submodule K V :=
  D.carrier.map C.carrier.subtype

/-- The canonical equivalence from a nested carrier to its ambient image. -/
def nestedCarrierEquiv (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) :
    D.carrier ≃ₗ[K] C.nestedCarrier D :=
  C.carrier.equivSubtypeMap D.carrier

/-- A nested carrier maps into its outer carrier. -/
theorem nestedCarrier_le (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) : C.nestedCarrier D ≤ C.carrier := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

@[simp]
theorem coe_nestedCarrierEquiv (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) (x : D.carrier) :
    (C.nestedCarrierEquiv D x : V) = (x : C.carrier) :=
  rfl

private theorem nestedCarrier_nondegenerate
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space) :
    (q.bilin.restrict (C.nestedCarrier D)).Nondegenerate := by
  let e := C.nestedCarrierEquiv D
  have h := D.nondegenerate.congr e
  convert h using 1
  ext x y
  rfl

/-- A quadratic sublattice of a restricted component, lifted to the original
quadratic space. -/
noncomputable def liftNested (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) : QuadraticSublattice q where
  carrier := C.nestedCarrier D
  nondegenerate := nestedCarrier_nondegenerate C D
  lattice := Lattice.map (C.nestedCarrierEquiv D) D.lattice

@[simp]
theorem liftNested_carrier (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) :
    (C.liftNested D).carrier = C.nestedCarrier D :=
  rfl

/-- The lifted lattice is integrally isometric to the nested lattice. -/
noncomputable def liftNestedIsometry (C : QuadraticSublattice q)
    (D : QuadraticSublattice C.space) :
    Lattice.Isometry D.space (C.liftNested D).space D.lattice
      (C.liftNested D).lattice where
  toLinearEquiv := C.nestedCarrierEquiv D
  map_bilin x y := rfl
  map_mem x := by
    change x ∈ D.lattice ↔ C.nestedCarrierEquiv D x ∈
      Lattice.map (C.nestedCarrierEquiv D) D.lattice
    exact (Lattice.map_mem_map_iff _ _ _).symm

/-- Membership in the ambient lattice of a lifted nested sublattice. -/
theorem mem_liftNested_ambientSubmodule_iff
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space) (x : V) :
    x ∈ (C.liftNested D).ambientSubmodule ↔
      ∃ y : D.carrier, y ∈ D.lattice ∧ (y : V) = x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (show C.nestedCarrier D from z) ∈
        Lattice.map (C.nestedCarrierEquiv D) D.lattice := by
      exact hz
    have hy := (Lattice.mem_map_iff (C.nestedCarrierEquiv D) D.lattice
      (show C.nestedCarrier D from z)).mp hz'
    exact ⟨(C.nestedCarrierEquiv D).symm z, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨C.nestedCarrierEquiv D y, ?_, rfl⟩
    exact (Lattice.map_mem_map_iff
      (C.nestedCarrierEquiv D) D.lattice y).2 hy

/-- The ambient integral module of a lifted nested component is the image of
the nested ambient module under the outer subtype map. -/
theorem ambientSubmodule_liftNested
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space) :
    (C.liftNested D).ambientSubmodule =
      D.ambientSubmodule.map
        ((Submodule.subtype C.carrier).restrictScalars (IntegerRing K)) := by
  ext x
  rw [mem_liftNested_ambientSubmodule_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(y : C.carrier), ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, hyz⟩, hzx⟩
    refine ⟨y, hy, ?_⟩
    exact congrArg Subtype.val hyz |>.trans hzx

/-- A norm generator of a nested component remains a norm generator after
lifting to the original ambient quadratic space. -/
theorem isNormGenerator_liftNested_iff
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space)
    (x : D.carrier) :
    IsNormGenerator (C.liftNested D).space (C.liftNested D).lattice
        (C.nestedCarrierEquiv D x) ↔
      IsNormGenerator D.space D.lattice x :=
  Lattice.isNormGenerator_map_iff (C.liftNestedIsometry D) x

/-- Modularity is preserved when a nested component is lifted to the outer
quadratic space. -/
theorem IsModular.liftNested
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space)
    {a : Kˣ} (hmodular : IsModular D.space D.lattice a) :
    IsModular (C.liftNested D).space (C.liftNested D).lattice a :=
  hmodular.mapLatticeIsometry (C.liftNestedIsometry D)

/-- Lifting a nested carrier preserves its field dimension. -/
theorem finrank_liftNested
    (C : QuadraticSublattice q) (D : QuadraticSublattice C.space) :
    Module.finrank K (C.liftNested D).carrier =
      Module.finrank K D.carrier :=
  (C.nestedCarrierEquiv D).symm.finrank_eq

end QuadraticSublattice

namespace OrthogonalDecomposition

variable {q : QuadraticSpace K V} {t : Nat}

/-- Lifting every component of a decomposition of a nested lattice recovers
the outer component's whole ambient integral module. -/
theorem iSup_liftNested_ambientSubmodule
    (C : QuadraticSublattice q)
    (D : OrthogonalDecomposition C.space C.lattice t) :
    (⨆ i, (C.liftNested (D.component i)).ambientSubmodule) =
      C.ambientSubmodule := by
  simp_rw [QuadraticSublattice.ambientSubmodule_liftNested]
  rw [← Submodule.map_iSup, D.sum_eq]
  rfl

end OrthogonalDecomposition

end Lattice

end Bong
