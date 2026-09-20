/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.Basic
import Bong.QuadraticSpace.ScalarExtension

/-!
# Integral lattices under scalar extension

For the carrier step in He Classic v6, Lemma 8.3, it is essential that the
upper lattice be the scalar extension of the *specified* lower lattice, not
merely a lattice with the same diagonal coefficients.  The definition below
uses a chosen integral basis; the theorem identifies it intrinsically as the
integral span of the pure tensors of all lower-lattice vectors.

The sole arithmetic premise is that the field embedding sends the lower
valuation ring into the upper valuation ring.  For finite number-field
completions this follows from the ramification-index valuation formula.
-/

namespace Bong.Lattice

open Dyadic
open scoped TensorProduct

universe u v w

variable {F : Type u} {E : Type v} {V : Type w}
  [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [DyadicContext F]
  [Field E] [CharZero E] [ValuativeRel E] [TopologicalSpace E]
  [DyadicContext E] [Algebra F E]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The integral lattice obtained from a lower lattice by extending its
chosen integral basis to the scalar-extension ambient space.  The span theorem
below shows that this definition does not depend on the basis choice. -/
noncomputable def scalarExtension (L : Lattice F V) :
    Lattice E (E ⊗[F] V) :=
  basisLattice (L.standardAmbientBasis.baseChange E)

omit [FiniteDimensional F V] in
/-- Concrete scalar extension is the upper integral span of the pure tensors
of every vector of the original lattice.  This characterizes the carrier of
`scalarExtension` without a chosen-basis hypothesis. -/
theorem scalarExtension_toSubmodule_eq_span
    (L : Lattice F V)
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F))) :
    (scalarExtension (E := E) L).toSubmodule =
      Submodule.span (IntegerRing E)
        (Set.range (fun x : L.toSubmodule => (1 : E) ⊗ₜ[F] (x : V))) := by
  let T : Submodule (IntegerRing E) (E ⊗[F] V) :=
    Submodule.span (IntegerRing E)
      (Set.range (L.standardAmbientBasis.baseChange E))
  change T = Submodule.span (IntegerRing E)
    (Set.range (fun x : L.toSubmodule => (1 : E) ⊗ₜ[F] (x : V)))
  have hb (i : Fin (Module.finrank F V)) :
      L.standardAmbientBasis i ∈ L.toSubmodule := by
    rw [L.toSubmodule_eq_span_standardAmbientBasis]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hImage (x : V) (hx : x ∈ L.toSubmodule) :
      (1 : E) ⊗ₜ[F] x ∈ T := by
    rw [L.toSubmodule_eq_span_standardAmbientBasis] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [← Module.Basis.baseChange_apply]
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
        simp
    | add x y _ _ hx hy =>
        simpa only [TensorProduct.tmul_add] using T.add_mem hx hy
    | smul a x _ hx =>
        let aE : IntegerRing E :=
          ⟨algebraMap F E (a : F), (Dyadic.mem_integerRing_iff E).mpr (hIntegral a)⟩
        have hsmul :
            (1 : E) ⊗ₜ[F] (a • x) =
              aE • ((1 : E) ⊗ₜ[F] x) := by
          rw [← IsScalarTower.algebraMap_smul
            (R := IntegerRing F) (A := F) (M := V) a x]
          rw [TensorProduct.tmul_smul]
          change (a : F) • ((1 : E) ⊗ₜ[F] x) =
            aE • ((1 : E) ⊗ₜ[F] x)
          rw [← IsScalarTower.algebraMap_smul
            (R := F) (A := E) (M := E ⊗[F] V)
            (a : F) ((1 : E) ⊗ₜ[F] x)]
          change (algebraMap F E (a : F)) • ((1 : E) ⊗ₜ[F] x) =
            aE • ((1 : E) ⊗ₜ[F] x)
          exact (IsScalarTower.algebraMap_smul
            (R := IntegerRing E) (A := E) (M := E ⊗[F] V) aE _)
        rw [hsmul]
        exact T.smul_mem aE hx
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨L.standardAmbientBasis i, hb i⟩, ?_⟩
    simp only [Module.Basis.baseChange_apply]
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hImage x x.property

omit [FiniteDimensional F V] in
/-- Scalar extension carries the integral lattice of any finite field basis
to the integral lattice of its scalar-extended basis. -/
theorem scalarExtension_basisLattice
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι F V)
    (hIntegral : ∀ a : IntegerRing F,
      Dyadic.IsIntegral E (algebraMap F E (a : F))) :
    scalarExtension (E := E) (basisLattice b) = basisLattice (b.baseChange E) := by
  let T : Submodule (IntegerRing E) (E ⊗[F] V) :=
    Submodule.span (IntegerRing E) (Set.range (b.baseChange E))
  have hImage (x : V) (hx : x ∈ (basisLattice b).toSubmodule) :
      (1 : E) ⊗ₜ[F] x ∈ T := by
    change x ∈ Submodule.span (IntegerRing F) (Set.range b) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [← Module.Basis.baseChange_apply]
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
        simp
    | add x y _ _ hx hy =>
        simpa only [TensorProduct.tmul_add] using T.add_mem hx hy
    | smul a x _ hx =>
        let aE : IntegerRing E :=
          ⟨algebraMap F E (a : F), (Dyadic.mem_integerRing_iff E).mpr (hIntegral a)⟩
        have hsmul :
            (1 : E) ⊗ₜ[F] (a • x) = aE • ((1 : E) ⊗ₜ[F] x) := by
          rw [← IsScalarTower.algebraMap_smul
            (R := IntegerRing F) (A := F) (M := V) a x]
          rw [TensorProduct.tmul_smul]
          change (a : F) • ((1 : E) ⊗ₜ[F] x) =
            aE • ((1 : E) ⊗ₜ[F] x)
          rw [← IsScalarTower.algebraMap_smul
            (R := F) (A := E) (M := E ⊗[F] V)
            (a : F) ((1 : E) ⊗ₜ[F] x)]
          change (algebraMap F E (a : F)) • ((1 : E) ⊗ₜ[F] x) =
            aE • ((1 : E) ⊗ₜ[F] x)
          exact (IsScalarTower.algebraMap_smul
            (R := IntegerRing E) (A := E) (M := E ⊗[F] V) aE _)
        rw [hsmul]
        exact T.smul_mem aE hx
  apply Lattice.ext
  rw [scalarExtension_toSubmodule_eq_span (E := E) (basisLattice b) hIntegral]
  change Submodule.span (IntegerRing E)
      (Set.range (fun x : (basisLattice b).toSubmodule => (1 : E) ⊗ₜ[F] (x : V))) = T
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hImage x x.property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨b i, ?_⟩, ?_⟩
    · change b i ∈ Submodule.span (IntegerRing F) (Set.range b)
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp only [Module.Basis.baseChange_apply]

end Bong.Lattice
