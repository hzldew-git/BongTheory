/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan
import Bong.Lattice.ModularMembership
import Bong.Lattice.Restriction
import Mathlib.LinearAlgebra.Projection

/-!
# O'Meara's modular sublattice splitting theorem

This file formalizes the part of O'Meara, Sections 82:15 and 82:15a, used
in Beli's Jordan-component arguments.  A nondegenerate modular sublattice
splits its ambient lattice when the mixed pairings have the modular scale.
The complementary lattice is constructed as the integral intersection with
the orthogonal complement; no splitting law is assumed.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

variable {q : QuadraticSpace K V} {L : Lattice K V}

/-- The two-component family used by a modular splitting. -/
def pairComponents (C D : QuadraticSublattice q) :
    Fin 2 → QuadraticSublattice q :=
  Fin.cases C (fun _ ↦ D)

@[simp]
theorem pairComponents_zero (C D : QuadraticSublattice q) :
    pairComponents C D 0 = C :=
  rfl

@[simp]
theorem pairComponents_one (C D : QuadraticSublattice q) :
    pairComponents C D 1 = D :=
  rfl

namespace QuadraticSublattice

variable [FiniteDimensional K V]

noncomputable def orthogonalCarrier (C : QuadraticSublattice q) :
    Submodule K V :=
  q.bilin.orthogonal C.carrier

theorem carrier_isCompl_orthogonalCarrier (C : QuadraticSublattice q) :
    IsCompl C.carrier C.orthogonalCarrier :=
  q.bilin.isCompl_orthogonal_of_restrict_nondegenerate
    q.isSymm.isRefl C.nondegenerate

theorem orthogonalCarrier_nondegenerate (C : QuadraticSublattice q) :
    (q.bilin.restrict C.orthogonalCarrier).Nondegenerate := by
  rw [q.bilin.restrict_nondegenerate_iff_isCompl_orthogonal q.isSymm.isRefl]
  have hcompl := C.carrier_isCompl_orthogonalCarrier
  have horth : q.bilin.orthogonal C.orthogonalCarrier = C.carrier := by
    exact q.bilin.orthogonal_orthogonal q.nondegenerate
      q.isSymm.isRefl C.carrier
  rw [horth]
  exact hcompl.symm

noncomputable def carrierProjection (C : QuadraticSublattice q) :
    V →ₗ[K] C.carrier :=
  C.carrier.projectionOnto C.orthogonalCarrier
    C.carrier_isCompl_orthogonalCarrier

noncomputable def orthogonalProjection (C : QuadraticSublattice q) :
    V →ₗ[K] C.orthogonalCarrier :=
  C.orthogonalCarrier.projectionOnto C.carrier
    C.carrier_isCompl_orthogonalCarrier.symm

@[simp]
theorem carrierProjection_add_orthogonalProjection (C : QuadraticSublattice q)
    (x : V) :
    (C.carrierProjection x : V) + (C.orthogonalProjection x : V) = x := by
  exact Submodule.projection_add_projection_eq_self
    C.carrier_isCompl_orthogonalCarrier x

theorem carrierProjection_mem_lattice_of_pairing
    (C : QuadraticSublattice q) {a : Kˣ}
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K))
    {x : V} (hx : x ∈ L) : C.carrierProjection x ∈ C.lattice := by
  rw [hmodular.mem_iff_pairing_mem_principal]
  intro y hy
  change q.bilin (C.carrierProjection x : V) (y : V) ∈
    principalIdeal (K := K) (a : K)
  have horth : q.bilin (y : V) (C.orthogonalProjection x : V) = 0 :=
    (C.orthogonalProjection x).property (y : V) y.property
  have hdecomp := C.carrierProjection_add_orthogonalProjection x
  have heq : q.bilin (C.carrierProjection x : V) (y : V) =
      q.bilin (y : V) x := by
    calc
      q.bilin (C.carrierProjection x : V) (y : V) =
          q.bilin (y : V) (C.carrierProjection x : V) :=
        q.isSymm.eq (C.carrierProjection x : V) (y : V)
      _ = q.bilin (y : V)
          ((C.carrierProjection x : V) +
            (C.orthogonalProjection x : V)) := by
        rw [LinearMap.BilinForm.add_right, horth, add_zero]
      _ = q.bilin (y : V) x := congrArg (q.bilin (y : V)) hdecomp
  rw [heq]
  exact hpair y hy x hx

theorem orthogonalProjection_mem_lattice
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K))
    {x : V} (hx : x ∈ L) : (C.orthogonalProjection x : V) ∈ L := by
  have hp := C.carrierProjection_mem_lattice_of_pairing hmodular hpair hx
  have hpL : (C.carrierProjection x : V) ∈ L :=
    hCL ⟨C.carrierProjection x, hp, rfl⟩
  have hdecomp := C.carrierProjection_add_orthogonalProjection x
  have heq : (C.orthogonalProjection x : V) =
      x - (C.carrierProjection x : V) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hdecomp
  rw [heq]
  exact L.sub_mem hx hpL

theorem orthogonalCarrier_spans_comap
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K)) :
    Submodule.span K
      ({z : C.orthogonalCarrier | (z : V) ∈ L} : Set C.orthogonalCarrier) = ⊤ := by
  apply top_unique
  intro z _
  have hzV : (z : V) ∈ Submodule.span K (L : Set V) := by
    rw [L.spans]
    exact Submodule.mem_top
  have hzProj : C.orthogonalProjection (z : V) ∈
      Submodule.span K
        (C.orthogonalProjection '' (L : Set V)) :=
    Submodule.apply_mem_span_image_of_mem_span C.orthogonalProjection hzV
  have himage : C.orthogonalProjection '' (L : Set V) ⊆
      {w : C.orthogonalCarrier | (w : V) ∈ L} := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.orthogonalProjection_mem_lattice hCL hmodular hpair hx
  have hzSpan := Submodule.span_mono himage hzProj
  simpa [orthogonalProjection] using hzSpan

noncomputable def orthogonalLattice
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K)) :
    Lattice K C.orthogonalCarrier :=
  comapSubtype L C.orthogonalCarrier
    (C.orthogonalCarrier_spans_comap hCL hmodular hpair)

noncomputable def orthogonalSublattice
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K)) :
    QuadraticSublattice q where
  carrier := C.orthogonalCarrier
  nondegenerate := C.orthogonalCarrier_nondegenerate
  lattice := C.orthogonalLattice hCL hmodular hpair

end QuadraticSublattice

/-- O'Meara 82:15: a modular sublattice splits when all mixed pairings
are divisible by its scale. -/
noncomputable def omearaModularSplitting
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hpair : ∀ (y : C.carrier), y ∈ C.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈ principalIdeal (K := K) (a : K)) :
    OrthogonalDecomposition q L 2 := by
  letI : Module.Finite K V := L.moduleFinite
  exact {
    component := pairComponents C
      (C.orthogonalSublattice hCL hmodular hpair)
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact y.property (x : V) x.property
      · exact q.isSymm.eq (x : V) (y : V) |>.trans
          (x.property (y : V) y.property)
      · exact False.elim (hij rfl)
    sum_eq := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i
        · exact hCL
        · rintro _ ⟨z, hz, rfl⟩
          exact hz
      · intro x hx
        rw [← C.carrierProjection_add_orthogonalProjection x]
        apply Submodule.add_mem
        · have hle := le_iSup
            (fun i : Fin 2 ↦
              (pairComponents C
                (C.orthogonalSublattice hCL hmodular hpair) i).ambientSubmodule) 0
          apply hle
          exact ⟨C.carrierProjection x,
            C.carrierProjection_mem_lattice_of_pairing hmodular hpair hx, rfl⟩
        · have hle := le_iSup
            (fun i : Fin 2 ↦
              (pairComponents C
                (C.orthogonalSublattice hCL hmodular hpair) i).ambientSubmodule) 1
          apply hle
          exact ⟨C.orthogonalProjection x,
            C.orthogonalProjection_mem_lattice hCL hmodular hpair hx, rfl⟩
  }

/-- O'Meara 82:15a: a modular sublattice at the ambient scale splits. -/
noncomputable def omearaModularSplittingOfScaleIdealLe
    (C : QuadraticSublattice q) {a : Kˣ}
    (hCL : C.ambientSubmodule ≤ L.toSubmodule)
    (hmodular : IsModular C.space C.lattice a)
    (hscale : scaleIdeal q L ≤
      principalIdeal (K := K) (a : K)) :
    OrthogonalDecomposition q L 2 :=
  omearaModularSplitting C hCL hmodular fun y hy _ hx ↦
    hscale (bilin_mem_scaleIdeal_of_mem q L
      (hCL ⟨y, hy, rfl⟩) hx)

end Lattice

end Bong
