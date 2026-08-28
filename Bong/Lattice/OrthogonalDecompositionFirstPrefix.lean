/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionTail

/-!
# The first prefix of an orthogonal decomposition

For a nonempty orthogonal decomposition, the intrinsic prefix of length one
is canonically the first component, both as a quadratic space and as an
integral lattice.  The explicit isometry below lets determinant and
representation statements at the first O'Meara boundary be rewritten as
statements about the first Jordan component.
-/

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The carrier of the prefix of length one is the carrier of the head
component. -/
theorem prefixCarrier_one
    (D : OrthogonalDecomposition q L (n + 1)) :
    D.prefixCarrier 1 = (D.component 0).carrier := by
  unfold prefixCarrier
  apply le_antisymm
  · apply iSup_le
    intro i
    have hi : i.1 = (0 : Fin (n + 1)) := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.2)
    simpa [hi]
  · exact le_iSup
      (fun i : D.PrefixIndex 1 ↦ (D.component i.1).carrier)
      ⟨0, by simp⟩

/-- Integral analogue of `prefixCarrier_one`, valid also for a
one-component decomposition. -/
theorem prefixAmbientSubmodule_one_nonempty
    (D : OrthogonalDecomposition q L (n + 1)) :
    D.prefixAmbientSubmodule 1 =
      (D.component 0).ambientSubmodule := by
  unfold prefixAmbientSubmodule
  apply le_antisymm
  · apply iSup_le
    intro i
    have hi : i.1 = (0 : Fin (n + 1)) := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.2)
    simpa [hi]
  · exact le_iSup
      (fun i : D.PrefixIndex 1 ↦
        (D.component i.1).ambientSubmodule)
      ⟨0, by simp⟩

/-- Canonical linear equivalence from the head carrier to the intrinsic
first-prefix carrier. -/
noncomputable def firstComponentPrefixLinearEquiv
    (D : OrthogonalDecomposition q L (n + 1)) :
    (D.component 0).carrier ≃ₗ[K] D.prefixCarrier 1 :=
  LinearEquiv.ofEq _ _ D.prefixCarrier_one.symm

@[simp]
theorem coe_firstComponentPrefixLinearEquiv
    (D : OrthogonalDecomposition q L (n + 1))
    (x : (D.component 0).carrier) :
    ((D.firstComponentPrefixLinearEquiv x : D.prefixCarrier 1) : V) = x :=
  rfl

/-- The first component is integrally isometric to the intrinsic prefix of
length one. -/
noncomputable def firstComponentPrefixLatticeIsometry
    (D : OrthogonalDecomposition q L (n + 1)) :
    Isometry (D.component 0).space
      (D.prefixQuadraticSublattice 1).space
      (D.component 0).lattice
      (D.prefixQuadraticSublattice 1).lattice where
  toLinearEquiv := D.firstComponentPrefixLinearEquiv
  map_bilin _ _ := rfl
  map_mem x := by
    change x ∈ (D.component 0).lattice ↔
      D.firstComponentPrefixLinearEquiv x ∈ D.prefixLattice 1
    rw [D.mem_prefixLattice_iff]
    rw [D.prefixAmbientSubmodule_one_nonempty]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      simpa [hxy] using hy

end Lattice.OrthogonalDecomposition

end Bong
