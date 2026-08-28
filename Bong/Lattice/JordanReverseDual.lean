/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormRescale
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Lattice.OrthogonalDecompositionIdeals

/-!
# Reverse duals of Jordan decompositions

O'Meara 93:24 reverses a Jordan chain after taking the integral dual.
This file constructs that Jordan decomposition with explicit generators:
an `s`-modular component with norm generator `a` becomes an
`s⁻¹`-modular component with norm generator `s⁻² a`.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The scale generator of the reverse-dual component. -/
noncomputable def reverseDualScaleGenerator
    (J : JordanDecomposition q L t) (i : Fin t) : Kˣ :=
  (J.scaleGenerator (Fin.rev i))⁻¹

/-- The norm generator of the reverse-dual component. -/
noncomputable def reverseDualNormGenerator
    (J : JordanDecomposition q L t) (i : Fin t) : Kˣ :=
  (J.scaleGenerator (Fin.rev i))⁻¹ ^ 2 *
    J.normGenerator (Fin.rev i)

/-- Reversing the componentwise integral duals produces a Jordan
decomposition of the ambient integral dual lattice. -/
noncomputable def reverseDual
    (J : JordanDecomposition q L t) :
    JordanDecomposition q (dualLattice q L) t where
  toOrthogonalDecomposition := J.toOrthogonalDecomposition.reverseDual
  scaleGenerator := J.reverseDualScaleGenerator
  normGenerator := J.reverseDualNormGenerator
  modular := by
    intro i
    exact (J.modular (Fin.rev i)).dual
  scaleIdeal_eq := by
    intro i
    exact (J.modular (Fin.rev i)).dual.scaleIdeal_eq_principal
      (J.component_finrank_pos (Fin.rev i))
  normIdeal_eq := by
    intro i
    change normIdeal (J.component (Fin.rev i)).space
        (dualLattice (J.component (Fin.rev i)).space
          (J.component (Fin.rev i)).lattice) =
      principalIdeal (K := K)
        (((J.scaleGenerator (Fin.rev i))⁻¹ ^ 2 *
          J.normGenerator (Fin.rev i) : Kˣ) : K)
    rw [J.modular (Fin.rev i)]
    exact normIdeal_rescale_eq_principal_of_finrank_pos
      (J.component_finrank_pos (Fin.rev i))
      (J.scaleGenerator (Fin.rev i))⁻¹
      (J.normGenerator (Fin.rev i)) (J.normIdeal_eq (Fin.rev i))
  scaleOrder_strict := by
    intro i j hij
    unfold reverseDualScaleGenerator
    rw [ordUnit_inv, ordUnit_inv]
    have hrev : Fin.rev j < Fin.rev i :=
      Fin.rev_lt_rev.mpr hij
    have h := J.scaleOrder_strict hrev
    omega

@[simp]
theorem reverseDual_component
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.component i =
      (J.component (Fin.rev i)).dual :=
  rfl

@[simp]
theorem reverseDual_scaleGenerator
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.scaleGenerator i =
      (J.scaleGenerator (Fin.rev i))⁻¹ :=
  rfl

@[simp]
theorem reverseDual_normGenerator
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.normGenerator i =
      (J.scaleGenerator (Fin.rev i))⁻¹ ^ 2 *
        J.normGenerator (Fin.rev i) :=
  rfl

@[simp]
theorem reverseDual_componentRank
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.componentRank i =
      J.componentRank (Fin.rev i) :=
  rfl

@[simp]
theorem reverseDual_reverseDual_scaleGenerator
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.reverseDual.scaleGenerator i = J.scaleGenerator i := by
  simp

@[simp]
theorem reverseDual_reverseDual_normGenerator
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.reverseDual.normGenerator i = J.normGenerator i := by
  simp

end Lattice.JordanDecomposition

end Bong
