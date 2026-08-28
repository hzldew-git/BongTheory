/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDual
import Bong.Lattice.ScaleTruncationDual
import Bong.Lattice.OmearaFundamentalInvariants
import Bong.Lattice.WeightIdealRescale

/-!
# Fundamental invariants of the reverse-dual Jordan chain

This is the invariant part of O'Meara 93:24.  Reversing a Jordan chain and
taking integral duals negates its scale orders.  At the reversed index, the
fundamental lattice is the old fundamental lattice rescaled by the inverse
scale; consequently norm groups and weights are multiplied by the inverse
square of that scale.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

@[simp]
theorem reverseDual_fundamentalScaleOrder
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.fundamentalScaleOrder i =
      -J.fundamentalScaleOrder (Fin.rev i) := by
  simp [fundamentalScaleOrder]

/-- Uniformizer form of the fundamental-lattice identity in 93:24. -/
theorem reverseDual_fundamentalLattice_uniformizer
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.fundamentalLattice i =
      Lattice.rescale
        (Lattice.scaleTruncationUnit (K := K)
          (-J.fundamentalScaleOrder (Fin.rev i)))
        (J.fundamentalLattice (Fin.rev i)) := by
  unfold fundamentalLattice
  rw [reverseDual_fundamentalScaleOrder]
  exact Lattice.scaleTruncation_dual_neg q L
    (J.fundamentalScaleOrder (Fin.rev i))

/-- Scale-generator form of the fundamental-lattice identity in 93:24. -/
theorem reverseDual_fundamentalLattice
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.fundamentalLattice i =
      Lattice.rescale (J.scaleGenerator (Fin.rev i))⁻¹
        (J.fundamentalLattice (Fin.rev i)) := by
  rw [J.reverseDual_fundamentalLattice_uniformizer i]
  apply Lattice.rescale_eq_of_principalIdeal_eq
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2
  simp [Lattice.scaleTruncationUnit, fundamentalScaleOrder]

/-- Membership form of the reverse-dual fundamental norm-group formula.
The new group is `s⁻² g` at the index corresponding to the old scale `s`. -/
theorem mem_reverseDual_fundamentalNormGroup_iff
    (J : JordanDecomposition q L t) (i : Fin t) (z : K) :
    z ∈ J.reverseDual.fundamentalNormGroup i ↔
      ((J.scaleGenerator (Fin.rev i) ^ 2 : Kˣ) : K) * z ∈
        J.fundamentalNormGroup (Fin.rev i) := by
  let A : Lattice K V := J.fundamentalLattice (Fin.rev i)
  let s : Kˣ := J.scaleGenerator (Fin.rev i)
  let c : Kˣ := s⁻¹
  let f := Lattice.scalarMultiplicationRescaleLatticeIsometry q A c
  change z ∈ Lattice.normGroupSet q
      (J.reverseDual.fundamentalLattice i) ↔
    ((s ^ 2 : Kˣ) : K) * z ∈ Lattice.normGroupSet q A
  rw [J.reverseDual_fundamentalLattice i]
  change z ∈ Lattice.normGroupSet q (Lattice.rescale c A) ↔ _
  rw [Lattice.normGroupSet_eq_of_latticeIsometry f,
    Lattice.mem_normGroupSet_rescaleQuadraticUnit_iff]
  have hc : (c ^ 2)⁻¹ = s ^ 2 := by
    dsimp only [c]
    group
  rw [hc]

/-- The selected reverse-dual norm generator has order `U - 2S`. -/
theorem reverseDual_fundamentalNormGenerator_order
    (J : JordanDecomposition q L t) (i : Fin t) :
    ordUnit K (J.reverseDual.fundamentalNormGenerator i) =
      -2 * J.fundamentalScaleOrder (Fin.rev i) +
        ordUnit K (J.fundamentalNormGenerator (Fin.rev i)) := by
  let A : Lattice K V := J.fundamentalLattice (Fin.rev i)
  let s : Kˣ := J.scaleGenerator (Fin.rev i)
  let c : Kˣ := s⁻¹
  have hpos : 0 < Module.finrank K V :=
    J.ambient_finrank_pos_of_index (Fin.rev i)
  have hnew := J.reverseDual.fundamentalNormGenerator_spec i
  have hold := J.fundamentalNormGenerator_spec (Fin.rev i)
  have hscaled : Lattice.normIdeal q (Lattice.rescale c A) =
      Lattice.principalIdeal (K := K)
        ((c ^ 2 * J.fundamentalNormGenerator (Fin.rev i) : Kˣ) : K) :=
    Lattice.normIdeal_rescale_eq_principal_of_finrank_pos hpos c
      (J.fundamentalNormGenerator (Fin.rev i)) hold.2
  have hnew' : Lattice.normIdeal q (Lattice.rescale c A) =
      Lattice.principalIdeal (K := K)
        (J.reverseDual.fundamentalNormGenerator i : K) := by
    rw [← J.reverseDual_fundamentalLattice i]
    exact hnew.2
  have hord := (Lattice.principalIdeal_eq_iff_ordUnit_eq
    (J.reverseDual.fundamentalNormGenerator i)
    (c ^ 2 * J.fundamentalNormGenerator (Fin.rev i))).1
      (hnew'.symm.trans hscaled)
  rw [ordUnit_mul, ordUnit_pow] at hord
  dsimp only [c, s, A] at hord ⊢
  rw [ordUnit_inv] at hord
  unfold fundamentalScaleOrder
  omega

/-- The reverse-dual fundamental weight order is `W - 2S`. -/
theorem reverseDual_fundamentalWeightOrder
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.reverseDual.fundamentalWeightOrder i =
      -2 * J.fundamentalScaleOrder (Fin.rev i) +
        J.fundamentalWeightOrder (Fin.rev i) := by
  let A : Lattice K V := J.fundamentalLattice (Fin.rev i)
  let s : Kˣ := J.scaleGenerator (Fin.rev i)
  have hpos : 0 < Module.finrank K V :=
    J.ambient_finrank_pos_of_index (Fin.rev i)
  change Lattice.weightIdealOrder q
      (J.reverseDual.fundamentalLattice i) =
    -2 * ordUnit K s + Lattice.weightIdealOrder q A
  rw [J.reverseDual_fundamentalLattice i]
  change Lattice.weightIdealOrder q (Lattice.rescale s⁻¹ A) = _
  rw [Lattice.weightIdealOrder_rescaleLattice q A s⁻¹ hpos,
    ordUnit_inv]
  ring

end Lattice.JordanDecomposition

end Bong
