/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualInvariants
import Bong.Lattice.NormGroupValuationUnitSquare
import Bong.Lattice.OmearaSaturatedJordan
import Bong.Lattice.OmearaComponentwiseFundamentalTransfer

/-!
# Saturation and fundamental type under reverse duality

O'Meara 93:24 reverses a Jordan chain after taking integral duals.  This
operation preserves saturation.  It also preserves equality of fundamental
type: the inverse-square factors attached to two chosen scale generators can
differ by a valuation-unit square, which does not change a norm group.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

namespace IsSaturated

/-- A saturated Jordan decomposition remains saturated after reversing the
chain and taking componentwise integral duals. -/
theorem reverseDual
    {J : JordanDecomposition q L t} (hJ : J.IsSaturated) :
    J.reverseDual.IsSaturated := by
  intro i
  change Lattice.normGroupSet (J.component (Fin.rev i)).space
      (Lattice.dualLattice (J.component (Fin.rev i)).space
        (J.component (Fin.rev i)).lattice) =
    J.reverseDual.fundamentalNormGroup i
  rw [J.modular (Fin.rev i)]
  change Lattice.normGroupSet (J.component (Fin.rev i)).space
      (Lattice.rescale (J.scaleGenerator (Fin.rev i))⁻¹
        (J.component (Fin.rev i)).lattice) =
    Lattice.normGroupSet q (J.reverseDual.fundamentalLattice i)
  rw [J.reverseDual_fundamentalLattice i]
  exact Lattice.normGroupSet_rescaleLattice_eq_of_eq
    (J.scaleGenerator (Fin.rev i))⁻¹ (hJ (Fin.rev i))

end IsSaturated

namespace SameFundamentalType

/-- Equality of O'Meara fundamental type is preserved by reverse duality. -/
noncomputable def reverseDual
    {J : JordanDecomposition q L t} {H : JordanDecomposition r M t}
    (F : SameFundamentalType J H) :
    SameFundamentalType J.reverseDual H.reverseDual where
  indexEquiv := Equiv.refl (Fin t)
  index_val := fun i => rfl
  componentRank_eq := by
    intro i
    simp only [Equiv.refl_apply, reverseDual_componentRank]
    have h := F.componentRank_eq (Fin.rev i)
    rw [F.indexEquiv_apply_eq_self] at h
    exact h
  scaleOrder_eq := by
    intro i
    simp only [Equiv.refl_apply, reverseDual_fundamentalScaleOrder]
    have h := F.scaleOrder_eq (Fin.rev i)
    rw [F.indexEquiv_apply_eq_self] at h
    omega
  normGroup_eq := by
    intro i
    simp only [Equiv.refl_apply]
    have hgroup := F.normGroup_eq (Fin.rev i)
    rw [F.indexEquiv_apply_eq_self] at hgroup
    have hscale := F.scaleOrder_eq (Fin.rev i)
    rw [F.indexEquiv_apply_eq_self] at hscale
    ext z
    rw [H.mem_reverseDual_fundamentalNormGroup_iff,
      J.mem_reverseDual_fundamentalNormGroup_iff, hgroup]
    exact Lattice.sq_mul_mem_normGroupSet_iff_sq_mul_of_ordUnit_eq
      (H.scaleGenerator (Fin.rev i))
      (J.scaleGenerator (Fin.rev i)) hscale z

end SameFundamentalType

end Lattice.JordanDecomposition

end Bong
