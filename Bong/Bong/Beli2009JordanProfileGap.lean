/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanProfileBoundary

/-!
# Boundary gaps for arbitrary Jordan profiles

The endpoint calculation for a Jordan decomposition adapted to a good BONG
was proved in `Beli2009JordanBoundaryOdd`.  Here it is transported across
O'Meara's intrinsic fundamental type to an arbitrary profiled Jordan
decomposition.  This removes the adapted-endpoint hypotheses from the form
used in Beli (2019), Section 5.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

/-- A global coordinate which is the last local coordinate of component
`z` is exactly the boundary index attached to `z`. -/
theorem boundaryIndex_eq_of_indexEquiv_last
    {m t : Nat} {a : GoodBONG q L (m + 1)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (g : Fin m) (z : Fin t)
    (hcomponent : (P.indexEquiv g.castSucc).1 =
      Lattice.JordanDecomposition.boundaryLeftIndex z)
    (hlast : (P.indexEquiv g.castSucc).2.val + 1 =
      J.componentRank (P.indexEquiv g.castSucc).1) :
    P.boundaryIndex z = g := by
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let last : Fin (J.componentRank li) :=
    ⟨J.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  have hlast' : (P.indexEquiv g.castSucc).2.val + 1 =
      J.componentRank li := by
    simpa only [li, hcomponent] using hlast
  have hpair : P.indexEquiv g.castSucc = ⟨li, last⟩ := by
    apply Sigma.ext
    · exact hcomponent
    · exact (Fin.heq_ext_iff
        (congrArg J.componentRank hcomponent)).2 (by
          dsimp only [last]
          omega)
  have hglobal : P.indexEquiv.symm ⟨li, last⟩ = g.castSucc := by
    rw [← hpair, P.indexEquiv.symm_apply_apply]
  apply Fin.ext
  unfold boundaryIndex
  dsimp only
  change (P.indexEquiv.symm ⟨li, last⟩).val = g.val
  rw [hglobal]
  rfl

/-- At every boundary of an arbitrary Jordan profile, the good-BONG order
gap is the sum of the two intrinsic norm orders minus twice the left scale.
This is the profile-invariant form of the endpoint calculation used in Beli
(2009), Lemma 2.16(ii). -/
theorem orderGap_boundaryIndex_eq_boundaryNormOrderSum_sub_twoScale
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    a.orderGap (P.boundaryIndex z) =
      J.boundaryNormOrderSum z -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hs := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have ht := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hRank] at hs
    omega
  have hraw := Ps.orderGap_boundaryIndex z
    (S.sourceTerminalValue_isNormGeneratorValue hcount
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (S.sourceNormGenerator_order_eq_fundamental hcount
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
  calc
    a.orderGap (P.boundaryIndex z) =
        a.orderGap (Ps.boundaryIndex z) := by rw [hboundary]
    _ = Js.boundaryNormOrderSum z -
        2 * Js.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) := hraw
    _ = J.boundaryNormOrderSum z -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
      rw [Fs.boundaryNormOrderSum_eq z, Fs.boundaryScaleOrder_eq z]

end BONG.JordanOrderProfileWitness

end Bong
