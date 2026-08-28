/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328AdjunctionAmbient
import Bong.Lattice.Omeara9328FirstBoundaryDispatcher
import Bong.Lattice.Omeara9328RankFourCancellation
import Bong.Lattice.Omeara9328StabilizationConditions
import Bong.Lattice.OmearaSaturationTheorem

/-!
# Scale control after O'Meara 93:28, Step 8

After Step 8, simultaneous stabilization, saturation, common adjunction and
rank-four reduction all preserve the displayed scale orders.  These lemmas
package that chain without unfolding the large dependent constructions in
the scale-spread recursion.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]

/-- Rank-four residualization of a common adjunction to a stabilized
Step-8 splitting has the original raw Step-8 scale orders. -/
theorem Omeara9328RankFourReductionSystem.sourceScaleOrder_eq_of_commonStable
    {X : Type u} [AddCommGroup X] [Module K X]
    {Y : Type u} [AddCommGroup Y] [Module K Y]
    {Z : Type u} [AddCommGroup Z] [Module K Z]
    {e : QuadraticSpace K X} {p : QuadraticSpace K Y}
    {z : QuadraticSpace K Z}
    {N : Lattice K X} {P₀ : Lattice K Y} {T₀ : Lattice K Z}
    {m : Nat} {EJ : JordanDecomposition e N (m + 2)}
    {P : JordanDecomposition p P₀ (m + 2)}
    (FPJ : SameFundamentalType P EJ.saturationStableJordan)
    (hP : P.IsSaturated)
    {T : JordanDecomposition z T₀ (m + 2)}
    (S : Omeara9328RankFourReductionSystem
      (P.commonAdjunctionJordan EJ.saturationStableJordan FPJ hP) T)
    (i : Fin (m + 2)) :
    ordUnit K (S.sourceJordan.scaleGenerator i) =
      ordUnit K (EJ.scaleGenerator i) := by
  calc
    ordUnit K (S.sourceJordan.scaleGenerator i) =
        ordUnit K ((P.commonAdjunctionJordan EJ.saturationStableJordan
          FPJ hP).scaleGenerator i) :=
      congrArg (ordUnit K) (S.sourceJordan_scaleGenerator i)
    _ = ordUnit K (P.scaleGenerator i) :=
      congrArg (ordUnit K)
        (P.commonAdjunctionJordan_scaleGenerator
          EJ.saturationStableJordan FPJ hP i)
    _ = ordUnit K (EJ.saturationStableJordan.scaleGenerator i) :=
      (FPJ.scaleGenerator_order_eq_sameIndex i).symm
    _ = ordUnit K (EJ.scaleGenerator i) :=
      congrArg (ordUnit K) (EJ.saturationStableJordan_scaleGenerator i)

/-- If the raw Step-8 splitting has first scale gap one, so does the
rank-four residual system obtained after the common saturated adjunction. -/
theorem Omeara9328RankFourReductionSystem.relativeScaleOrder_eq_one_of_commonStable
    {X : Type u} [AddCommGroup X] [Module K X]
    {Y : Type u} [AddCommGroup Y] [Module K Y]
    {Z : Type u} [AddCommGroup Z] [Module K Z]
    {e : QuadraticSpace K X} {p : QuadraticSpace K Y}
    {z : QuadraticSpace K Z}
    {N : Lattice K X} {P₀ : Lattice K Y} {T₀ : Lattice K Z}
    {m : Nat} {EJ : JordanDecomposition e N (m + 2)}
    {P : JordanDecomposition p P₀ (m + 2)}
    (FPJ : SameFundamentalType P EJ.saturationStableJordan)
    (hP : P.IsSaturated)
    {T : JordanDecomposition z T₀ (m + 2)}
    (S : Omeara9328RankFourReductionSystem
      (P.commonAdjunctionJordan EJ.saturationStableJordan FPJ hP) T)
    (hfirst : EJ.fundamentalScaleOrder 1 -
      EJ.fundamentalScaleOrder 0 = 1) :
    ordUnit K S.relativeSecondScale = 1 := by
  calc
    ordUnit K S.relativeSecondScale =
        S.sourceJordan.fundamentalScaleOrder 1 -
          S.sourceJordan.fundamentalScaleOrder 0 :=
      S.relativeSecondScale_order
    _ = EJ.fundamentalScaleOrder 1 - EJ.fundamentalScaleOrder 0 := by
      unfold fundamentalScaleOrder
      exact congrArg₂ (fun a b : Int ↦ a - b)
        (S.sourceScaleOrder_eq_of_commonStable FPJ hP 1)
        (S.sourceScaleOrder_eq_of_commonStable FPJ hP 0)
    _ = 1 := hfirst

/-- Removing the aligned head after the common stabilized rank-four
reduction has the same scale spread as removing the head of the raw Step-8
splitting. -/
theorem Omeara9328RankFourReductionSystem.tail_scaleSpread_eq_of_commonStable
    {X : Type u} [AddCommGroup X] [Module K X]
    {Y : Type u} [AddCommGroup Y] [Module K Y]
    {Z : Type u} [AddCommGroup Z] [Module K Z]
    {e : QuadraticSpace K X} {p : QuadraticSpace K Y}
    {z : QuadraticSpace K Z}
    {N : Lattice K X} {P₀ : Lattice K Y} {T₀ : Lattice K Z}
    {m : Nat} {EJ : JordanDecomposition e N (m + 2)}
    {P : JordanDecomposition p P₀ (m + 2)}
    (FPJ : SameFundamentalType P EJ.saturationStableJordan)
    (hP : P.IsSaturated)
    {T : JordanDecomposition z T₀ (m + 2)}
    (S : Omeara9328RankFourReductionSystem
      (P.commonAdjunctionJordan EJ.saturationStableJordan FPJ hP) T) :
    S.sourceJordan.tail.scaleSpread = EJ.tail.scaleSpread := by
  apply scaleSpread_eq_of_scaleGenerator_order_eq EJ.tail S.sourceJordan.tail
  intro i
  simp only [tail_scaleGenerator]
  exact S.sourceScaleOrder_eq_of_commonStable FPJ hP i.succ

end Lattice.JordanDecomposition

end Bong
