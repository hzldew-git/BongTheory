/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationTheorem
import Bong.Lattice.OmearaFundamentalTypeAlgebra

/-!
# Fundamental type of O'Meara's saturated splitting

The saturated splitting constructed in 93:21 has the same component ranks,
scale sequence, and intrinsic fundamental norm groups as the input
splitting.  Thus paired saturation preserves complete fundamental type.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The saturated splitting constructed by 93:21 has the same complete
fundamental type as the original nontrivial splitting. -/
noncomputable def SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThree
    (J : JordanDecomposition q L (n + 2))
    (hrank : ∀ i, 3 ≤ J.componentRank i) :
    SameFundamentalType J
      (J.saturatedJordanOfComponentRanksAtLeastThree hrank) where
  indexEquiv := Equiv.refl _
  index_val := fun _ ↦ rfl
  componentRank_eq := by
    intro i
    exact J.saturatedJordanOfComponentRanksAtLeastThree_componentRank
      hrank i
  scaleOrder_eq := by
    intro i
    unfold fundamentalScaleOrder
    simpa using congrArg (ordUnit K)
      (J.saturatedJordanOfComponentRanksAtLeastThree_scaleGenerator hrank i)
  normGroup_eq := by
    intro i
    unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
    rfl

/-- Uniform nonempty version, including the one-component case. -/
noncomputable def SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThreeNonempty
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (hrank : ∀ i, 3 ≤ J.componentRank i) :
    SameFundamentalType J
      (J.saturatedJordanOfComponentRanksAtLeastThreeNonempty hrank) := by
  cases m with
  | zero => exact SameFundamentalType.refl J
  | succ n =>
      exact SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThree
        J hrank

/-- Saturating both sides of an aligned pair preserves their complete
fundamental type. -/
noncomputable def SameFundamentalType.pairedSaturation
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (hrankJ : ∀ i, 3 ≤ J.componentRank i)
    (hrankH : ∀ i, 3 ≤ H.componentRank i) :
    SameFundamentalType
      (J.saturatedJordanOfComponentRanksAtLeastThree hrankJ)
      (H.saturatedJordanOfComponentRanksAtLeastThree hrankH) :=
  (SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThree
      J hrankJ).symm.trans <|
    F.trans <|
      SameFundamentalType.saturatedJordanOfComponentRanksAtLeastThree
        H hrankH

end Lattice.JordanDecomposition

end Bong
