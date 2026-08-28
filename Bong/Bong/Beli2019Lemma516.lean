/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordan
import Bong.Lattice.OmearaModularDecompositionTruncation

/-!
# Beli (2019), Lemma 5.16

For the index-uniformizer inclusion furnished by Lemma 5.1, every scale
truncation at or below the scale of the enlarged selected component contains
the corresponding truncation of the smaller lattice.  The proof uses the
unsorted modular decompositions: their common-complement components agree,
and at the selected component both truncation factors are one.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.OrthogonalDecomposition

/-- A modular truncation factor is one when the target scale is no larger
than the component scale. -/
theorem modularScaleTruncationFactor_eq_one_of_le
    {t : Nat} (s : Fin t → Kˣ) (r : Int) (i : Fin t)
    (h : r ≤ ordUnit K (s i)) :
    modularScaleTruncationFactor s r i = 1 := by
  unfold modularScaleTruncationFactor positivePartUnit
  have hnot : ¬0 < ordUnit K
      (scaleTruncationUnit (K := K) r * (s i)⁻¹) := by
    rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit]
    change ¬0 < r - ordUnit K (s i)
    omega
  rw [if_neg hnot]

end Lattice.OrthogonalDecomposition

namespace Lattice.QuadraticSublattice

@[simp]
theorem rescaleLattice_one_ambientSubmodule (C : QuadraticSublattice q) :
    (C.rescaleLattice 1).ambientSubmodule = C.ambientSubmodule := by
  unfold rescaleLattice ambientSubmodule
  rw [Lattice.rescale_one]

end Lattice.QuadraticSublattice

namespace Lattice.Beli2019Lemma51Data

@[simp]
theorem smallModularDecomposition_component_zero
    (D : Beli2019Lemma51Data q M N) :
    D.smallModularDecomposition.component 0 = D.input.block.component := by
  rfl

@[simp]
theorem largeModularDecomposition_component_zero
    (D : Beli2019Lemma51Data q M N) :
    D.largeModularDecomposition.component 0 = D.input.enlargedComponent := by
  simpa only [largeModularDecomposition,
    OrthogonalDecomposition.prependNestedOfEq_zero] using
      D.input.largeSplitting_component_zero

@[simp]
theorem smallModularDecomposition_component_succ
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallModularDecomposition.component i.succ =
      D.complement.liftNested (D.complementStrictWeak.component i) := by
  rfl

@[simp]
theorem largeModularDecomposition_component_succ
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeModularDecomposition.component i.succ =
      D.complement.liftNested (D.complementStrictWeak.component i) := by
  simpa only [largeModularDecomposition,
    OrthogonalDecomposition.prependNestedOfEq_succ]

@[simp]
theorem smallModularDecomposition_scaleGenerator_zero
    (D : Beli2019Lemma51Data q M N) :
    D.smallModularDecomposition.scaleGenerator 0 =
      D.input.block.scaleGenerator := by
  rfl

@[simp]
theorem largeModularDecomposition_scaleGenerator_zero
    (D : Beli2019Lemma51Data q M N) :
    D.largeModularDecomposition.scaleGenerator 0 =
      D.input.block.enlargedScaleGenerator := by
  rfl

@[simp]
theorem smallModularDecomposition_scaleGenerator_succ
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallModularDecomposition.scaleGenerator i.succ =
      D.complementStrictWeak.scaleGenerator i := by
  rfl

@[simp]
theorem largeModularDecomposition_scaleGenerator_succ
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeModularDecomposition.scaleGenerator i.succ =
      D.complementStrictWeak.scaleGenerator i := by
  rfl

/-- The enlarged selected component has strictly smaller modular scale than
the selected component of the smaller lattice. -/
theorem enlargedScaleOrder_lt_smallScaleOrder
    (D : Beli2019Lemma51Data q M N) :
    ordUnit K D.input.block.enlargedScaleGenerator <
      ordUnit K D.input.block.scaleGenerator := by
  rcases D.input.block.componentRank_and_enlargedScaleOrder with h | h
  · omega
  · omega

/-- Beli (2019), Lemma 5.16.  In the repository's inclusion orientation this
says `N^s ≤ M^s`, i.e. the paper's `M^s \supset N^s`. -/
theorem scaleTruncation_small_le_large
    (D : Beli2019Lemma51Data q M N) (s : Int)
    (hs : s ≤ ordUnit K D.input.block.enlargedScaleGenerator) :
    scaleTruncation q N s ≤ scaleTruncation q M s := by
  let S := D.smallModularDecomposition
  let T := D.largeModularDecomposition
  let fS := OrthogonalDecomposition.modularScaleTruncationFactor
    S.scaleGenerator s
  let fT := OrthogonalDecomposition.modularScaleTruncationFactor
    T.scaleGenerator s
  have hsSmall : s ≤ ordUnit K D.input.block.scaleGenerator :=
    hs.trans (D.enlargedScaleOrder_lt_smallScaleOrder.le)
  have hfS : fS 0 = 1 := by
    apply OrthogonalDecomposition.modularScaleTruncationFactor_eq_one_of_le
    simpa only [fS, S, D.smallModularDecomposition_scaleGenerator_zero]
      using hsSmall
  have hfT : fT 0 = 1 := by
    apply OrthogonalDecomposition.modularScaleTruncationFactor_eq_one_of_le
    simpa only [fT, T, D.largeModularDecomposition_scaleGenerator_zero]
      using hs
  rw [S.toOrthogonalDecomposition.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      S.scaleGenerator S.modular s,
    T.toOrthogonalDecomposition.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      T.scaleGenerator T.modular s]
  change
    (S.toOrthogonalDecomposition.componentwiseRescaleLattice fS).toSubmodule ≤
      (T.toOrthogonalDecomposition.componentwiseRescaleLattice fT).toSubmodule
  rw [← (S.toOrthogonalDecomposition.componentwiseRescale fS).sum_eq,
    ← (T.toOrthogonalDecomposition.componentwiseRescale fT).sum_eq]
  apply iSup_le
  intro i
  apply le_trans ?_ (le_iSup
    (fun j ↦ ((T.toOrthogonalDecomposition.componentwiseRescale fT).component j).ambientSubmodule)
    i)
  cases i using Fin.cases with
  | zero =>
      rw [OrthogonalDecomposition.componentwiseRescale_component,
        OrthogonalDecomposition.componentwiseRescale_component, hfS, hfT,
        QuadraticSublattice.rescaleLattice_one_ambientSubmodule,
        QuadraticSublattice.rescaleLattice_one_ambientSubmodule]
      simpa only [S, T, D.smallModularDecomposition_component_zero,
        D.largeModularDecomposition_component_zero,
        Beli2019Lemma51InputData.enlargedComponent] using
        (QuadraticSublattice.ambientSubmodule_le_adjoinVector
          D.input.block.component D.input.enlargedVector)
  | succ i =>
      have hfactor : fS i.succ = fT i.succ := by
        rfl
      rw [OrthogonalDecomposition.componentwiseRescale_component,
        OrthogonalDecomposition.componentwiseRescale_component, hfactor]
      have hcomponent : S.component i.succ = T.component i.succ := by
        simp only [S, T, D.smallModularDecomposition_component_succ,
          D.largeModularDecomposition_component_succ]
      rw [hcomponent]

end Lattice.Beli2019Lemma51Data

end Bong
