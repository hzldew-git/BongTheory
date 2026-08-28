/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveUnaryProper

/-!
# Beli (2019), Section 5: the improper unary exceptional interval

This file treats case 4 following Lemma 5.13.  Its geometric input is the
literal equality of the two fundamental lattices at the intermediate scale.
In rank one the enlarged selected block is `π⁻¹ J`; hence the scale
truncation at the intervening scale multiplies it back by `π`.  Every other
component belongs to the common complement and has the same truncation
factor on both sides.  This proves, without a new law interface, the paper's
display

`M^(p^(r-1)) = K^(p^(r-1)) ⊥ π J' = K^(p^(r-1)) ⊥ J = N^(p^(r-1))`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51BlockData

/-- A rank-one block is necessarily the unary constructor, so adjoining
the inverse-uniformizer multiple of its distinguished vector is exactly a
global inverse-uniformizer rescaling. -/
theorem enlargedLattice_eq_rescale_inv_of_rank_one
    {L : Lattice K V} {x : V}
    (B : Beli2019Lemma51BlockData q L x)
    (hfin : finrank K B.component.carrier = 1) :
    B.enlargedLattice =
      Lattice.rescale (uniformizerUnit K)⁻¹ B.component.lattice := by
  cases B with
  | unary z hz hcongruent hanisotropic hpairing =>
      exact enlargedLattice_eq_rescale_of_unary
        z hz hcongruent hanisotropic hpairing
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      have hactual :
          finrank K (BONG.binaryPairSpan (K := K) z y) = 2 := by
        simpa using Module.finrank_eq_card_basis
          (BONG.binaryPairBasis (K := K) z y
            (binaryPair_linearIndependent_of_left_strict hzy hleft hright))
      change finrank K (BONG.binaryPairSpan (K := K) z y) = 1 at hfin
      omega

end Lattice.Beli2019Lemma51BlockData

namespace Lattice.Beli2019Lemma51Data

/-- The enlarged selected component of rank one is `π⁻¹` times the
original selected component. -/
theorem enlargedComponent_lattice_eq_rescale_inv_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    D.input.enlargedComponent.lattice =
      Lattice.rescale (uniformizerUnit K)⁻¹
        D.input.block.component.lattice := by
  rw [D.input.enlargedComponent_lattice_eq_block]
  exact D.input.block.enlargedLattice_eq_rescale_inv_of_rank_one hfin

/-- Case 4 following Lemma 5.13: at the unique scale strictly between the
two unary selected scales, the source and target scale truncations are
literally the same lattice. -/
theorem unaryShift_intermediate_scaleTruncation_eq
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    Lattice.scaleTruncation q M
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      Lattice.scaleTruncation q N
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by
  let target := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let S := D.smallModularDecomposition
  let T := D.largeModularDecomposition
  let fS := Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
    S.scaleGenerator target
  let fT := Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
    T.scaleGenerator target
  have hsmallScale : target ≤ ordUnit K D.input.block.scaleGenerator := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · dsimp only [target]
      omega
    · omega
  have hfS : fS 0 = 1 := by
    apply Lattice.OrthogonalDecomposition.modularScaleTruncationFactor_eq_one_of_le
    simpa only [fS, S, D.smallModularDecomposition_scaleGenerator_zero]
      using hsmallScale
  have hfTOrder : ordUnit K (fT 0) = 1 := by
    rw [Lattice.OrthogonalDecomposition.ordUnit_modularScaleTruncationFactor]
    simp only [T, D.largeModularDecomposition_scaleGenerator_zero]
    dsimp only [target]
    omega
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  have hselectedLattice :
      Lattice.rescale (fT 0) D.input.enlargedComponent.lattice =
        D.input.block.component.lattice := by
    change Lattice.rescale (fT 0) D.input.block.enlargedLattice =
      D.input.block.component.lattice
    rw [D.input.block.enlargedLattice_eq_rescale_inv_of_rank_one hfin,
      ← Lattice.rescale_mul]
    apply Lattice.rescale_eq_self_of_isValuationUnit
    rw [Dyadic.isValuationUnit_iff_ordUnit_eq_zero,
      ordUnit_mul, ordUnit_inv, hfTOrder, hpi]
    omega
  rw [S.toOrthogonalDecomposition.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      S.scaleGenerator S.modular target,
    T.toOrthogonalDecomposition.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      T.scaleGenerator T.modular target]
  apply Lattice.ext
  change
    (T.toOrthogonalDecomposition.componentwiseRescaleLattice fT).toSubmodule =
      (S.toOrthogonalDecomposition.componentwiseRescaleLattice fS).toSubmodule
  rw [← (T.toOrthogonalDecomposition.componentwiseRescale fT).sum_eq,
    ← (S.toOrthogonalDecomposition.componentwiseRescale fS).sum_eq]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero =>
      rw [Lattice.OrthogonalDecomposition.componentwiseRescale_component,
        Lattice.OrthogonalDecomposition.componentwiseRescale_component,
        hfS]
      change
        (D.input.enlargedComponent.rescaleLattice (fT 0)).ambientSubmodule =
          (D.input.block.component.rescaleLattice 1).ambientSubmodule
      unfold Lattice.QuadraticSublattice.rescaleLattice
        Lattice.QuadraticSublattice.ambientSubmodule
      rw [hselectedLattice, Lattice.rescale_one]
      rfl
  | succ i =>
      have hfactor : fT i.succ = fS i.succ := by rfl
      rw [Lattice.OrthogonalDecomposition.componentwiseRescale_component,
        Lattice.OrthogonalDecomposition.componentwiseRescale_component,
        hfactor]
      have hcomponent : T.component i.succ = S.component i.succ := by
        simp only [T, S, D.largeModularDecomposition_component_succ,
          D.smallModularDecomposition_component_succ]
      rw [hcomponent]

/-- The common intermediate fundamental lattice has the same weight ideal
on the two sides. -/
theorem unaryShift_intermediate_weightIdealOrder_eq
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q M
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) =
      Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q N
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) := by
  rw [D.unaryShift_intermediate_scaleTruncation_eq hfin i₀ hi₀]

/-- The literal equality of the intermediate fundamental lattices lets us
choose one scalar norm generator on both sides, including all endpoint
collision patterns. -/
theorem exists_unaryShift_intermediate_commonNormGenerator
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    ∃ A : Kˣ,
      Lattice.IsNormGeneratorValue q
          (Lattice.scaleTruncation q M
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) A ∧
      Lattice.IsNormGeneratorValue q
          (Lattice.scaleTruncation q N
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) A := by
  letI : Module.Finite K V := M.moduleFinite
  let target := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  have hpos : 0 < finrank K V := by
    have hle := Submodule.finrank_le D.input.block.component.carrier
    omega
  obtain ⟨x, hx, hxne⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos q
      (Lattice.scaleTruncation q N target) hpos
  let A : Kˣ := Units.mk0 (q.quadratic x) hxne
  have hsmall : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N target) A :=
    hx.isNormGeneratorValue hxne
  have heq := D.unaryShift_intermediate_scaleTruncation_eq hfin i₀ hi₀
  refine ⟨A, ?_, hsmall⟩
  simpa only [target, heq] using hsmall

/-! ## Exact weak-profile coordinates in the exceptional block -/

/-- The `j`-th coordinate of the intermediate component on the large side
occurs one place after the exceptional interval start. -/
theorem weakUnaryShift_largeCommon_indexEquiv
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (j : Nat)
    (hj : j < finrank K (D.complementStrictWeak.component i₀).carrier) :
    (D.largeWeakProfileWitness a).indexEquiv
        ⟨D.largeSelectedStart + (j + 1), by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart +
              (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
            at hbound
          omega⟩ =
      ⟨D.smallSelectedPosition,
        ⟨j, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          exact hj⟩⟩ := by
  let w := D.largeWeakProfileWitness a
  let ell : Fin
      (finrank K (D.largeAlmostJordan.component
        D.smallSelectedPosition).carrier) :=
    ⟨j, by
      rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
        hfin i₀ hi₀]
      exact hj⟩
  let I : Fin n := ⟨D.largeSelectedStart + (j + 1), by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
      at hbound
    omega⟩
  have hprefix := D.weakUnaryShift_largePrefixRank_at_smallSelected
    hfin i₀ hi₀
  have hI : I = w.indexEquiv.symm ⟨D.smallSelectedPosition, ell⟩ := by
    apply Fin.ext
    have hinverse := w.inverse_index_val D.smallSelectedPosition ell
    dsimp only [I, ell, Fin.val_mk]
    rw [hinverse, hprefix]
    dsimp only [largeSelectedStart, ell, Fin.val_mk]
    omega
  change w.indexEquiv I = ⟨D.smallSelectedPosition, ell⟩
  rw [hI, w.indexEquiv.apply_symm_apply]

/-- The `j`-th coordinate of the intermediate component on the small side
starts at the exceptional interval start itself. -/
theorem weakUnaryShift_smallCommon_indexEquiv
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (j : Nat)
    (hj : j < finrank K (D.complementStrictWeak.component i₀).carrier) :
    (D.smallWeakProfileWitness b).indexEquiv
        ⟨D.largeSelectedStart + j, by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart +
              (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
            at hbound
          omega⟩ =
      ⟨D.largeSelectedPosition,
        ⟨j, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact hj⟩⟩ := by
  let w := D.smallWeakProfileWitness b
  let ell : Fin
      (finrank K (D.smallAlmostJordan.component
        D.largeSelectedPosition).carrier) :=
    ⟨j, by
      rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
        hfin i₀ hi₀]
      exact hj⟩
  let I : Fin n := ⟨D.largeSelectedStart + j, by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
      at hbound
    omega⟩
  have hprefix := D.weakUnaryShift_prefixRank_eq hfin i₀ hi₀
  have hI : I = w.indexEquiv.symm ⟨D.largeSelectedPosition, ell⟩ := by
    apply Fin.ext
    have hinverse := w.inverse_index_val D.largeSelectedPosition ell
    dsimp only [I, ell, Fin.val_mk]
    rw [hinverse, ← hprefix]
    dsimp only [largeSelectedStart, ell, Fin.val_mk]
  change w.indexEquiv I = ⟨D.largeSelectedPosition, ell⟩
  rw [hI, w.indexEquiv.apply_symm_apply]

end Lattice.Beli2019Lemma51Data

end Bong
