/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanProfile
import Bong.Bong.Beli2019Lemma516
import Bong.Bong.Beli2019Lemma513Profiles
import Bong.Bong.Beli2019Lemma32ProfileSeeds
import Bong.Bong.JordanEffectiveNormGenerator
import Bong.Lattice.OrthogonalDecompositionPrefixComponentwise

/-!
# Common approximations in Beli (2019), Lemma 5.13

This file constructs the scalar approximations used in Lemma 5.13 from the
almost-Jordan decompositions of Section 5.  It begins with the aligned,
no-scale-collision branch.  The even seed is the determinant of the literal
common component prefix; the odd seed is supplied by an effective norm
generator of the relevant intrinsic scale truncation.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Away from the aligned selected position, the two almost-Jordan
components are literally the same lifted common-complement component. -/
theorem aligned_component_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p ≠ D.largeSelectedPosition) :
    D.largeAlmostJordan.component p = D.smallAlmostJordan.component p := by
  rcases D.largePosition_eq_selected_or_common p with hsel | ⟨c, hc⟩
  · exact (hp hsel).elim
  · subst p
    have hpositions := D.commonPositions_eq_of_selectedPositions_eq hselected c
    rw [D.largeAlmostJordan_component_common, ← hpositions,
      D.smallAlmostJordan_component_common]

/-- Aligned positions strictly before the selected block have the same
scale order. -/
theorem aligned_scaleOrder_eq_of_lt
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) := by
  rcases D.largePosition_eq_selected_or_common p with hposition | ⟨c, hposition⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hcommon := D.commonPositions_eq_of_selectedPositions_eq hselected c
    rw [D.largeAlmostJordan_scaleGenerator_common, ← hcommon,
      D.smallAlmostJordan_scaleGenerator_common]

/-- Before the exceptional rank-one transposition, the two almost-Jordan
families contain the same common component at the same numerical position.
-/
theorem unaryShift_component_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    D.largeAlmostJordan.component p = D.smallAlmostJordan.component p := by
  rcases D.largePosition_eq_selected_or_common p with
    hselected | ⟨c, hcommon⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hne : c ≠ i₀ := by
      intro h
      subst c
      have hright :=
        D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      have hrightVal := congrArg Fin.val hright
      change (D.largeCommonPosition i₀).val <
        D.largeSelectedPosition.val at hp
      omega
    have hpositions :=
      D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
    rw [D.largeAlmostJordan_component_common, ← hpositions,
      D.smallAlmostJordan_component_common]

/-- Before an aligned selected component, the two strict no-collision
prefix determinants differ by an actual square. -/
theorem exists_noCollision_prefixDeterminant_eq_mul_square
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hcomponents : ∀ j, j < p →
      D.largeAlmostJordan.component j = D.smallAlmostJordan.component j)
    (hpzero : p.val ≠ 0) :
    ∃ s : Kˣ,
      (D.smallNoCollisionJordan hsmall).prefixDeterminantUnit
          ⟨p.val - 1, by omega⟩ =
        (D.largeNoCollisionJordan hlarge).prefixDeterminantUnit
          ⟨p.val - 1, by omega⟩ * s ^ 2 := by
  let P := (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition
  let Q := (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition
  have hk : (p.val - 1) + 1 ≤ D.complementComponentCount + 1 := by omega
  have hcomponents : ∀ i : Fin ((p.val - 1) + 1),
      P.component (P.prefixIndexEquiv ((p.val - 1) + 1) hk i).1 =
        Q.component (Q.prefixIndexEquiv ((p.val - 1) + 1) hk i).1 := by
    intro i
    let jP := (P.prefixIndexEquiv ((p.val - 1) + 1) hk i).1
    let jQ := (Q.prefixIndexEquiv ((p.val - 1) + 1) hk i).1
    have hj : jP = jQ := by
      apply Fin.ext
      rw [P.prefixIndexEquiv_val, Q.prefixIndexEquiv_val]
    change P.component jP = Q.component jQ
    rw [hj]
    change D.largeAlmostJordan.component jQ =
      D.smallAlmostJordan.component jQ
    apply hcomponents jQ
    have hjlt : jQ.val < p.val := by
      change (Q.prefixIndexEquiv ((p.val - 1) + 1) hk i).1.val < p.val
      rw [Q.prefixIndexEquiv_val]
      exact i.isLt.trans_le (by omega)
    exact hjlt
  have hsquare :=
    P.exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry
      Q hk (fun i ↦ by
        rw [hcomponents i]
        exact Lattice.Isometry.refl _ _)
  simpa only [P, Q, Lattice.JordanDecomposition.prefixDeterminantUnit,
    show p.val - 1 + 1 = p.val by omega] using hsquare

/-- At a common component strictly before the selected component, the two
effective norm orders differ by zero, one, or two.  This remains valid at
the unique large-side scale collision: only a non-strict comparison with
the enlarged selected scale is needed. -/
theorem common_effectiveNormOrder_bounds
    (D : Beli2019Lemma51Data q M N)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    D.largeAlmostJordan.effectiveNormOrderAt p target ≤
        D.smallAlmostJordan.effectiveNormOrderAt p target ∧
      D.smallAlmostJordan.effectiveNormOrderAt p target ≤
        D.largeAlmostJordan.effectiveNormOrderAt p target + 2 := by
  dsimp only
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  have htargetLarge : target ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hp.le
    simpa only [target, D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have htargetSmall : target <
      ordUnit K D.input.block.scaleGenerator :=
    htargetLarge.trans_lt D.enlargedScaleOrder_lt_smallScaleOrder
  refine ⟨D.large_effectiveNormOrderAt_le_small_of_target_lt
      p p target htargetSmall, ?_⟩
  let e := D.largeToSmallPositionEquiv
  rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt,
    Lattice.WeakJordanDecomposition.effectiveNormOrderAt,
    ← JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e p p target]
  apply JordanProfileOrder.effectiveAt_le_add_of_pointwise
  intro j
  rcases D.largePosition_eq_selected_or_common j with hselected | ⟨c, hcommon⟩
  · subst j
    simpa only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
      largeToSmallPositionEquiv_selected,
      Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected,
      if_neg (not_lt_of_ge htargetLarge),
      if_neg (not_lt_of_ge htargetSmall.le)] using
        D.smallSelected_normOrder_le_largeSelected_add_two
  · subst j
    simp only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
      largeToSmallPositionEquiv_common,
      Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_common,
      D.common_normOrder_eq]
    omega

/-- Backwards-compatible no-collision specialization of
`common_effectiveNormOrder_bounds`. -/
theorem noCollision_common_effectiveNormOrder_bounds
    (D : Beli2019Lemma51Data q M N)
    (_hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    D.largeAlmostJordan.effectiveNormOrderAt p target ≤
        D.smallAlmostJordan.effectiveNormOrderAt p target ∧
      D.smallAlmostJordan.effectiveNormOrderAt p target ≤
        D.largeAlmostJordan.effectiveNormOrderAt p target + 2 :=
  D.common_effectiveNormOrder_bounds p hp

/-- If the two effective norm orders agree at an aligned common component,
the corresponding intrinsic scale truncations admit one literal scalar norm
generator. -/
theorem exists_noCollision_commonNormGenerator_of_effective_eq
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition)
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p))
    (heffective :
      D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) =
        D.smallAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p))) :
    ∃ A : Kˣ,
      Lattice.IsNormGeneratorValue q
          ((D.largeNoCollisionJordan hlarge).fundamentalLattice p) A ∧
        Lattice.IsNormGeneratorValue q
          ((D.smallNoCollisionJordan hsmall).fundamentalLattice p) A := by
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let largeJ := D.largeNoCollisionJordan hlarge
  let smallJ := D.smallNoCollisionJordan hsmall
  have htargetLarge : target <
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hstrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge hp
    simpa only [target, D.largeAlmostJordan_scaleGenerator_selected] using
      hstrict
  obtain ⟨j, hjmin, hsmallGenerator⟩ :=
    D.smallAlmostJordan.exists_adjustedNormGeneratorUnit_spec
      (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
      p target
  let A := D.smallAlmostJordan.adjustedNormGeneratorUnit
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall) target j
  have hnorm :
      Lattice.normIdeal q (Lattice.scaleTruncation q M target) =
        Lattice.normIdeal q (Lattice.scaleTruncation q N target) := by
    rw [largeJ.normIdeal_scaleTruncation_eq_powerIdeal p target,
      smallJ.normIdeal_scaleTruncation_eq_powerIdeal p target]
    change Lattice.powerIdeal (K := K)
        (D.largeAlmostJordan.effectiveNormOrderAt p target) =
      Lattice.powerIdeal (K := K)
        (D.smallAlmostJordan.effectiveNormOrderAt p target)
    rw [heffective]
  have hlargeGenerator : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q M target) A :=
    hsmallGenerator.of_le_of_normIdeal_eq
      (D.scaleTruncation_small_le_large target htargetLarge.le) hnorm
  refine ⟨A, ?_, ?_⟩
  · simpa only [largeJ, target,
      largeNoCollisionJordan,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder] using
        hlargeGenerator
  · change Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator p))) A
    rw [← hscale]
    exact hsmallGenerator

/-- If the effective norm on the smaller side is exactly two steps above
the effective norm on the larger side, the selected enlarged-component
generator and its square-uniformizer multiple generate the two intrinsic
fundamental norm ideals.  This is the `u_k` versus `π²u_k` branch in the
proof of Beli (2019), Lemma 5.13(i). -/
theorem noCollision_gapTwo_normGenerator_pair
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition)
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p))
    (heffective :
      D.smallAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) =
        D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2) :
    let A := D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition
    Lattice.IsNormGeneratorValue q
        ((D.largeNoCollisionJordan hlarge).fundamentalLattice p) A ∧
      Lattice.IsNormGeneratorValue q
        ((D.smallNoCollisionJordan hsmall).fundamentalLattice p)
        ((uniformizerUnit K) ^ 2 * A) := by
  dsimp only
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let largeJ := D.largeNoCollisionJordan hlarge
  let smallJ := D.smallNoCollisionJordan hsmall
  let A := D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition
  have htargetLarge : target <
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hstrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge hp
    simpa only [target, D.largeAlmostJordan_scaleGenerator_selected] using
      hstrict
  have htargetSmall : target <
      ordUnit K D.input.block.scaleGenerator :=
    htargetLarge.trans D.enlargedScaleOrder_lt_smallScaleOrder
  have hlt :
      D.largeAlmostJordan.effectiveNormOrderAt p target <
        D.smallAlmostJordan.effectiveNormOrderAt p target := by
    dsimp only [target] at heffective ⊢
    omega
  have hforce := D.large_effectiveNormOrderAt_eq_selected_of_lt
    p p target hlt
  have hlargeGenerator0 :=
    D.largeAlmostJordan.adjustedNormGeneratorUnit_spec
      (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
      p D.largeSelectedPosition target hforce.symm
  have hlargeGenerator : Lattice.IsNormGeneratorValue q
      (largeJ.fundamentalLattice p) A := by
    have htargetLarge' : target ≤ ordUnit K
        (D.largeAlmostJordan.scaleGenerator D.largeSelectedPosition) := by
      simpa only [D.largeAlmostJordan_scaleGenerator_selected] using
        htargetLarge.le
    simpa only [largeJ, A, target, largeNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.largeAlmostJordan.adjustedNormGeneratorUnit_eq_of_le
        (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
        target D.largeSelectedPosition htargetLarge'] using hlargeGenerator0
  obtain ⟨j, hjmin, hsmallSome⟩ :=
    D.smallAlmostJordan.exists_adjustedNormGeneratorUnit_spec
      (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall) p target
  have hlargeOrder :
      D.largeAlmostJordan.effectiveNormOrderAt p target = ordUnit K A := by
    simpa only [A] using
      D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
        p p p target target le_rfl htargetLarge.le hlt
  have htargetOrder : ordUnit K ((uniformizerUnit K) ^ 2 * A) =
      D.smallAlmostJordan.effectiveNormOrderAt p target := by
    rw [ordUnit_mul, ordUnit_pow]
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    rw [hpi, heffective, hlargeOrder]
    omega
  have hsmallSomeOrder :
      ordUnit K (D.smallAlmostJordan.adjustedNormGeneratorUnit
        (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
        target j) = D.smallAlmostJordan.effectiveNormOrderAt p target := by
    unfold Lattice.WeakJordanDecomposition.adjustedNormGeneratorUnit
    rw [ordUnit_mul, ordUnit_pow,
      (D.smallAlmostJordan.toJordan
        (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)).ordUnit_scaleTruncationFactor]
    simp only [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
    change 2 * max 0
        (target - D.smallAlmostJordan.scaleOrderFamily j) +
      D.smallAlmostJordan.normOrderFamily j =
        D.smallAlmostJordan.effectiveNormOrderAt p target
    rw [← hjmin]
    simp only [JordanProfileOrder.adjustedAt]
    split <;> omega
  have hrescaled :=
    D.largeAlmostJordan.rescaledNormGeneratorUnit_spec
      D.largeSelectedPosition (uniformizerUnit K)
  rw [D.largeAlmostJordan_component_selected] at hrescaled
  have hsmallComponentMem :
      ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) ∈
        Lattice.normGroupSet D.input.block.component.space
          D.input.block.component.lattice := by
    exact Lattice.normGroupSet_mono D.uniformizer_large_le_small hrescaled.1
  have hfactor : smallJ.scaleTruncationFactor target
      D.smallSelectedPosition = 1 := by
    apply smallJ.scaleTruncationFactor_eq_one_of_le
    simpa only [smallJ, smallNoCollisionJordan,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.smallAlmostJordan_scaleGenerator_selected] using htargetSmall.le
  have hcomponent :
      (smallJ.scaleTruncationDecomposition target).component
          D.smallSelectedPosition = D.input.block.component := by
    rw [smallJ.scaleTruncationDecomposition_component, hfactor]
    rw [show smallJ.component D.smallSelectedPosition =
        D.input.block.component by
      simp only [smallJ, smallNoCollisionJordan,
        Lattice.WeakJordanDecomposition.toJordan_component,
        D.smallAlmostJordan_component_selected]]
    cases D.input.block.component
    simp [QuadraticSublattice.rescaleLattice, Lattice.rescale_one]
  have hsmallMem : ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) ∈
      Lattice.normGroupSet q (Lattice.scaleTruncation q N target) := by
    have hsubset :=
      (smallJ.scaleTruncationDecomposition target).component_normGroupSet_subset
        D.smallSelectedPosition
    rw [hcomponent] at hsubset
    exact hsubset hsmallComponentMem
  have hsmallGenerator : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N target) ((uniformizerUnit K) ^ 2 * A) := by
    refine ⟨hsmallMem, ?_⟩
    calc
      Lattice.normIdeal q (Lattice.scaleTruncation q N target) =
          Lattice.principalIdeal (K := K)
            ((D.smallAlmostJordan.adjustedNormGeneratorUnit
              (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
              target j : Kˣ) : K) := hsmallSome.2
      _ = Lattice.principalIdeal (K := K)
          ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) :=
        (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2
          (hsmallSomeOrder.trans htargetOrder.symm)
  refine ⟨hlargeGenerator, ?_⟩
  simpa only [smallJ, target, smallNoCollisionJordan,
    Lattice.JordanDecomposition.fundamentalLattice,
    Lattice.JordanDecomposition.fundamentalScaleOrder,
    Lattice.WeakJordanDecomposition.toJordan_scaleGenerator, ← hscale] using
      hsmallGenerator

/-- The smaller lattice in Lemma 5.1 is contained in the larger lattice,
recovered directly from the one-vector adjunction model. -/
theorem smallLattice_le_large
    (D : Beli2019Lemma51Data q M N) : N ≤ M := by
  rw [← D.input.enlarged_eq]
  exact Lattice.le_adjoinVector N
    ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • D.input.block.representative)

/-- Multiplication by a uniformizer sends the whole larger lattice into the
smaller lattice, not only the selected component. -/
theorem uniformizer_largeLattice_le_small
    (D : Beli2019Lemma51Data q M N) :
    Lattice.rescale (uniformizerUnit K) M ≤ N := by
  rw [← D.input.enlarged_eq]
  exact Lattice.rescale_uniformizer_adjoin_uniformizerInv_smul_le
    N D.input.block.representative_mem

/-- In the binary selected-block case, multiplying the larger fundamental
lattice at scale `r'` by a uniformizer places it in the smaller fundamental
lattice at scale `r=r'+1`. -/
theorem rescale_largeFundamental_le_small_of_rank_two
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2) :
    Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K D.input.block.enlargedScaleGenerator)) ≤
      Lattice.scaleTruncation q N
        (ordUnit K D.input.block.scaleGenerator) := by
  intro x hx
  change x ∈ Lattice.rescale (uniformizerUnit K)
    (Lattice.scaleTruncation q M
      (ordUnit K D.input.block.enlargedScaleGenerator)) at hx
  change x ∈ Lattice.scaleTruncation q N
    (ordUnit K D.input.block.scaleGenerator)
  rw [Lattice.mem_rescale_iff] at hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Lattice.mem_scaleTruncation_iff_ord_bilin_ge] at hz ⊢
  refine ⟨D.uniformizer_largeLattice_le_small
    (Lattice.smul_mem_rescale (uniformizerUnit K) M hz.1), ?_⟩
  intro y hy
  have hpair := hz.2 y (D.smallLattice_le_large hy)
  rw [LinearMap.BilinForm.smul_left, ord_mul]
  change (ordUnit K D.input.block.scaleGenerator : WithTop Int) ≤
    ord K ((uniformizerUnit K : Kˣ) : K) + ord K (q.bilin z y)
  have hpi : ord K ((uniformizerUnit K : Kˣ) : K) =
      ((1 : Int) : WithTop Int) := by
    rw [← coe_ordUnit]
    congr 1
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [hpi]
  have hscale : ordUnit K D.input.block.scaleGenerator =
      ordUnit K D.input.block.enlargedScaleGenerator + 1 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo <;> omega
  rw [hscale]
  have hadd :
      (((ordUnit K D.input.block.enlargedScaleGenerator + 1 : Int) :
          WithTop Int)) =
        ((1 : Int) : WithTop Int) +
          (ordUnit K D.input.block.enlargedScaleGenerator : WithTop Int) := by
    norm_cast
    omega
  rw [hadd]
  exact add_le_add_right hpair _

/-- If the selected binary fundamental lattices have equal effective norm
order, a norm generator of the smaller fundamental lattice is also a norm
generator of the larger one. -/
theorem selected_commonNormGenerator_of_effective_eq
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (heffective :
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) =
        D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator)) :
    ∃ A : Kˣ,
      Lattice.IsNormGeneratorValue q
          ((D.largeNoCollisionJordan hlarge).fundamentalLattice
            D.largeSelectedPosition) A ∧
        Lattice.IsNormGeneratorValue q
          ((D.smallNoCollisionJordan hsmall).fundamentalLattice
            D.smallSelectedPosition) A := by
  let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let targetSmall := ordUnit K D.input.block.scaleGenerator
  let largeJ := D.largeNoCollisionJordan hlarge
  let smallJ := D.smallNoCollisionJordan hsmall
  obtain ⟨j, _hjmin, hsmallGenerator⟩ :=
    D.smallAlmostJordan.exists_adjustedNormGeneratorUnit_spec
      (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
      D.smallSelectedPosition targetSmall
  let A := D.smallAlmostJordan.adjustedNormGeneratorUnit
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
      targetSmall j
  have hscale : targetLarge ≤ targetSmall := by
    dsimp only [targetLarge, targetSmall]
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo <;> omega
  have hinclude : Lattice.scaleTruncation q N targetSmall ≤
      Lattice.scaleTruncation q M targetLarge := by
    intro z hz
    exact D.scaleTruncation_small_le_large targetLarge le_rfl
      (Lattice.scaleTruncation_anti (q := q) (L := N) hscale hz)
  have hnorm : Lattice.normIdeal q
        (Lattice.scaleTruncation q M targetLarge) =
      Lattice.normIdeal q (Lattice.scaleTruncation q N targetSmall) := by
    rw [largeJ.normIdeal_scaleTruncation_eq_powerIdeal
        D.largeSelectedPosition targetLarge,
      smallJ.normIdeal_scaleTruncation_eq_powerIdeal
        D.smallSelectedPosition targetSmall]
    change Lattice.powerIdeal (K := K)
        (D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          targetLarge) =
      Lattice.powerIdeal (K := K)
        (D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          targetSmall)
    rw [heffective]
  have hlargeGenerator : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q M targetLarge) A :=
    hsmallGenerator.of_le_of_normIdeal_eq hinclude hnorm
  refine ⟨A, ?_, ?_⟩
  · simpa only [largeJ, targetLarge, largeNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.largeAlmostJordan_scaleGenerator_selected] using hlargeGenerator
  · simpa only [smallJ, targetSmall, smallNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.smallAlmostJordan_scaleGenerator_selected] using hsmallGenerator

/-- If the selected binary effective norm increases by two, multiplication
by `π²` carries a larger-fundamental norm generator to a smaller-fundamental
norm generator. -/
theorem selected_gapTwo_normGenerator_pair
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hpos : 0 < finrank K V)
    (heffective :
      D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) =
        D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) + 2) :
    ∃ A : Kˣ,
      Lattice.IsNormGeneratorValue q
          ((D.largeNoCollisionJordan hlarge).fundamentalLattice
            D.largeSelectedPosition) A ∧
        Lattice.IsNormGeneratorValue q
          ((D.smallNoCollisionJordan hsmall).fundamentalLattice
            D.smallSelectedPosition) ((uniformizerUnit K) ^ 2 * A) := by
  let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let targetSmall := ordUnit K D.input.block.scaleGenerator
  let largeJ := D.largeNoCollisionJordan hlarge
  let smallJ := D.smallNoCollisionJordan hsmall
  obtain ⟨j, hjmin, hlargeGenerator⟩ :=
    D.largeAlmostJordan.exists_adjustedNormGeneratorUnit_spec
      (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
      D.largeSelectedPosition targetLarge
  let A := D.largeAlmostJordan.adjustedNormGeneratorUnit
    (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
      targetLarge j
  have hlargeOrder : ordUnit K A =
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
        targetLarge :=
    D.largeAlmostJordan.ordUnit_adjustedNormGeneratorUnit_eq_effective
      (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
      D.largeSelectedPosition j targetLarge hjmin
  obtain ⟨k, hkmin, hsmallSome⟩ :=
    D.smallAlmostJordan.exists_adjustedNormGeneratorUnit_spec
      (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
      D.smallSelectedPosition targetSmall
  have hsmallOrder : ordUnit K
      (D.smallAlmostJordan.adjustedNormGeneratorUnit
        (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
        targetSmall k) =
      D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
        targetSmall :=
    D.smallAlmostJordan.ordUnit_adjustedNormGeneratorUnit_eq_effective
      (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
      D.smallSelectedPosition k targetSmall hkmin
  have hrescaled := hlargeGenerator.rescale_of_finrank_pos
    (c := uniformizerUnit K) hpos
  have horder : ordUnit K ((uniformizerUnit K) ^ 2 * A) =
      ordUnit K (D.smallAlmostJordan.adjustedNormGeneratorUnit
        (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
        targetSmall k) := by
    rw [ordUnit_mul, ordUnit_pow]
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    rw [hpi, hlargeOrder, hsmallOrder, heffective]
    dsimp only [targetLarge]
    omega
  have hsmallGenerator : Lattice.IsNormGeneratorValue q
      (Lattice.scaleTruncation q N targetSmall)
      ((uniformizerUnit K) ^ 2 * A) :=
    hrescaled.of_le_of_order_eq hsmallSome
      (D.rescale_largeFundamental_le_small_of_rank_two hfin) horder
  refine ⟨A, ?_, ?_⟩
  · simpa only [largeJ, targetLarge, largeNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.largeAlmostJordan_scaleGenerator_selected] using hlargeGenerator
  · simpa only [smallJ, targetSmall, smallNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.smallAlmostJordan_scaleGenerator_selected] using hsmallGenerator

/-- If the two no-collision decompositions have identical components before
`p`, their determinant seeds at `p` differ by a square. -/
theorem noCollision_determinantSeeds_square_of_components
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (p : Fin (D.complementComponentCount + 1))
    (hcomponents : ∀ j, j < p →
      D.largeAlmostJordan.component j = D.smallAlmostJordan.component j) :
    let hLargeStrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
    let hSmallStrict :=
      D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
    let P := D.largeNoCollisionProfileWitness hlarge a
    let Q := D.smallNoCollisionProfileWitness hsmall b
    let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p
    let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p
    ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
  dsimp only
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  by_cases hpzero : p.val = 0
  · refine ⟨1, ?_⟩
    rw [BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData_leftDet_of_component_zero
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p hpzero,
      BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData_leftDet_of_component_zero
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p hpzero]
    simp
  · obtain ⟨s, hs⟩ :=
      D.exists_noCollision_prefixDeterminant_eq_mul_square
        hsmall hlarge p hcomponents hpzero
    refine ⟨s, ?_⟩
    rw [BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData_leftDet_of_component_ne_zero
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p hpzero,
      BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData_leftDet_of_component_ne_zero
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p hpzero]
    exact hs

/-- The determinant seeds at any aligned no-collision component up to the
selected block differ by a square.  At the first component both seeds are
`1`; at every later component this is the determinant square relation of the
literal common orthogonal prefix. -/
theorem noCollision_determinantSeeds_square
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (p : Fin (D.complementComponentCount + 1))
    (hp : p ≤ D.largeSelectedPosition) :
    let hLargeStrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
    let hSmallStrict :=
      D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
    let P := D.largeNoCollisionProfileWitness hlarge a
    let Q := D.smallNoCollisionProfileWitness hsmall b
    let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p
    let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p
    ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
  apply D.noCollision_determinantSeeds_square_of_components
    hsmall hlarge a b p
  intro j hj
  apply D.aligned_component_eq hselected j
  intro hjselected
  subst j
  exact (not_lt_of_ge hp) hj

/-- Before (or at the left endpoint of) the unique unary adjacent
transposition, the no-collision determinant seeds differ by a square. -/
theorem unaryShift_noCollision_determinantSeeds_square
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (p : Fin (D.complementComponentCount + 1))
    (hp : p ≤ D.largeSelectedPosition) :
    let hLargeStrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
    let hSmallStrict :=
      D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
    let P := D.largeNoCollisionProfileWitness hlarge a
    let Q := D.smallNoCollisionProfileWitness hsmall b
    let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p
    let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p
    ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
  apply D.noCollision_determinantSeeds_square_of_components
    hsmall hlarge a b p
  intro j hj
  exact D.unaryShift_component_eq_before hfin i₀ hi₀ j
    (hj.trans_le hp)

/-- On the direct reduced range in the aligned case, the right-hand
boundary coordinate used by Lemma 5.13(i) is either in a component before
the selected block or in the selected block itself.  This is the
right-boundary analogue of `weakAligned_reducedRange_coordinate`, whose
coordinate is the preceding BONG entry. -/
theorem weakAligned_reducedRange_right_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i) :
    let R : Fin n := ⟨i.val, i.lt_large⟩
    let x := D.largeWeakProfileWitness a
    (x.indexEquiv R).1 < D.largeSelectedPosition ∨
      (x.indexEquiv R).1 = D.largeSelectedPosition := by
  classical
  let R : Fin n := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let p := (x.indexEquiv R).1
  let localIndex := (x.indexEquiv R).2.val
  change p < D.largeSelectedPosition ∨ p = D.largeSelectedPosition
  change i.val ≤ D.largeSelectedStart +
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1 at hi
  have hglobal := x.index_val_eq_componentStart_add_local R
  change i.val =
    (∑ k ∈ Finset.Iio p,
      finrank K (D.largeAlmostJordan.component k).carrier) + localIndex
    at hglobal
  let selectedRank := finrank K D.input.block.component.carrier
  have hselectedRankPos : 0 < selectedRank := by
    rcases D.rank_one_or_two with h | h <;>
      dsimp only [selectedRank] <;> omega
  rw [D.largeAlmostJordan_finrank_selected] at hi
  change i.val ≤ D.largeSelectedStart + selectedRank - 1 at hi
  by_cases hbefore : p < D.largeSelectedPosition
  · exact Or.inl hbefore
  · right
    have hselectedLe : D.largeSelectedPosition ≤ p := le_of_not_gt hbefore
    by_contra hposition
    have hselectedLt : D.largeSelectedPosition < p :=
      lt_of_le_of_ne hselectedLe (Ne.symm hposition)
    have hsubset : Finset.Iic D.largeSelectedPosition ⊆ Finset.Iio p := by
      intro k hk
      exact Finset.mem_Iio.mpr
        ((Finset.mem_Iic.mp hk).trans_lt hselectedLt)
    have hsumLe :
        (∑ k ∈ Finset.Iic D.largeSelectedPosition,
            finrank K (D.largeAlmostJordan.component k).carrier) ≤
          ∑ k ∈ Finset.Iio p,
            finrank K (D.largeAlmostJordan.component k).carrier :=
      Finset.sum_le_sum_of_subset hsubset
    rw [sum_Iic_eq_sum_Iio_add,
      D.largeAlmostJordan_finrank_selected] at hsumLe
    change D.largeSelectedStart + selectedRank ≤ _ at hsumLe
    omega

/-- Lemma 5.13(i) at a boundary lying in a common component strictly before
the aligned selected block, when neither almost-Jordan family has a scale
collision.  Even local boundaries use the common determinant square class.
At odd boundaries the two effective norms differ by `0`, `1`, or `2`; the
middle case is precisely the excluded current-order jump, while the other
two cases use respectively a common generator or the pair `A`, `π²A`. -/
theorem noCollision_commonApproximation_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let xWeak := D.largeWeakProfileWitness a
  let yWeak := D.smallWeakProfileWitness b
  let p := (xWeak.indexEquiv R).1
  let j := (xWeak.indexEquiv R).2.val
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan hLargeStrict P
  let y := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan hSmallStrict Q
  have hxCoordinates := x.indexEquiv_coordinates_eq_of_componentRank_eq
    xWeak rfl R
  have hweakCoordinates := D.weakProfile_coordinates_eq hselected a b R
  have hyCoordinates := y.indexEquiv_coordinates_eq_of_componentRank_eq
    yWeak rfl R
  have hxPosition : (x.indexEquiv R).1 = p :=
    hxCoordinates.1.trans rfl
  have hxLocal : (x.indexEquiv R).2.val = j :=
    hxCoordinates.2.trans rfl
  have hyPosition : (y.indexEquiv R).1 = p :=
    hyCoordinates.1.trans (hweakCoordinates.1.symm.trans rfl)
  have hyLocal : (y.indexEquiv R).2.val = j :=
    hyCoordinates.2.trans (hweakCoordinates.2.symm.trans rfl)
  let C := x.jordanBlockCoordinates
    D.largeAlmostJordan_hasImproperEvenRank p
  let E := y.jordanBlockCoordinates
    D.smallAlmostJordan_hasImproperEvenRank p
  have hstartRaw : x.componentStart p = y.componentStart p := by
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  have hstart : C.start = E.start := hstartRaw
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = C.start + j := by
    change R.val = x.componentStart p + j
    rw [← hxPosition, ← hxLocal]
    exact hglobal
  have hstop : C.stop = E.stop := by
    change x.componentStart p +
        finrank K (D.largeAlmostJordan.component p).carrier =
      y.componentStart p +
        finrank K (D.smallAlmostJordan.component p).carrier
    rw [hstartRaw, congrFun (D.almostJordan_componentRank_eq hselected) p]
  have hiC : i.val < C.stop := by
    rw [hiStart]
    change C.start + j < C.start +
      finrank K (D.largeAlmostJordan.component p).carrier
    exact Nat.add_lt_add_left (by
      rw [← hxLocal, ← hxPosition]
      exact (x.indexEquiv R).2.isLt) _
  have hiE : i.val < E.stop := by
    rw [← hstop]
    exact hiC
  have hp : p < D.largeSelectedPosition := hbefore
  let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p
  let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.noCollision_determinantSeeds_square hsmall hlarge hselected
      a b p hp.le
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p dLarge
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator p)
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator_spec p)
    let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p dSmall
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator p)
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator_spec p)
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    let eLarge := D.largeAlmostJordan.effectiveNormOrderAt p target
    let eSmall := D.smallAlmostJordan.effectiveNormOrderAt p target
    have hbounds := D.noCollision_common_effectiveNormOrder_bounds hlarge p hp
    change eLarge ≤ eSmall ∧ eSmall ≤ eLarge + 2 at hbounds
    have hcases : eSmall = eLarge ∨ eSmall = eLarge + 1 ∨
        eSmall = eLarge + 2 := by omega
    have hnotOne : eSmall ≠ eLarge + 1 := by
      intro hone
      apply hcurrent
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩
      let localPrevious : Fin
          (finrank K (D.largeAlmostJordan.component p).carrier) :=
        ⟨j - 1, by
          have hjlt : j <
              finrank K (D.largeAlmostJordan.component p).carrier := by
            rw [← hxLocal, ← hxPosition]
            exact (x.indexEquiv R).2.isLt
          omega⟩
      have hI : I = xWeak.indexEquiv.symm ⟨p, localPrevious⟩ := by
        apply Fin.ext
        rw [xWeak.inverse_index_val]
        change i.val - 1 = xWeak.componentStart p + (j - 1)
        have hstartWeak : xWeak.componentStart p = C.start := rfl
        rw [hstartWeak, hiStart]
        omega
      have hxWeakI : xWeak.indexEquiv I = ⟨p, localPrevious⟩ := by
        rw [hI, xWeak.indexEquiv.apply_symm_apply]
      have hxyI := D.weakProfile_coordinates_eq hselected a b I
      have hscale : ordUnit K (D.smallAlmostJordan.scaleGenerator p) =
          target :=
        (D.aligned_scaleOrder_eq_of_lt hselected p hp).symm
      have hevenPrevious : Even (j - 1) := ⟨k, by omega⟩
      have hlargeScale : target ≤ eLarge :=
        D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p target
      have hsmallScale : target ≤ eSmall := by
        dsimp only [eSmall]
        rw [← hscale]
        exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt p
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
      have hlargeOrder := D.largeWeak_order_eq_localOrder a I
      have hsmallOrder := D.smallWeak_order_eq_localOrder b I
      have hxWeakIPosition : (xWeak.indexEquiv I).1 = p := by
        rw [hxWeakI]
      have hxWeakILocal : (xWeak.indexEquiv I).2.val = j - 1 := by
        rw [hxWeakI]
      have hyWeakIPosition : (yWeak.indexEquiv I).1 = p :=
        hxyI.1.symm.trans hxWeakIPosition
      have hyWeakILocal : (yWeak.indexEquiv I).2.val = j - 1 :=
        hxyI.2.symm.trans hxWeakILocal
      have hlargeOrder' : a.order I =
          JordanProfileOrder.localOrder target eLarge (j - 1) := by
        simpa only [xWeak, hxWeakIPosition, hxWeakILocal, target, eLarge]
          using hlargeOrder
      have hsmallOrder' : b.order I =
          JordanProfileOrder.localOrder target eSmall (j - 1) := by
        simpa only [yWeak, hyWeakIPosition, hyWeakILocal, hscale,
          target, eSmall] using hsmallOrder
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hlargeScale hevenPrevious] at hlargeOrder'
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hsmallScale hevenPrevious] at hsmallOrder'
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (by have := i.lt_large; omega),
        BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (by have := i.lt_large; omega)]
      change b.order I = a.order I + 1
      omega
    rcases hcases with hzero | hone | htwo
    · obtain ⟨A, hALarge, hASmall⟩ :=
        D.exists_noCollision_commonNormGenerator_of_effective_eq
          hsmall hlarge p hp
          (D.aligned_scaleOrder_eq_of_lt hselected p hp) (by
            simpa only [eLarge, eSmall, target] using hzero.symm)
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hALarge
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall A hASmall
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change A * dSmall.leftDet = (A * dLarge.leftDet) * s ^ 2
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · exact (hnotOne hone).elim
    · have hpair := D.noCollision_gapTwo_normGenerator_pair
        hsmall hlarge p hp
        (D.aligned_scaleOrder_eq_of_lt hselected p hp) htwo
      let A := D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition
      let B := (uniformizerUnit K) ^ 2 * A
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hpair.1
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall B hpair.2
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        change B * dSmall.leftDet =
          (A * dLarge.leftDet) * (uniformizerUnit K * s) ^ 2
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

/-- Lemma 5.13(i) at a boundary inside the aligned selected binary block in
the no-collision case.  The first local boundary is determinant-even.  At
the second one, the preceding BONG coordinate reads the two selected
effective norms; excluding a one-step jump leaves the equal and two-step
generator cases constructed above. -/
theorem noCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let xWeak := D.largeWeakProfileWitness a
  let yWeak := D.smallWeakProfileWitness b
  let p := D.largeSelectedPosition
  let j := (xWeak.indexEquiv R).2.val
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan hLargeStrict P
  let y := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan hSmallStrict Q
  have hxCoordinates := x.indexEquiv_coordinates_eq_of_componentRank_eq
    xWeak rfl R
  have hweakCoordinates := D.weakProfile_coordinates_eq hselected a b R
  have hyCoordinates := y.indexEquiv_coordinates_eq_of_componentRank_eq
    yWeak rfl R
  have hxPosition : (x.indexEquiv R).1 = p :=
    hxCoordinates.1.trans hposition
  have hxLocal : (x.indexEquiv R).2.val = j :=
    hxCoordinates.2.trans rfl
  have hyPosition : (y.indexEquiv R).1 = p :=
    hyCoordinates.1.trans (hweakCoordinates.1.symm.trans hposition)
  have hyLocal : (y.indexEquiv R).2.val = j :=
    hyCoordinates.2.trans (hweakCoordinates.2.symm.trans rfl)
  let C := x.jordanBlockCoordinates
    D.largeAlmostJordan_hasImproperEvenRank p
  let E := y.jordanBlockCoordinates
    D.smallAlmostJordan_hasImproperEvenRank p
  have hstartRaw : x.componentStart p = y.componentStart p := by
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  have hstart : C.start = E.start := hstartRaw
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = C.start + j := by
    change R.val = x.componentStart p + j
    rw [← hxPosition, ← hxLocal]
    exact hglobal
  have hstop : C.stop = E.stop := by
    change x.componentStart p +
        finrank K (D.largeAlmostJordan.component p).carrier =
      y.componentStart p +
        finrank K (D.smallAlmostJordan.component p).carrier
    rw [hstartRaw, congrFun (D.almostJordan_componentRank_eq hselected) p]
  have hiC : i.val < C.stop := by
    rw [hiStart]
    change C.start + j < C.start +
      finrank K (D.largeAlmostJordan.component p).carrier
    exact Nat.add_lt_add_left (by
      rw [← hxLocal, ← hxPosition]
      exact (x.indexEquiv R).2.isLt) _
  have hiE : i.val < E.stop := by
    rw [← hstop]
    exact hiC
  let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p
  let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.noCollision_determinantSeeds_square hsmall hlarge hselected
      a b p le_rfl
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p dLarge
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator p)
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator_spec p)
    let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p dSmall
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator p)
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator_spec p)
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
    let targetSmall := ordUnit K D.input.block.scaleGenerator
    let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
      D.largeSelectedPosition targetLarge
    let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
      D.smallSelectedPosition targetSmall
    have hlargeLe := D.largeSelected_effectiveNormOrder_le_smallSelected
    have hsmallLe :=
      D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
        hfin
    change eLarge ≤ eSmall at hlargeLe
    change eSmall ≤ eLarge + 2 at hsmallLe
    have hcases : eSmall = eLarge ∨ eSmall = eLarge + 1 ∨
        eSmall = eLarge + 2 := by omega
    have hnotOne : eSmall ≠ eLarge + 1 := by
      intro hone
      apply hcurrent
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩
      have hjlt : j < 2 := by
        have hlocalLt : j <
            finrank K (D.largeAlmostJordan.component p).carrier := by
          rw [← hxLocal, ← hxPosition]
          exact (x.indexEquiv R).2.isLt
        simpa only [p, D.largeAlmostJordan_finrank_selected, hfin] using
          hlocalLt
      have hj : j = 1 := by omega
      let localZero : Fin
          (finrank K (D.largeAlmostJordan.component p).carrier) :=
        ⟨0, by
          have hrank : finrank K
              (D.largeAlmostJordan.component p).carrier = 2 := by
            simpa only [p, D.largeAlmostJordan_finrank_selected] using hfin
          rw [hrank]
          omega⟩
      have hI : I = xWeak.indexEquiv.symm ⟨p, localZero⟩ := by
        apply Fin.ext
        rw [xWeak.inverse_index_val]
        change i.val - 1 = xWeak.componentStart p
        have hstartWeak : xWeak.componentStart p = C.start := rfl
        rw [hstartWeak, hiStart, hj]
        omega
      have hxWeakI : xWeak.indexEquiv I = ⟨p, localZero⟩ := by
        rw [hI, xWeak.indexEquiv.apply_symm_apply]
      have hxyI := D.weakProfile_coordinates_eq hselected a b I
      have hlargeScale : targetLarge ≤ eLarge :=
        D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
          D.largeSelectedPosition targetLarge
      have hsmallScale : targetSmall ≤ eSmall :=
        D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
          D.smallSelectedPosition targetSmall
      have hlargeOrder := D.largeWeak_order_eq_localOrder a I
      have hsmallOrder := D.smallWeak_order_eq_localOrder b I
      have hxWeakIPosition : (xWeak.indexEquiv I).1 = p := by
        rw [hxWeakI]
      have hxWeakILocal : (xWeak.indexEquiv I).2.val = 0 := by
        rw [hxWeakI]
      have hyWeakIPosition : (yWeak.indexEquiv I).1 = p :=
        hxyI.1.symm.trans hxWeakIPosition
      have hyWeakILocal : (yWeak.indexEquiv I).2.val = 0 :=
        hxyI.2.symm.trans hxWeakILocal
      have hlargeOrder' : a.order I =
          JordanProfileOrder.localOrder targetLarge eLarge 0 := by
        simpa only [xWeak, hxWeakIPosition, hxWeakILocal, p,
          targetLarge, eLarge,
          D.largeAlmostJordan_scaleGenerator_selected] using hlargeOrder
      have hsmallOrder' : b.order I =
          JordanProfileOrder.localOrder targetSmall eSmall 0 := by
        simpa only [yWeak, hyWeakIPosition, hyWeakILocal, p, ← hselected,
          targetSmall, eSmall,
          D.smallAlmostJordan_scaleGenerator_selected] using hsmallOrder
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hlargeScale (by simp)] at hlargeOrder'
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hsmallScale (by simp)] at hsmallOrder'
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (by have := i.lt_large; omega),
        BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (by have := i.lt_large; omega)]
      change b.order I = a.order I + 1
      omega
    rcases hcases with hzero | hone | htwo
    · obtain ⟨A, hALarge, hASmall⟩ :=
        D.selected_commonNormGenerator_of_effective_eq
          hsmall hlarge hfin (by
            simpa only [eLarge, eSmall, targetLarge, targetSmall] using
              hzero.symm)
      have hASmall' : Lattice.IsNormGeneratorValue q
          ((D.smallNoCollisionJordan hsmall).fundamentalLattice p) A := by
        simpa only [p, ← hselected] using hASmall
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hALarge
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall A hASmall'
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change A * dSmall.leftDet = (A * dLarge.leftDet) * s ^ 2
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · exact (hnotOne hone).elim
    · have hpos : 0 < finrank K V := by
        rw [← a.toBONG.length_eq_finrank]
        omega
      obtain ⟨A, hALarge, hASmall⟩ :=
        D.selected_gapTwo_normGenerator_pair
          hsmall hlarge hfin hpos (by
            simpa only [eLarge, eSmall, targetLarge, targetSmall] using htwo)
      let B := (uniformizerUnit K) ^ 2 * A
      have hASmall' : Lattice.IsNormGeneratorValue q
          ((D.smallNoCollisionJordan hsmall).fundamentalLattice p) B := by
        simpa only [p, B, ← hselected] using hASmall
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hALarge
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall B hASmall'
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        change B * dSmall.leftDet =
          (A * dLarge.leftDet) * (uniformizerUnit K * s) ^ 2
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

/-- Lemma 5.13(i) at the aligned selected unary component in the
no-collision case.  Its only local boundary has coordinate zero, so the
common approximation is the determinant-even seed and no norm comparison
is needed. -/
theorem noCollision_commonApproximation_at_selected_rank_one
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let xWeak := D.largeWeakProfileWitness a
  let yWeak := D.smallWeakProfileWitness b
  let p := D.largeSelectedPosition
  let j := (xWeak.indexEquiv R).2.val
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan hLargeStrict P
  let y := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan hSmallStrict Q
  have hxCoordinates := x.indexEquiv_coordinates_eq_of_componentRank_eq
    xWeak rfl R
  have hweakCoordinates := D.weakProfile_coordinates_eq hselected a b R
  have hyCoordinates := y.indexEquiv_coordinates_eq_of_componentRank_eq
    yWeak rfl R
  have hxPosition : (x.indexEquiv R).1 = p :=
    hxCoordinates.1.trans hposition
  have hxLocal : (x.indexEquiv R).2.val = j :=
    hxCoordinates.2.trans rfl
  have hyPosition : (y.indexEquiv R).1 = p :=
    hyCoordinates.1.trans (hweakCoordinates.1.symm.trans hposition)
  have hyLocal : (y.indexEquiv R).2.val = j :=
    hyCoordinates.2.trans (hweakCoordinates.2.symm.trans rfl)
  let C := x.jordanBlockCoordinates
    D.largeAlmostJordan_hasImproperEvenRank p
  let E := y.jordanBlockCoordinates
    D.smallAlmostJordan_hasImproperEvenRank p
  have hstartRaw : x.componentStart p = y.componentStart p := by
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  have hstart : C.start = E.start := hstartRaw
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = C.start + j := by
    change R.val = x.componentStart p + j
    rw [← hxPosition, ← hxLocal]
    exact hglobal
  have hstop : C.stop = E.stop := by
    change x.componentStart p +
        finrank K (D.largeAlmostJordan.component p).carrier =
      y.componentStart p +
        finrank K (D.smallAlmostJordan.component p).carrier
    rw [hstartRaw, congrFun (D.almostJordan_componentRank_eq hselected) p]
  have hiC : i.val < C.stop := by
    rw [hiStart]
    change C.start + j < C.start +
      finrank K (D.largeAlmostJordan.component p).carrier
    exact Nat.add_lt_add_left (by
      rw [← hxLocal, ← hxPosition]
      exact (x.indexEquiv R).2.isLt) _
  have hiE : i.val < E.stop := by
    rw [← hstop]
    exact hiC
  have hjlt : j < 1 := by
    have hlocalLt : j <
        finrank K (D.largeAlmostJordan.component p).carrier := by
      rw [← hxLocal, ← hxPosition]
      exact (x.indexEquiv R).2.isLt
    simpa only [p, D.largeAlmostJordan_finrank_selected, hfin] using
      hlocalLt
  have hj : j = 0 := by omega
  let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p
  let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.noCollision_determinantSeeds_square hsmall hlarge hselected
      a b p le_rfl
  let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p dLarge
      ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator p)
      ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator_spec p)
  let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p dSmall
      ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator p)
      ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator_spec p)
  apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet
    i.val 0
  · calc
      i.val = C.start + j := hiStart
      _ = C.start + 2 * 0 := by omega
  · exact hiC
  · exact hiE

/-- Lemma 5.13(i) at a boundary in a component strictly before the unique
unary adjacent transposition.  The component coordinates, prefix ranks, and
scales agree on this range, so the aligned no-collision seed calculation
applies componentwise even though the selected positions differ globally. -/
theorem unaryShift_noCollision_commonApproximation_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  let p := (P.indexEquiv R).1
  let j := (P.indexEquiv R).2.val
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan hLargeStrict P
  let y := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan hSmallStrict Q
  have hxCoordinates :
      (x.indexEquiv R).1 = (P.indexEquiv R).1 ∧
        (x.indexEquiv R).2.val = (P.indexEquiv R).2.val := by
    exact ⟨rfl, rfl⟩
  have hstrictCoordinates := D.unaryShift_profile_coordinates_eq_before
    hsmall hlarge hfin i₀ hi₀ a b R hbefore
  have hyCoordinates :
      (y.indexEquiv R).1 = (Q.indexEquiv R).1 ∧
        (y.indexEquiv R).2.val = (Q.indexEquiv R).2.val := by
    exact ⟨rfl, rfl⟩
  have hxPosition : (x.indexEquiv R).1 = p :=
    hxCoordinates.1.trans rfl
  have hxLocal : (x.indexEquiv R).2.val = j :=
    hxCoordinates.2.trans rfl
  have hyPosition : (y.indexEquiv R).1 = p :=
    hyCoordinates.1.trans (hstrictCoordinates.1.symm.trans rfl)
  have hyLocal : (y.indexEquiv R).2.val = j :=
    hyCoordinates.2.trans (hstrictCoordinates.2.symm.trans rfl)
  have hp : p < D.largeSelectedPosition := hbefore
  let C := x.jordanBlockCoordinates
    D.largeAlmostJordan_hasImproperEvenRank p
  let E := y.jordanBlockCoordinates
    D.smallAlmostJordan_hasImproperEvenRank p
  have hstartRaw : x.componentStart p = y.componentStart p := by
    change
      (∑ k ∈ Finset.Iio p,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank k) =
      ∑ k ∈ Finset.Iio p,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank k
    exact D.unaryShift_prefixRank_eq_before
      hsmall hlarge hfin i₀ hi₀ p hp
  have hstart : C.start = E.start := hstartRaw
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = C.start + j := by
    change R.val = x.componentStart p + j
    rw [← hxPosition, ← hxLocal]
    exact hglobal
  have hstop : C.stop = E.stop := by
    have hrank := D.unaryShift_componentRank_eq_before
      hsmall hlarge hfin i₀ hi₀ p hp
    change finrank K (D.largeAlmostJordan.component p).carrier =
      finrank K (D.smallAlmostJordan.component p).carrier at hrank
    change x.componentStart p +
        finrank K (D.largeAlmostJordan.component p).carrier =
      y.componentStart p +
        finrank K (D.smallAlmostJordan.component p).carrier
    rw [hstartRaw, hrank]
  have hiC : i.val < C.stop := by
    rw [hiStart]
    change C.start + j < C.start +
      finrank K (D.largeAlmostJordan.component p).carrier
    exact Nat.add_lt_add_left (by
      rw [← hxLocal, ← hxPosition]
      exact (x.indexEquiv R).2.isLt) _
  have hiE : i.val < E.stop := by
    rw [← hstop]
    exact hiC
  have hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) :=
    D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ p hp
  let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p
  let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.unaryShift_noCollision_determinantSeeds_square
      hsmall hlarge hfin i₀ hi₀ a b p hp.le
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
        hLargeStrict P p dLarge
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator p)
        ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator_spec p)
    let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
        hSmallStrict Q p dSmall
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator p)
        ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator_spec p)
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    let eLarge := D.largeAlmostJordan.effectiveNormOrderAt p target
    let eSmall := D.smallAlmostJordan.effectiveNormOrderAt p target
    have hbounds := D.noCollision_common_effectiveNormOrder_bounds hlarge p hp
    change eLarge ≤ eSmall ∧ eSmall ≤ eLarge + 2 at hbounds
    have hcases : eSmall = eLarge ∨ eSmall = eLarge + 1 ∨
        eSmall = eLarge + 2 := by omega
    have hnotOne : eSmall ≠ eLarge + 1 := by
      intro hone
      apply hcurrent
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩
      let localPrevious : Fin
          (finrank K (D.largeAlmostJordan.component p).carrier) :=
        ⟨j - 1, by
          have hjlt : j <
              finrank K (D.largeAlmostJordan.component p).carrier := by
            rw [← hxLocal, ← hxPosition]
            exact (x.indexEquiv R).2.isLt
          omega⟩
      have hI : I = x.indexEquiv.symm ⟨p, localPrevious⟩ := by
        apply Fin.ext
        rw [x.inverse_index_val]
        change i.val - 1 = x.componentStart p + (j - 1)
        have hstartX : x.componentStart p = C.start := rfl
        rw [hstartX, hiStart]
        omega
      have hxI : x.indexEquiv I = ⟨p, localPrevious⟩ := by
        rw [hI, x.indexEquiv.apply_symm_apply]
      have hPIPosition : (P.indexEquiv I).1 = p := by
        change (x.indexEquiv I).1 = p
        rw [hxI]
      have hPILocal : (P.indexEquiv I).2.val = j - 1 := by
        change (x.indexEquiv I).2.val = j - 1
        rw [hxI]
      have hxyI := D.unaryShift_profile_coordinates_eq_before
        hsmall hlarge hfin i₀ hi₀ a b I (by
          rw [hPIPosition]
          exact hp)
      have hsmallScale : ordUnit K
          (D.smallAlmostJordan.scaleGenerator p) = target := by
        exact hscale.symm
      have hevenPrevious : Even (j - 1) := ⟨k, by omega⟩
      have hlargeScale : target ≤ eLarge :=
        D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p target
      have hsmallScaleLe : target ≤ eSmall := by
        dsimp only [eSmall]
        rw [← hsmallScale]
        exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt p
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
      have hlargeOrder := D.largeNoCollision_order_eq_localOrder hlarge a I
      have hsmallOrder := D.smallNoCollision_order_eq_localOrder hsmall b I
      have hxIPosition : (P.indexEquiv I).1 = p := hPIPosition
      have hxILocal : (P.indexEquiv I).2.val = j - 1 := hPILocal
      have hyIPosition : (Q.indexEquiv I).1 = p :=
        hxyI.1.symm.trans hxIPosition
      have hyILocal : (Q.indexEquiv I).2.val = j - 1 :=
        hxyI.2.symm.trans hxILocal
      have hlargeOrder' : a.order I =
          JordanProfileOrder.localOrder target eLarge (j - 1) := by
        simpa only [P, hxIPosition, hxILocal, target, eLarge]
          using hlargeOrder
      have hsmallOrder' : b.order I =
          JordanProfileOrder.localOrder target eSmall (j - 1) := by
        simpa only [Q, hyIPosition, hyILocal, hsmallScale,
          target, eSmall] using hsmallOrder
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hlargeScale hevenPrevious] at hlargeOrder'
      rw [JordanProfileOrder.localOrder_even_of_scale_le
          hsmallScaleLe hevenPrevious] at hsmallOrder'
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (by have := i.lt_large; omega),
        BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (by have := i.lt_large; omega)]
      change b.order I = a.order I + 1
      omega
    rcases hcases with hzero | hone | htwo
    · obtain ⟨A, hALarge, hASmall⟩ :=
        D.exists_noCollision_commonNormGenerator_of_effective_eq
          hsmall hlarge p hp hscale (by
            simpa only [eLarge, eSmall, target] using hzero.symm)
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hALarge
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall A hASmall
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change A * dSmall.leftDet = (A * dLarge.leftDet) * s ^ 2
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · exact (hnotOne hone).elim
    · have hpair := D.noCollision_gapTwo_normGenerator_pair
        hsmall hlarge p hp hscale htwo
      let A := D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition
      let B := (uniformizerUnit K) ^ 2 * A
      let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hLargeStrict P p dLarge A hpair.1
      let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
          hSmallStrict Q p dSmall B hpair.2
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        change B * dSmall.leftDet =
          (A * dLarge.leftDet) * (uniformizerUnit K * s) ^ 2
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

/-- Lemma 5.13(i) at the selected unary component when the small and large
almost-Jordan decompositions differ by the unique adjacent unary shift.  The
selected coordinate is zero, so the determinant-even seeds give the common
approximation directly. -/
theorem unaryShift_noCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let p := D.largeSelectedPosition
  let hLargeStrict :=
    D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let hSmallStrict :=
    D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
  let P := D.largeNoCollisionProfileWitness hlarge a
  let Q := D.smallNoCollisionProfileWitness hsmall b
  let x := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan hLargeStrict P
  let y := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan hSmallStrict Q
  change (x.indexEquiv R).1 = p at hposition
  have hlargeRank : finrank K
      (D.largeAlmostJordan.component p).carrier = 1 := by
    simpa only [p, D.largeAlmostJordan_finrank_selected] using hfin
  have hlocalZero : (x.indexEquiv R).2.val = 0 := by
    have hrankAt : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv R).1).carrier = 1 := by
      rw [hposition]
      exact hlargeRank
    have hlt : (x.indexEquiv R).2.val <
        finrank K
          (D.largeAlmostJordan.component (x.indexEquiv R).1).carrier :=
      (x.indexEquiv R).2.isLt
    have hltOne : (x.indexEquiv R).2.val < 1 :=
      lt_of_lt_of_eq hlt hrankAt
    omega
  let C := x.jordanBlockCoordinates
    D.largeAlmostJordan_hasImproperEvenRank p
  let E := y.jordanBlockCoordinates
    D.smallAlmostJordan_hasImproperEvenRank p
  have hstartRaw : x.componentStart p = y.componentStart p := by
    change
      (∑ k ∈ Finset.Iio p,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank k) =
      ∑ k ∈ Finset.Iio p,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank k
    exact D.unaryShift_prefixRank_eq hsmall hlarge hfin i₀ hi₀
  have hstart : C.start = E.start := hstartRaw
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = C.start := by
    change R.val = x.componentStart p
    have hcomponentStart :
        x.componentStart (x.indexEquiv R).1 = x.componentStart p :=
      congrArg x.componentStart hposition
    calc
      R.val = x.componentStart (x.indexEquiv R).1 +
          (x.indexEquiv R).2.val := hglobal
      _ = x.componentStart p := by rw [hcomponentStart, hlocalZero]; omega
  have hiC : i.val < C.stop := by
    rw [hiStart]
    exact C.start_lt_stop
  have hiE : i.val < E.stop := by
    rw [hiStart, hstart]
    exact E.start_lt_stop
  let dLarge := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p
  let dSmall := BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedData
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.unaryShift_noCollision_determinantSeeds_square
      hsmall hlarge hfin i₀ hi₀ a b p le_rfl
  let S := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
    D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      hLargeStrict P p dLarge
      ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator p)
      ((D.largeNoCollisionJordan hlarge).fundamentalNormGenerator_spec p)
  let T := BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWith
    D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      hSmallStrict Q p dSmall
      ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator p)
      ((D.smallNoCollisionJordan hsmall).fundamentalNormGenerator_spec p)
  apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet
    i.val 0
  · simpa only [Nat.mul_zero, Nat.add_zero] using hiStart
  · exact hiC
  · exact hiE

/-- Complete Lemma 5.13 data on its literal range in the no-collision unary
adjacent-transposition case.  This deliberately stops at the end of the
large selected unary block; the later exceptional interval is handled by
the separate Section 5 cases 3--4 certificates. -/
theorem noCollision_unaryShift_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range where
  commonApproximation i hi hcurrent := by
    let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
    let xWeak := D.largeWeakProfileWitness a
    let P := D.largeNoCollisionProfileWitness hlarge a
    let x := BONG.WeakJordanOrderProfileWitness.ofStrict
      D.largeAlmostJordan
        (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge) P
    have hxCoordinates := x.indexEquiv_coordinates_eq_of_componentRank_eq
      xWeak rfl R
    rcases D.weakAligned_reducedRange_right_coordinate a i hi with
      hbefore | hposition
    · have hstrictBefore : (P.indexEquiv R).1 <
          D.largeSelectedPosition := by
        change (x.indexEquiv R).1 < D.largeSelectedPosition
        rw [hxCoordinates.1]
        exact hbefore
      exact D.unaryShift_noCollision_commonApproximation_before_selected
        hsmall hlarge hfin i₀ hi₀ a b i hstrictBefore hcurrent
    · have hstrictPosition : (P.indexEquiv R).1 =
          D.largeSelectedPosition := by
        change (x.indexEquiv R).1 = D.largeSelectedPosition
        exact hxCoordinates.1.trans hposition
      exact D.unaryShift_noCollision_commonApproximation_at_selected
        hsmall hlarge hfin i₀ hi₀ a b i hstrictPosition
  previousPrefixSum_eq i hi hcurrent := by
    have hstart := D.weakUnaryShift_smallSelectedStart_eq_intervalEnd
      hfin i₀ hi₀
    change D.smallSelectedStart = D.largeSelectedStart +
      finrank K (D.complementStrictWeak.component i₀).carrier at hstart
    have hcommonRankPos :
        0 < finrank K (D.complementStrictWeak.component i₀).carrier :=
      D.complementStrictWeak.component_finrank_pos i₀
    have hiDefect : D.DefectReducedRange i := by
      change i.val ≤ D.largeSelectedStart +
        finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
        at hi
      change i.val ≤ D.smallSelectedStart +
        finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      rw [D.largeAlmostJordan_finrank_selected] at hi
      rw [D.smallAlmostJordan_finrank_selected, hstart]
      omega
    exact D.weakUnaryShift_previousPrefixSum_eq_of_current_succ_reduced
      hfin i₀ hi₀ a b i hiDefect hcurrent

/-- Complete direct-range Lemma 5.13 data for the aligned case when both
almost-Jordan families are already strict.  The approximation branch is
split by the right boundary coordinate, while the prefix-sum branch is the
all-ranks weak-profile calculation. -/
theorem noCollision_aligned_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range where
  commonApproximation i hi hcurrent := by
    rcases D.weakAligned_reducedRange_right_coordinate a i hi with
      hbefore | hposition
    · exact D.noCollision_commonApproximation_before_selected
        hsmall hlarge hselected a b i hbefore hcurrent
    · rcases D.rank_one_or_two with hOne | hTwo
      · exact D.noCollision_commonApproximation_at_selected_rank_one
          hsmall hlarge hselected hOne a b i hposition
      · exact D.noCollision_commonApproximation_at_selected
          hsmall hlarge hselected hTwo a b i hposition hcurrent
  previousPrefixSum_eq i hi hcurrent := by
    have hstart :=
      D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
    change D.largeSelectedStart = D.smallSelectedStart at hstart
    have hiDefect : D.DefectReducedRange i := by
      change i.val ≤ D.largeSelectedStart +
        finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
        at hi
      change i.val ≤ D.smallSelectedStart +
        finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      rw [D.largeAlmostJordan_finrank_selected] at hi
      rw [D.smallAlmostJordan_finrank_selected, ← hstart]
      exact hi
    exact D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
      a b i hiDefect hcurrent

/-- Complete no-collision Lemma 5.13 data in both possible selected-rank
cases.  Rank two is aligned.  Rank one is either aligned or the unique
adjacent unary transposition handled above. -/
theorem noCollision_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range := by
  rcases D.rank_one_or_two with hOne | hTwo
  · rcases D.selectedPositions_unary_alternative hOne with
      hselected | hunary
    · exact D.noCollision_aligned_lemma513LocalData
        hsmall hlarge hselected a b
    · obtain ⟨i₀, ⟨hi₀, _hposition⟩, _hunique⟩ := hunary
      exact D.noCollision_unaryShift_lemma513LocalData
        hsmall hlarge hOne i₀ hi₀ a b
  · exact D.noCollision_aligned_lemma513LocalData hsmall hlarge
      (D.selectedPositions_eq_of_rank_two hTwo) a b

end Lattice.Beli2019Lemma51Data

end Bong
