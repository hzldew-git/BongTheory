/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityOrthogonalizedBasis
import Bong.Lattice.OmearaBoundaryBinaryCongruence
import Bong.Lattice.NormGroupValuationUnitSquare
import Bong.Lattice.OmearaNormGeneratorDefect

/-!
# O'Meara 93:28 necessity: the first-boundary discriminants

This file applies the boundary determinant calculation to the projected
adapted basis used in Step 1 of O'Meara 93:28.  The key geometric input is
that an isotropic source-head vector is carried to a target head vector
whose negative norm is represented by the discarded Jordan tail.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- If an integral source-head vector is isotropic, then the negative norm
of its projected target-head component belongs to the second fundamental
norm group.  It is the sum of the norms of the discarded target
coordinates, all of which occur at Jordan scales at least the second one. -/
theorem neg_firstProjection_quadratic_mem_targetFundamentalNormGroup_one_of_source_mem
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hsource : (S.sourceJordan.component 0).space.quadratic x ∈
      S.targetJordan.fundamentalNormGroup 1) :
    -(S.targetJordan.component 0).space.quadratic
        (S.firstProjectionMap f x) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  classical
  have hterm : ∀ i : Fin (n + 1),
      (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) ∈
        S.targetJordan.fundamentalNormGroup 1 := by
    intro i
    let z := f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ
    have hz : z ∈ S.targetLattice i.succ :=
      S.targetResidualCoordinate_mem f hx i.succ
    have hzRaw : (S.targetForm i.succ).quadratic z ∈
        normGroupSet (S.targetForm i.succ) (S.targetLattice i.succ) := by
      exact ⟨z, hz, 0, Submodule.zero_mem _, by simp⟩
    have hzComponent : (S.targetForm i.succ).quadratic z ∈
        normGroupSet (S.targetJordan.component i.succ).space
          (S.targetJordan.component i.succ).lattice := by
      rw [S.targetJordan_component_normGroupSet i.succ,
        ← (S.pair i.succ).targetResidualNormGroupSet_eq]
      exact hzRaw
    have hzFundamental : (S.targetForm i.succ).quadratic z ∈
        S.targetJordan.fundamentalNormGroup i.succ := by
      rw [← S.targetJordan_isSaturated i.succ]
      exact hzComponent
    exact S.targetJordan.fundamentalNormGroup_anti
      (show (1 : Fin (n + 2)) ≤ i.succ by
        rw [Fin.le_iff_val_le_val]
        simp) hzFundamental
  have htail :
      ∑ i : Fin (n + 1),
        (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    let Q := BONG.blockOrthogonalForm (n + 1)
      S.targetCarrier S.targetForm
    let N := S.targetJordan.fundamentalLattice 1
    change (∑ i : Fin (n + 1),
        (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)) ∈
      normGroupSet Q N
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction_on with
    | empty =>
        simpa using zero_mem_normGroupSet Q N
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact add_mem_normGroupSet Q N (hterm i) ih
  have hsplit := S.firstProjection_bilin_add_tail f x x
  have heq :
      -(S.targetJordan.component 0).space.quadratic
          (S.firstProjectionMap f x) =
        ∑ i : Fin (n + 1),
          (S.targetForm i.succ).quadratic
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) -
          (S.sourceJordan.component 0).space.quadratic x := by
    change -((S.targetJordan.component 0).space.bilin
          (S.firstProjectionMap f x) (S.firstProjectionMap f x)) =
      ∑ i : Fin (n + 1),
        (S.targetForm i.succ).bilin
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) -
        (S.sourceJordan.component 0).space.bilin x x
    linear_combination -hsplit
  have hdifference :
      (∑ i : Fin (n + 1),
          (S.targetForm i.succ).quadratic
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)) -
        (S.sourceJordan.component 0).space.quadratic x ∈
      S.targetJordan.fundamentalNormGroup 1 :=
    sub_mem_normGroupSet
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (S.targetJordan.fundamentalLattice 1) htail hsource
  rw [heq]
  exact hdifference

/-- The projection changes the quadratic value of every integral
source-head vector by an element of the second target fundamental norm
group.  This is the precise `g₂` error term used in Step 1 of O'Meara
93:28; no assertion about the second scale ideal is needed. -/
theorem firstProjection_quadratic_sub_source_quadratic_mem_targetFundamentalNormGroup_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice) :
    (S.targetJordan.component 0).space.quadratic
          (S.firstProjectionMap f x) -
        (S.sourceJordan.component 0).space.quadratic x ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  classical
  have hterm : ∀ i : Fin (n + 1),
      (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) ∈
        S.targetJordan.fundamentalNormGroup 1 := by
    intro i
    let z := f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ
    have hz : z ∈ S.targetLattice i.succ :=
      S.targetResidualCoordinate_mem f hx i.succ
    have hzRaw : (S.targetForm i.succ).quadratic z ∈
        normGroupSet (S.targetForm i.succ) (S.targetLattice i.succ) := by
      exact ⟨z, hz, 0, Submodule.zero_mem _, by simp⟩
    have hzComponent : (S.targetForm i.succ).quadratic z ∈
        normGroupSet (S.targetJordan.component i.succ).space
          (S.targetJordan.component i.succ).lattice := by
      rw [S.targetJordan_component_normGroupSet i.succ,
        ← (S.pair i.succ).targetResidualNormGroupSet_eq]
      exact hzRaw
    have hzFundamental : (S.targetForm i.succ).quadratic z ∈
        S.targetJordan.fundamentalNormGroup i.succ := by
      rw [← S.targetJordan_isSaturated i.succ]
      exact hzComponent
    exact S.targetJordan.fundamentalNormGroup_anti
      (show (1 : Fin (n + 2)) ≤ i.succ by
        rw [Fin.le_iff_val_le_val]
        simp) hzFundamental
  have htail :
      ∑ i : Fin (n + 1),
        (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    let Q := BONG.blockOrthogonalForm (n + 1)
      S.targetCarrier S.targetForm
    let N := S.targetJordan.fundamentalLattice 1
    change (∑ i : Fin (n + 1),
        (S.targetForm i.succ).quadratic
          (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)) ∈
      normGroupSet Q N
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction_on with
    | empty =>
        simpa using zero_mem_normGroupSet Q N
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact add_mem_normGroupSet Q N (hterm i) ih
  have hsplit := S.firstProjection_bilin_add_tail f x x
  have heq :
      (S.targetJordan.component 0).space.quadratic
          (S.firstProjectionMap f x) -
        (S.sourceJordan.component 0).space.quadratic x =
      -(∑ i : Fin (n + 1),
          (S.targetForm i.succ).quadratic
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)) := by
    change (S.targetJordan.component 0).space.bilin
          (S.firstProjectionMap f x) (S.firstProjectionMap f x) -
        (S.sourceJordan.component 0).space.bilin x x =
      -(∑ i : Fin (n + 1),
          (S.targetForm i.succ).bilin
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ)
            (f.toLinearEquiv (S.sourceHeadEmbedding x) i.succ))
    linear_combination hsplit
  rw [heq]
  exact neg_mem_normGroupSet
    (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
    (S.targetJordan.fundamentalLattice 1) htail

/-- Isotropic source-head vectors are the principal special case of the
preceding tail identity. -/
theorem neg_firstProjection_quadratic_mem_targetFundamentalNormGroup_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    {x : (S.sourceJordan.component 0).carrier}
    (hx : x ∈ (S.sourceJordan.component 0).lattice)
    (hiso : (S.sourceJordan.component 0).space.quadratic x = 0) :
    -(S.targetJordan.component 0).space.quadratic
        (S.firstProjectionMap f x) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  apply S.neg_firstProjection_quadratic_mem_targetFundamentalNormGroup_one_of_source_mem
    f hx
  rw [hiso]
  unfold fundamentalNormGroup
  exact zero_mem_normGroupSet _ _

/-- Undo the common first-scale normalization on a source-head pairing. -/
theorem sourceFirst_bilin_eq_firstScale_mul_normalized
    (x y : (S.sourceJordan.component 0).carrier) :
    (S.sourceJordan.component 0).space.bilin x y =
      (S.firstScale : K) * S.sourceFirstNormalized.bilin x y := by
  simp only [sourceFirstNormalized,
    QuadraticSpace.rescaleUnit_bilin_apply, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero S.firstScale]

/-- Undo the common first-scale normalization on a target-head pairing. -/
theorem targetFirst_bilin_eq_firstScale_mul_normalized
    (x y : (S.targetJordan.component 0).carrier) :
    (S.targetJordan.component 0).space.bilin x y =
      (S.firstScale : K) * S.targetFirstNormalized.bilin x y := by
  simp only [targetFirstNormalized,
    QuadraticSpace.rescaleUnit_bilin_apply, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero S.firstScale]

/-- Multiplication by the square of the actual relative second-scale
generator carries the first fundamental norm group into the second. -/
theorem relativeSecondScale_sq_mul_mem_sourceFundamentalNormGroup_one
    {z : K} (hz : z ∈ S.sourceJordan.fundamentalNormGroup 0) :
    (((S.relativeSecondScale ^ 2 : Kˣ) : K) * z) ∈
      S.sourceJordan.fundamentalNormGroup 1 := by
  let p : Kˣ := uniformizerPowerUnit K
    (S.sourceJordan.fundamentalScaleOrder 1 -
      S.sourceJordan.fundamentalScaleOrder 0)
  have hp : (((p ^ 2 : Kˣ) : K) * z) ∈
      S.sourceJordan.fundamentalNormGroup 1 := by
    simpa only [p] using
      (S.sourceJordan.fundamentalNormGroup_sq_scale_subset
        (i := (0 : Fin (n + 2))) (j := (1 : Fin (n + 2)))
        (by simp) hz)
  have horder : ordUnit K p = ordUnit K S.relativeSecondScale := by
    dsimp only [p]
    rw [ordUnit_uniformizerPowerUnit, S.relativeSecondScale_order]
  unfold fundamentalNormGroup at hp ⊢
  exact (sq_mul_mem_normGroupSet_iff_sq_mul_of_ordUnit_eq
    (q := BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
    (L := S.sourceJordan.fundamentalLattice 1)
    p S.relativeSecondScale horder z).1 hp

/-- A value of the adapted first plane whose two coefficients lie in the
relative second-scale ideal belongs to the second fundamental norm group. -/
theorem sourceAdaptedFirstPlane_quadratic_mem_fundamentalNormGroup_one
    {alpha beta : K}
    (halpha : alpha ∈
      principalIdeal (K := K) (S.relativeSecondScale : K))
    (hbeta : beta ∈
      principalIdeal (K := K) (S.relativeSecondScale : K)) :
    (S.sourceJordan.component 0).space.quadratic
        (alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1) ∈
      S.sourceJordan.fundamentalNormGroup 1 := by
  rw [principalIdeal, Submodule.mem_span_singleton] at halpha hbeta
  rcases halpha with ⟨a, ha⟩
  rcases hbeta with ⟨b, hb⟩
  have haField : algebraMap (IntegerRing K) K a *
      (S.relativeSecondScale : K) = alpha := by
    simpa only [Algebra.smul_def] using ha
  have hbField : algebraMap (IntegerRing K) K b *
      (S.relativeSecondScale : K) = beta := by
    simpa only [Algebra.smul_def] using hb
  let u := (a : K) • S.sourceHeadAdaptedBasis 0 +
    (b : K) • S.sourceHeadAdaptedBasis 1
  have hb0 : S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 0 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨0, rfl⟩
  have hb1 : S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 1 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨1, rfl⟩
  have hu : u ∈ (S.sourceJordan.component 0).lattice := by
    apply (S.sourceJordan.component 0).lattice.add_mem
    · change algebraMap (IntegerRing K) K a •
        S.sourceHeadAdaptedBasis 0 ∈ (S.sourceJordan.component 0).lattice
      exact (S.sourceJordan.component 0).lattice.smul_mem a hb0
    · change algebraMap (IntegerRing K) K b •
        S.sourceHeadAdaptedBasis 1 ∈ (S.sourceJordan.component 0).lattice
      exact (S.sourceJordan.component 0).lattice.smul_mem b hb1
  have huComponent : (S.sourceJordan.component 0).space.quadratic u ∈
      normGroupSet (S.sourceJordan.component 0).space
        (S.sourceJordan.component 0).lattice :=
    ⟨u, hu, 0, Submodule.zero_mem _, by simp⟩
  have huFundamental : (S.sourceJordan.component 0).space.quadratic u ∈
      S.sourceJordan.fundamentalNormGroup 0 := by
    rw [← S.sourceJordan_isSaturated 0]
    exact huComponent
  have hscaled :=
    S.relativeSecondScale_sq_mul_mem_sourceFundamentalNormGroup_one huFundamental
  have hvector : alpha • S.sourceHeadAdaptedBasis 0 +
      beta • S.sourceHeadAdaptedBasis 1 =
        (S.relativeSecondScale : K) • u := by
    dsimp only [u]
    rw [← haField, ← hbField]
    rw [ValuationSubring.algebraMap_apply (IntegerRing K) a,
      ValuationSubring.algebraMap_apply (IntegerRing K) b]
    module
  rw [hvector, QuadraticSpace.quadratic_smul]
  simpa only [Units.val_pow_eq_pow_val] using hscaled

set_option maxHeartbeats 1000000 in
/-- The fourth adapted source vector is isotropic and orthogonal to the
first adapted plane, so adding a first-plane vector changes only by the
quadratic value of that vector. -/
theorem sourceAdaptedThree_add_firstPlane_quadratic
    (alpha beta : K) :
    (S.sourceJordan.component 0).space.quadratic
        (S.sourceHeadAdaptedBasis 3 +
          alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1) =
      (S.sourceJordan.component 0).space.quadratic
        (alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1) := by
  apply (mul_left_cancel₀ (Units.ne_zero (S.firstScale⁻¹)))
  change S.sourceFirstNormalized.quadratic
      (S.sourceHeadAdaptedBasis 3 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1) =
    S.sourceFirstNormalized.quadratic
      (alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1)
  change S.sourceFirstNormalized.bilin
      (S.sourceHeadAdaptedBasis 3 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1)
      (S.sourceHeadAdaptedBasis 3 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1) =
    S.sourceFirstNormalized.bilin
      (alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1)
      (alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1)
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [S.sourceHeadAdaptedBasis_bilin 3 3,
    S.sourceHeadAdaptedBasis_bilin 3 0,
    S.sourceHeadAdaptedBasis_bilin 3 1,
    S.sourceHeadAdaptedBasis_bilin 0 3,
    S.sourceHeadAdaptedBasis_bilin 1 3]
  simp

set_option maxHeartbeats 1000000 in
/-- The third adapted source vector is orthogonal to the first adapted
plane, so adding a first-plane vector adds exactly its quadratic value. -/
theorem sourceAdaptedTwo_add_firstPlane_quadratic
    (alpha beta : K) :
    (S.sourceJordan.component 0).space.quadratic
        (S.sourceHeadAdaptedBasis 2 +
          alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1) =
      (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 2) +
        (S.sourceJordan.component 0).space.quadratic
          (alpha • S.sourceHeadAdaptedBasis 0 +
            beta • S.sourceHeadAdaptedBasis 1) := by
  apply (mul_left_cancel₀ (Units.ne_zero (S.firstScale⁻¹)))
  rw [mul_add]
  change S.sourceFirstNormalized.quadratic
      (S.sourceHeadAdaptedBasis 2 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1) =
    S.sourceFirstNormalized.quadratic (S.sourceHeadAdaptedBasis 2) +
      S.sourceFirstNormalized.quadratic
        (alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1)
  change S.sourceFirstNormalized.bilin
      (S.sourceHeadAdaptedBasis 2 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1)
      (S.sourceHeadAdaptedBasis 2 +
        alpha • S.sourceHeadAdaptedBasis 0 +
        beta • S.sourceHeadAdaptedBasis 1) =
    S.sourceFirstNormalized.bilin
        (S.sourceHeadAdaptedBasis 2) (S.sourceHeadAdaptedBasis 2) +
      S.sourceFirstNormalized.bilin
        (alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1)
        (alpha • S.sourceHeadAdaptedBasis 0 +
          beta • S.sourceHeadAdaptedBasis 1)
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [S.sourceHeadAdaptedBasis_bilin 2 0,
    S.sourceHeadAdaptedBasis_bilin 2 1,
    S.sourceHeadAdaptedBasis_bilin 0 2,
    S.sourceHeadAdaptedBasis_bilin 1 2]
  simp
  ring

/-- Exact relative-scale membership implies maximal-ideal membership. -/
theorem isInMaximalIdeal_of_mem_relativeSecondScaleIdeal
    {z : K}
    (hz : z ∈ principalIdeal (K := K) (S.relativeSecondScale : K)) :
    IsInMaximalIdeal K z := by
  rw [principalIdeal_eq_powerIdeal, mem_powerIdeal_iff] at hz
  have hrelative := S.relativeSecondScale_isInMaximalIdeal
  rw [IsInMaximalIdeal, ← coe_ordUnit] at hrelative
  rw [IsInMaximalIdeal]
  exact hrelative.trans_le hz

/-- The last orthogonalized projected vector has negative quadratic value
in the second target fundamental norm group.  The source lift uses exactly
the two Cramer coefficients; their relative-scale divisibility is what
makes the source error a second-tail norm. -/
theorem neg_orthogonalizedProjectedAdaptedBasis_three_quadratic_mem_targetFundamentalNormGroup_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    -(S.targetJordan.component 0).space.quadratic
        (S.orthogonalizedProjectedAdaptedBasis f 3) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  let alpha := S.projectedOrthogonalCoefficientZero f
    (S.projectedAdaptedBasis f 3)
  let beta := S.projectedOrthogonalCoefficientOne f
    (S.projectedAdaptedBasis f 3)
  let x := S.sourceHeadAdaptedBasis 3 +
    alpha • S.sourceHeadAdaptedBasis 0 +
    beta • S.sourceHeadAdaptedBasis 1
  have htail : Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) := by
    ext
    rfl
  have halpha : alpha ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
    dsimp only [alpha]
    simpa only [htail] using
      S.projectedOrthogonalCoefficientZero_tail_mem f (1 : Fin 2)
  have hbeta : beta ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
    dsimp only [beta]
    simpa only [htail] using
      S.projectedOrthogonalCoefficientOne_tail_mem f (1 : Fin 2)
  have hb0 : S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 0 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨0, rfl⟩
  have hb1 : S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 1 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨1, rfl⟩
  have hb3 : S.sourceHeadAdaptedBasis 3 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 3 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨3, rfl⟩
  let alphaO : IntegerRing K := ⟨alpha,
    S.mem_integerRing_of_mem_relativeSecondScaleIdeal halpha⟩
  let betaO : IntegerRing K := ⟨beta,
    S.mem_integerRing_of_mem_relativeSecondScaleIdeal hbeta⟩
  have halphaSmul : alpha • S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    change (alphaO : K) • S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice
    exact (S.sourceJordan.component 0).lattice.smul_mem alphaO hb0
  have hbetaSmul : beta • S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    change (betaO : K) • S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice
    exact (S.sourceJordan.component 0).lattice.smul_mem betaO hb1
  have hx : x ∈ (S.sourceJordan.component 0).lattice := by
    dsimp only [x]
    exact (S.sourceJordan.component 0).lattice.add_mem
      ((S.sourceJordan.component 0).lattice.add_mem hb3 halphaSmul)
      hbetaSmul
  have hxSource : (S.sourceJordan.component 0).space.quadratic x ∈
      S.sourceJordan.fundamentalNormGroup 1 := by
    dsimp only [x]
    rw [S.sourceAdaptedThree_add_firstPlane_quadratic]
    exact S.sourceAdaptedFirstPlane_quadratic_mem_fundamentalNormGroup_one
      halpha hbeta
  have hgroups : S.targetJordan.fundamentalNormGroup 1 =
      S.sourceJordan.fundamentalNormGroup 1 := by
    simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
      S.residualFundamentalType.normGroup_eq (1 : Fin (n + 2))
  have hxTarget : (S.sourceJordan.component 0).space.quadratic x ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    rw [hgroups]
    exact hxSource
  have hprojection : S.firstProjectionMap f x =
      S.orthogonalizedProjectedAdaptedBasis f 3 := by
    dsimp only [x]
    simp only [map_add, map_smul]
    rw [S.orthogonalizedProjectedAdaptedBasis_three]
    have hprojected (i : Fin 4) :
        S.firstProjectionMap f (S.sourceHeadAdaptedBasis i) =
          S.projectedAdaptedBasis f i := by
      exact (S.projectedAdaptedBasis_apply f i).symm
    rw [hprojected 3, hprojected 0, hprojected 1]
    rw [orthogonalizeAgainstProjectedFirstPlane]
  have h :=
    S.neg_firstProjection_quadratic_mem_targetFundamentalNormGroup_one_of_source_mem
      f hx hxTarget
  rw [hprojection] at h
  exact h

/-- The quadratic value of the first vector in the orthogonalized second
binary block differs from the corresponding source norm-generator value
by an element of the second target fundamental norm group. -/
theorem orthogonalizedProjectedAdaptedBasis_two_quadratic_sub_source_two_mem_targetFundamentalNormGroup_one
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.targetJordan.component 0).space.quadratic
          (S.orthogonalizedProjectedAdaptedBasis f 2) -
        (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 2) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  let alpha := S.projectedOrthogonalCoefficientZero f
    (S.projectedAdaptedBasis f 2)
  let beta := S.projectedOrthogonalCoefficientOne f
    (S.projectedAdaptedBasis f 2)
  let correction := alpha • S.sourceHeadAdaptedBasis 0 +
    beta • S.sourceHeadAdaptedBasis 1
  let x := S.sourceHeadAdaptedBasis 2 + correction
  have htail : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by
    ext
    rfl
  have halpha : alpha ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
    dsimp only [alpha]
    simpa only [htail] using
      S.projectedOrthogonalCoefficientZero_tail_mem f (0 : Fin 2)
  have hbeta : beta ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
    dsimp only [beta]
    simpa only [htail] using
      S.projectedOrthogonalCoefficientOne_tail_mem f (0 : Fin 2)
  have hb0 : S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hb1 : S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hb2 : S.sourceHeadAdaptedBasis 2 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    exact Submodule.subset_span ⟨2, rfl⟩
  let alphaO : IntegerRing K := ⟨alpha,
    S.mem_integerRing_of_mem_relativeSecondScaleIdeal halpha⟩
  let betaO : IntegerRing K := ⟨beta,
    S.mem_integerRing_of_mem_relativeSecondScaleIdeal hbeta⟩
  have halphaSmul : alpha • S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    change (alphaO : K) • S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice
    exact (S.sourceJordan.component 0).lattice.smul_mem alphaO hb0
  have hbetaSmul : beta • S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    change (betaO : K) • S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice
    exact (S.sourceJordan.component 0).lattice.smul_mem betaO hb1
  have hx : x ∈ (S.sourceJordan.component 0).lattice := by
    dsimp only [x, correction]
    exact (S.sourceJordan.component 0).lattice.add_mem hb2
      ((S.sourceJordan.component 0).lattice.add_mem halphaSmul hbetaSmul)
  have hcorrectionSource :
      (S.sourceJordan.component 0).space.quadratic correction ∈
        S.sourceJordan.fundamentalNormGroup 1 := by
    dsimp only [correction]
    exact S.sourceAdaptedFirstPlane_quadratic_mem_fundamentalNormGroup_one
      halpha hbeta
  have hgroups : S.targetJordan.fundamentalNormGroup 1 =
      S.sourceJordan.fundamentalNormGroup 1 := by
    simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
      S.residualFundamentalType.normGroup_eq (1 : Fin (n + 2))
  have hcorrectionTarget :
      (S.sourceJordan.component 0).space.quadratic correction ∈
        S.targetJordan.fundamentalNormGroup 1 := by
    rw [hgroups]
    exact hcorrectionSource
  have hprojection : S.firstProjectionMap f x =
      S.orthogonalizedProjectedAdaptedBasis f 2 := by
    dsimp only [x, correction]
    simp only [map_add, map_smul]
    rw [S.orthogonalizedProjectedAdaptedBasis_two]
    have hprojected (i : Fin 4) :
        S.firstProjectionMap f (S.sourceHeadAdaptedBasis i) =
          S.projectedAdaptedBasis f i :=
      (S.projectedAdaptedBasis_apply f i).symm
    rw [hprojected 2, hprojected 0, hprojected 1]
    rw [orthogonalizeAgainstProjectedFirstPlane]
    module
  have hraw :=
    S.firstProjection_quadratic_sub_source_quadratic_mem_targetFundamentalNormGroup_one
      f hx
  have hsum := add_mem_normGroupSet
    (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
    (S.targetJordan.fundamentalLattice 1) hraw hcorrectionTarget
  have hsource : (S.sourceJordan.component 0).space.quadratic x =
      (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 2) +
        (S.sourceJordan.component 0).space.quadratic correction := by
    dsimp only [x, correction]
    simpa only [add_assoc] using
      S.sourceAdaptedTwo_add_firstPlane_quadratic alpha beta
  change (S.targetJordan.component 0).space.quadratic
          (S.orthogonalizedProjectedAdaptedBasis f 2) -
        (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 2) ∈
      normGroupSet
        (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
        (S.targetJordan.fundamentalLattice 1)
  rw [hprojection, hsource] at hsum
  convert hsum using 1 <;> ring

/-- The first projected binary Gram determinant as a nonzero scalar. -/
noncomputable def projectedAdaptedFirstGramUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) : Kˣ :=
  Units.mk0 (S.projectedAdaptedFirstGramMatrix f).det
    (Lattice.ne_zero_of_isValuationUnit
      (S.projectedAdaptedFirstGramDet_isValuationUnit f))

@[simp]
theorem coe_projectedAdaptedFirstGramUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.projectedAdaptedFirstGramUnit f : K) =
      (S.projectedAdaptedFirstGramMatrix f).det :=
  rfl

/-- Equal residual fundamental type identifies the independently chosen
target and source norm-generator orders at every boundary. -/
theorem target_fundamentalNormGenerator_order_eq_source
    (i : Fin (n + 2)) :
    ordUnit K (S.targetJordan.fundamentalNormGenerator i) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator i) := by
  have h :=
    S.residualFundamentalType.fundamentalNormGenerator_order_eq i
  simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using h

/-- In the strict branch, the first projected diagonal coefficient cannot
vanish: its difference from the source norm generator lies in `g₂`, whose
valuation is strictly larger. -/
theorem projectedAdaptedFirstGram_zero_zero_ne_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.projectedAdaptedFirstGramMatrix f 0 0 ≠ 0 := by
  let A : K := S.projectedAdaptedFirstGramMatrix f 0 0
  let c : Kˣ := S.firstScale
  let a : Kˣ := S.firstNormGenerator
  have hb0 : S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 0 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨0, rfl⟩
  have hraw :=
    S.firstProjection_quadratic_sub_source_quadratic_mem_targetFundamentalNormGroup_one
      f hb0
  have htargetValue :
      (S.targetJordan.component 0).space.quadratic
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0)) =
        (c : K) * A := by
    change (S.targetJordan.component 0).space.bilin
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0))
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0)) =
        (c : K) * A
    rw [S.targetFirst_bilin_eq_firstScale_mul_normalized]
    have hzero : Fin.castAdd 2 (0 : Fin 2) = (0 : Fin 4) := by
      ext
      rfl
    simp only [c, A, projectedAdaptedFirstGramMatrix,
      projectedAdaptedBasis_apply, projectedHeadFamily, hzero]
  have hsourceValue :
      (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 0) = ((c * a : Kˣ) : K) := by
    change (S.sourceJordan.component 0).space.bilin
          (S.sourceHeadAdaptedBasis 0) (S.sourceHeadAdaptedBasis 0) =
        ((c * a : Kˣ) : K)
    rw [S.sourceFirst_bilin_eq_firstScale_mul_normalized,
      S.sourceHeadAdaptedBasis_bilin_zero_zero]
    rfl
  have herror : (c : K) * A - ((c * a : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    rw [htargetValue, hsourceValue] at hraw
    exact hraw
  intro hA
  change A = 0 at hA
  have hnegative : -((c * a : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [hA, mul_zero, zero_sub] using herror
  let z : Kˣ := -(c * a)
  have hz : (z : K) ∈ S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [z, Units.val_neg, Units.val_mul] using hnegative
  have hbound := canonicalNormOrder_le_ordUnit_of_mem_normGroupSet
    (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2))) hz
  rw [← ordUnit_eq_canonicalNormOrder
    (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))] at hbound
  have hsourceStrict :
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
    omega
  have htargetStrict :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.targetJordan.fundamentalNormGenerator 1) := by
    rw [S.target_fundamentalNormGenerator_order_eq_source 0,
      S.target_fundamentalNormGenerator_order_eq_source 1]
    exact hsourceStrict
  have hcOrder : ordUnit K c =
      S.sourceJordan.fundamentalScaleOrder 0 := by
    rfl
  have hcaOrder : ordUnit K (c * a) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
    dsimp only [c, a]
    rw [ordUnit_mul, S.firstNormGenerator_order]
    dsimp only [c] at hcOrder
    omega
  have hzOrder : ordUnit K z =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
    dsimp only [z]
    rw [ordUnit_neg, hcaOrder]
  rw [hzOrder] at hbound
  have hbound' :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 1) ≤
        ordUnit K (S.targetJordan.fundamentalNormGenerator 0) := by
    rw [S.target_fundamentalNormGenerator_order_eq_source 0]
    exact hbound
  exact (not_le_of_gt htargetStrict) hbound'

/-- The nonzero first projected diagonal coefficient, packaged as a unit. -/
noncomputable def projectedAdaptedFirstGramZeroUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) : Kˣ :=
  Units.mk0 (S.projectedAdaptedFirstGramMatrix f 0 0)
    (S.projectedAdaptedFirstGram_zero_zero_ne_zero f hgap)

@[simp]
theorem coe_projectedAdaptedFirstGramZeroUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    (S.projectedAdaptedFirstGramZeroUnit f hgap : K) =
      S.projectedAdaptedFirstGramMatrix f 0 0 :=
  rfl

/-- The first projected coefficient has exactly the normalized first norm
order.  The error is either zero or has order at least the second
fundamental norm order, so the ultrametric strict-sum rule applies. -/
theorem projectedAdaptedFirstGramZeroUnit_order_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    ordUnit K (S.projectedAdaptedFirstGramZeroUnit f hgap) =
      ordUnit K S.firstNormGenerator := by
  let A : Kˣ := S.projectedAdaptedFirstGramZeroUnit f hgap
  let c : Kˣ := S.firstScale
  let a : Kˣ := S.firstNormGenerator
  have hb0 : S.sourceHeadAdaptedBasis 0 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 0 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨0, rfl⟩
  have hraw :=
    S.firstProjection_quadratic_sub_source_quadratic_mem_targetFundamentalNormGroup_one
      f hb0
  have htargetValue :
      (S.targetJordan.component 0).space.quadratic
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0)) =
        ((c * A : Kˣ) : K) := by
    change (S.targetJordan.component 0).space.bilin
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0))
          (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 0)) =
        ((c * A : Kˣ) : K)
    rw [S.targetFirst_bilin_eq_firstScale_mul_normalized]
    have hzero : Fin.castAdd 2 (0 : Fin 2) = (0 : Fin 4) := by
      ext
      rfl
    simp only [c, A, projectedAdaptedFirstGramZeroUnit,
      projectedAdaptedFirstGramMatrix, projectedAdaptedBasis_apply,
      projectedHeadFamily, Units.val_mk0, hzero, Units.val_mul]
  have hsourceValue :
      (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 0) = ((c * a : Kˣ) : K) := by
    change (S.sourceJordan.component 0).space.bilin
          (S.sourceHeadAdaptedBasis 0) (S.sourceHeadAdaptedBasis 0) =
        ((c * a : Kˣ) : K)
    rw [S.sourceFirst_bilin_eq_firstScale_mul_normalized,
      S.sourceHeadAdaptedBasis_bilin_zero_zero]
    rfl
  have herror : ((c * A : Kˣ) : K) - ((c * a : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    rw [htargetValue, hsourceValue] at hraw
    exact hraw
  by_cases he : ((c * A : Kˣ) : K) - ((c * a : Kˣ) : K) = 0
  · have heq : c * A = c * a := by
      apply Units.ext
      exact sub_eq_zero.mp he
    have hA : A = a := mul_left_cancel heq
    simpa only [A, a] using congrArg (ordUnit K) hA
  · let error : Kˣ := Units.mk0
        (((c * A : Kˣ) : K) - ((c * a : Kˣ) : K)) he
    have herrorMem : (error : K) ∈
        S.targetJordan.fundamentalNormGroup 1 := by
      simpa only [error, Units.val_mk0] using herror
    have hbound := canonicalNormOrder_le_ordUnit_of_mem_normGroupSet
      (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))
      herrorMem
    rw [← ordUnit_eq_canonicalNormOrder
      (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))] at hbound
    have hsourceStrict :
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
          ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
      have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
      omega
    have htargetStrict :
        ordUnit K (S.targetJordan.fundamentalNormGenerator 0) <
          ordUnit K (S.targetJordan.fundamentalNormGenerator 1) := by
      rw [S.target_fundamentalNormGenerator_order_eq_source 0,
        S.target_fundamentalNormGenerator_order_eq_source 1]
      exact hsourceStrict
    have hcOrder : ordUnit K c =
        S.sourceJordan.fundamentalScaleOrder 0 := by
      rfl
    have hcaOrder : ordUnit K (c * a) =
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
      dsimp only [c, a]
      rw [ordUnit_mul, S.firstNormGenerator_order]
      dsimp only [c] at hcOrder
      omega
    have hmainLt : ordUnit K (c * a) < ordUnit K error := by
      rw [hcaOrder]
      exact hsourceStrict.trans_le
        ((S.target_fundamentalNormGenerator_order_eq_source 1).ge.trans hbound)
    have hmainLtTop : ord K ((c * a : Kˣ) : K) < ord K (error : K) := by
      rw [← coe_ordUnit, ← coe_ordUnit]
      exact WithTop.coe_lt_coe.mpr hmainLt
    have hfield : ((c * A : Kˣ) : K) =
        ((c * a : Kˣ) : K) + (error : K) := by
      dsimp only [error]
      simp only [Units.val_mk0]
      ring
    have hactual : ordUnit K (c * A) = ordUnit K (c * a) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit, hfield]
      exact (ord K).map_add_eq_of_lt_left hmainLtTop
    dsimp only [c, A, a] at hactual ⊢
    rw [ordUnit_mul, ordUnit_mul] at hactual
    omega

/-- The first projected diagonal value is a norm generator of the
normalized target first component. -/
theorem projectedAdaptedFirstGramZeroUnit_isNormGeneratorValue
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      (S.projectedAdaptedFirstGramZeroUnit f hgap) := by
  let y := S.projectedAdaptedBasis f 0
  have hy : y ∈ (S.targetJordan.component 0).lattice := by
    simpa only [y] using S.projectedAdaptedBasis_mem f 0
  constructor
  · refine ⟨y, hy, 0, Submodule.zero_mem _, ?_⟩
    simp only [add_zero]
    change S.targetFirstNormalized.bilin y y =
      (S.projectedAdaptedFirstGramZeroUnit f hgap : K)
    have hzero : Fin.castAdd 2 (0 : Fin 2) = (0 : Fin 4) := by
      ext
      rfl
    simp only [y, coe_projectedAdaptedFirstGramZeroUnit,
      projectedAdaptedFirstGramMatrix, hzero]
  · calc
      normIdeal S.targetFirstNormalized
          (S.targetJordan.component 0).lattice =
          principalIdeal (K := K) (S.firstNormGenerator : K) :=
        S.firstNormGenerator_target.2
      _ = principalIdeal (K := K)
          (S.projectedAdaptedFirstGramZeroUnit f hgap : K) := by
        apply (principalIdeal_eq_iff_ordUnit_eq _ _).2
        exact (S.projectedAdaptedFirstGramZeroUnit_order_eq f hgap).symm

/-- A normalized scalar whose actual value differs from an actual first
norm-generator value by `g₂` is nonzero in the strict branch. -/
theorem normalizedTargetValue_ne_zero_of_actual_sub_mem_second
    (b : Kˣ)
    (hbOrder : ordUnit K b = ordUnit K S.firstNormGenerator)
    {z : K}
    (herror : (S.firstScale : K) * z -
        ((S.firstScale * b : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1)
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    z ≠ 0 := by
  intro hz
  have hnegative : -((S.firstScale * b : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [hz, mul_zero, zero_sub] using herror
  let error : Kˣ := -(S.firstScale * b)
  have herrorMem : (error : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [error, Units.val_neg, Units.val_mul] using hnegative
  have hbound := canonicalNormOrder_le_ordUnit_of_mem_normGroupSet
    (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))
    herrorMem
  rw [← ordUnit_eq_canonicalNormOrder
    (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))] at hbound
  have hsourceStrict :
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
    omega
  have htargetStrict :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.targetJordan.fundamentalNormGenerator 1) := by
    rw [S.target_fundamentalNormGenerator_order_eq_source 0,
      S.target_fundamentalNormGenerator_order_eq_source 1]
    exact hsourceStrict
  have hbActualOrder : ordUnit K (S.firstScale * b) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
    rw [ordUnit_mul, hbOrder, S.firstNormGenerator_order]
    change ordUnit K S.firstScale +
        (ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) -
          S.sourceJordan.fundamentalScaleOrder 0) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0)
    have hc : ordUnit K S.firstScale =
        S.sourceJordan.fundamentalScaleOrder 0 := rfl
    omega
  have herrorOrder : ordUnit K error =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
    dsimp only [error]
    rw [ordUnit_neg, hbActualOrder]
  rw [herrorOrder] at hbound
  have hbound' :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 1) ≤
        ordUnit K (S.targetJordan.fundamentalNormGenerator 0) := by
    rw [S.target_fundamentalNormGenerator_order_eq_source 0]
    exact hbound
  exact (not_le_of_gt htargetStrict) hbound'

/-- Under the same `g₂` approximation, the packaged normalized target
value has the same order as the source norm generator. -/
theorem normalizedTargetValueUnit_order_eq_of_actual_sub_mem_second
    (b : Kˣ)
    (hbOrder : ordUnit K b = ordUnit K S.firstNormGenerator)
    {z : K} (hz : z ≠ 0)
    (herror : (S.firstScale : K) * z -
        ((S.firstScale * b : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1)
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    ordUnit K (Units.mk0 z hz) = ordUnit K b := by
  let zUnit : Kˣ := Units.mk0 z hz
  let c : Kˣ := S.firstScale
  have herror' : ((c * zUnit : Kˣ) : K) - ((c * b : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [c, zUnit, Units.val_mul, Units.val_mk0] using herror
  by_cases he : ((c * zUnit : Kˣ) : K) - ((c * b : Kˣ) : K) = 0
  · have heq : c * zUnit = c * b := by
      apply Units.ext
      exact sub_eq_zero.mp he
    have hzEq : zUnit = b := mul_left_cancel heq
    simpa only [zUnit] using congrArg (ordUnit K) hzEq
  · let error : Kˣ := Units.mk0
        (((c * zUnit : Kˣ) : K) - ((c * b : Kˣ) : K)) he
    have herrorMem : (error : K) ∈
        S.targetJordan.fundamentalNormGroup 1 := by
      simpa only [error, Units.val_mk0] using herror'
    have hbound := canonicalNormOrder_le_ordUnit_of_mem_normGroupSet
      (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))
      herrorMem
    rw [← ordUnit_eq_canonicalNormOrder
      (S.targetJordan.fundamentalNormGenerator_spec (1 : Fin (n + 2)))] at hbound
    have hsourceStrict :
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
          ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
      have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
      omega
    have hcBOrder : ordUnit K (c * b) =
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
      dsimp only [c]
      rw [ordUnit_mul, hbOrder, S.firstNormGenerator_order]
      have hc : ordUnit K S.firstScale =
          S.sourceJordan.fundamentalScaleOrder 0 := rfl
      omega
    have hmainLt : ordUnit K (c * b) < ordUnit K error := by
      rw [hcBOrder]
      exact hsourceStrict.trans_le
        ((S.target_fundamentalNormGenerator_order_eq_source 1).ge.trans hbound)
    have hmainLtTop : ord K ((c * b : Kˣ) : K) < ord K (error : K) := by
      rw [← coe_ordUnit, ← coe_ordUnit]
      exact WithTop.coe_lt_coe.mpr hmainLt
    have hfield : ((c * zUnit : Kˣ) : K) =
        ((c * b : Kˣ) : K) + (error : K) := by
      dsimp only [error]
      simp only [Units.val_mk0]
      ring
    have hactual : ordUnit K (c * zUnit) = ordUnit K (c * b) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit, hfield]
      exact (ord K).map_add_eq_of_lt_left hmainLtTop
    dsimp only [c, zUnit] at hactual ⊢
    rw [ordUnit_mul, ordUnit_mul] at hactual
    omega

/-- The auxiliary source coefficient in the third adapted vector has the
same order as the normalized first norm generator. -/
theorem sourceHeadAdaptedSecondCoefficient_order_eq :
    ordUnit K S.sourceHeadAdaptedModelData.secondCoefficient =
      ordUnit K S.firstNormGenerator := by
  exact (principalIdeal_eq_iff_ordUnit_eq
    S.sourceHeadAdaptedModelData.secondCoefficient
    S.firstNormGenerator).1
      S.sourceHeadAdaptedModelData.secondCoefficientIdeal_eq

/-- Actual-value form of the `g₂` approximation for the first vector of
the orthogonalized second binary block. -/
theorem firstScale_mul_orthogonalizedSecondGram_zero_zero_sub_mem_second
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.firstScale : K) * S.orthogonalizedSecondGramMatrix f 0 0 -
        ((S.firstScale *
          S.sourceHeadAdaptedModelData.secondCoefficient : Kˣ) : K) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
  have hraw :=
    S.orthogonalizedProjectedAdaptedBasis_two_quadratic_sub_source_two_mem_targetFundamentalNormGroup_one
      f
  have htwo : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by
    ext
    rfl
  have htargetValue :
      (S.targetJordan.component 0).space.quadratic
          (S.orthogonalizedProjectedAdaptedBasis f 2) =
        (S.firstScale : K) *
          S.orthogonalizedSecondGramMatrix f 0 0 := by
    change (S.targetJordan.component 0).space.bilin
          (S.orthogonalizedProjectedAdaptedBasis f 2)
          (S.orthogonalizedProjectedAdaptedBasis f 2) = _
    rw [S.targetFirst_bilin_eq_firstScale_mul_normalized]
    simp only [orthogonalizedSecondGramMatrix, htwo]
  have hsourceValue :
      (S.sourceJordan.component 0).space.quadratic
          (S.sourceHeadAdaptedBasis 2) =
        ((S.firstScale *
          S.sourceHeadAdaptedModelData.secondCoefficient : Kˣ) : K) := by
    change (S.sourceJordan.component 0).space.bilin
          (S.sourceHeadAdaptedBasis 2) (S.sourceHeadAdaptedBasis 2) = _
    rw [S.sourceFirst_bilin_eq_firstScale_mul_normalized,
      S.sourceHeadAdaptedBasis_bilin_two_two]
    rfl
  rw [htargetValue, hsourceValue] at hraw
  exact hraw

/-- The first diagonal coefficient of the orthogonalized second block is
nonzero in the strict branch. -/
theorem orthogonalizedSecondGram_zero_zero_ne_zero
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    S.orthogonalizedSecondGramMatrix f 0 0 ≠ 0 := by
  exact S.normalizedTargetValue_ne_zero_of_actual_sub_mem_second
    S.sourceHeadAdaptedModelData.secondCoefficient
    S.sourceHeadAdaptedSecondCoefficient_order_eq
    (S.firstScale_mul_orthogonalizedSecondGram_zero_zero_sub_mem_second f)
    hgap

/-- The nonzero third projected diagonal coefficient, packaged as a unit. -/
noncomputable def orthogonalizedSecondGramZeroUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) : Kˣ :=
  Units.mk0 (S.orthogonalizedSecondGramMatrix f 0 0)
    (S.orthogonalizedSecondGram_zero_zero_ne_zero f hgap)

@[simp]
theorem coe_orthogonalizedSecondGramZeroUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    (S.orthogonalizedSecondGramZeroUnit f hgap : K) =
      S.orthogonalizedSecondGramMatrix f 0 0 :=
  rfl

theorem orthogonalizedSecondGramZeroUnit_order_eq
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    ordUnit K (S.orthogonalizedSecondGramZeroUnit f hgap) =
      ordUnit K S.firstNormGenerator := by
  have horder :=
    S.normalizedTargetValueUnit_order_eq_of_actual_sub_mem_second
      S.sourceHeadAdaptedModelData.secondCoefficient
      S.sourceHeadAdaptedSecondCoefficient_order_eq
      (S.orthogonalizedSecondGram_zero_zero_ne_zero f hgap)
      (S.firstScale_mul_orthogonalizedSecondGram_zero_zero_sub_mem_second f)
      hgap
  exact horder.trans S.sourceHeadAdaptedSecondCoefficient_order_eq

/-- The third projected diagonal value is likewise a norm generator of
the normalized target first component. -/
theorem orthogonalizedSecondGramZeroUnit_isNormGeneratorValue
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    IsNormGeneratorValue S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      (S.orthogonalizedSecondGramZeroUnit f hgap) := by
  let y := S.orthogonalizedProjectedAdaptedBasis f 2
  have hy : y ∈ (S.targetJordan.component 0).lattice := by
    dsimp only [y]
    rw [S.orthogonalizedProjectedAdaptedBasis_apply]
    exact S.orthogonalizedProjectedAdaptedFamily_mem f 2
  constructor
  · refine ⟨y, hy, 0, Submodule.zero_mem _, ?_⟩
    simp only [add_zero]
    change S.targetFirstNormalized.bilin y y =
      (S.orthogonalizedSecondGramZeroUnit f hgap : K)
    have htwo : Fin.natAdd 2 (0 : Fin 2) = (2 : Fin 4) := by
      ext
      rfl
    simp only [y, coe_orthogonalizedSecondGramZeroUnit,
      orthogonalizedSecondGramMatrix, htwo]
  · calc
      normIdeal S.targetFirstNormalized
          (S.targetJordan.component 0).lattice =
          principalIdeal (K := K) (S.firstNormGenerator : K) :=
        S.firstNormGenerator_target.2
      _ = principalIdeal (K := K)
          (S.orthogonalizedSecondGramZeroUnit f hgap : K) := by
        apply (principalIdeal_eq_iff_ordUnit_eq _ _).2
        exact (S.orthogonalizedSecondGramZeroUnit_order_eq f hgap).symm

/-- The determinant of the orthogonalized second binary block is a
valuation unit. -/
theorem orthogonalizedSecondGramDet_isValuationUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    IsValuationUnit K (S.orthogonalizedSecondGramMatrix f).det := by
  apply isValuationUnit_of_sub_isInMaximalIdeal
    (b := (-1 : K))
  · simp [IsValuationUnit]
  · exact S.isInMaximalIdeal_of_mem_relativeSecondScaleIdeal
      (S.orthogonalizedSecondGramDet_sub_negOne_mem_relativeSecondScaleIdeal f)

/-- The orthogonalized second binary determinant as a nonzero scalar. -/
noncomputable def orthogonalizedSecondGramUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) : Kˣ :=
  Units.mk0 (S.orthogonalizedSecondGramMatrix f).det
    (Lattice.ne_zero_of_isValuationUnit
      (S.orthogonalizedSecondGramDet_isValuationUnit f))

@[simp]
theorem coe_orthogonalizedSecondGramUnit
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.orthogonalizedSecondGramUnit f : K) =
      (S.orthogonalizedSecondGramMatrix f).det :=
  rfl

/-- The determinant formula for the orthogonalized second binary block. -/
theorem orthogonalizedSecondGramDet_formula
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    (S.orthogonalizedSecondGramMatrix f).det =
      S.orthogonalizedSecondGramMatrix f 0 0 *
        S.orthogonalizedSecondGramMatrix f 1 1 -
      S.orthogonalizedSecondGramMatrix f 0 1 ^ 2 := by
  rw [Matrix.det_fin_two]
  have hsymm : S.orthogonalizedSecondGramMatrix f 1 0 =
      S.orthogonalizedSecondGramMatrix f 0 1 := by
    unfold orthogonalizedSecondGramMatrix
    exact S.targetFirstNormalized.isSymm.eq _ _
  rw [hsymm]
  ring

/-- Orthogonality of the two corrected binary blocks factors the full
rank-four Gram determinant literally as the product of their determinants. -/
theorem orthogonalizedGramUnit_eq_mul_binaryGramUnits
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    gramUnitOfBasis S.targetFirstNormalized
        (S.orthogonalizedProjectedAdaptedBasis f) =
      S.projectedAdaptedFirstGramUnit f *
        S.orthogonalizedSecondGramUnit f := by
  let G : Matrix (Fin 4) (Fin 4) K :=
    LinearMap.BilinForm.toMatrix
      (S.orthogonalizedProjectedAdaptedBasis f)
      S.targetFirstNormalized.bilin
  let A : Matrix (Fin 2) (Fin 2) K :=
    S.projectedAdaptedFirstGramMatrix f
  let D : Matrix (Fin 2) (Fin 2) K :=
    S.orthogonalizedSecondGramMatrix f
  let e : Fin 4 ≃ (Fin 2 ⊕ Fin 2) :=
    (finSumFinEquiv (m := 2) (n := 2)).symm
  have hfirst (i : Fin 2) :
      S.orthogonalizedProjectedAdaptedBasis f (Fin.castAdd 2 i) =
        S.projectedAdaptedBasis f (Fin.castAdd 2 i) := by
    fin_cases i <;> simp
  have hcross (i j : Fin 2) :
      S.targetFirstNormalized.bilin
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.castAdd 2 i))
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 j)) = 0 := by
    fin_cases i <;> fin_cases j
    · exact S.orthogonalizedProjectedAdaptedBasis_bilin_zero_two f
    · exact S.orthogonalizedProjectedAdaptedBasis_bilin_zero_three f
    · exact S.orthogonalizedProjectedAdaptedBasis_bilin_one_two f
    · exact S.orthogonalizedProjectedAdaptedBasis_bilin_one_three f
  have hcrossReverse (i j : Fin 2) :
      S.targetFirstNormalized.bilin
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 i))
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.castAdd 2 j)) = 0 := by
    rw [S.targetFirstNormalized.isSymm.eq]
    exact hcross j i
  have hblock : Matrix.reindex e e G =
      Matrix.fromBlocks A 0 0 D := by
    ext (i | i) (j | j)
    · simp only [e, G, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, finSumFinEquiv_apply_left,
        Matrix.fromBlocks_apply₁₁, LinearMap.BilinForm.toMatrix_apply]
      change S.targetFirstNormalized.bilin
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.castAdd 2 i))
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.castAdd 2 j)) =
        S.targetFirstNormalized.bilin
          (S.projectedAdaptedBasis f (Fin.castAdd 2 i))
          (S.projectedAdaptedBasis f (Fin.castAdd 2 j))
      rw [hfirst i, hfirst j]
    · simp only [e, G, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, LinearMap.BilinForm.toMatrix_apply]
      exact hcross i j
    · simp only [e, G, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, LinearMap.BilinForm.toMatrix_apply]
      exact hcrossReverse i j
    · simp only [e, G, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, finSumFinEquiv_apply_right,
        Matrix.fromBlocks_apply₂₂, LinearMap.BilinForm.toMatrix_apply]
      change S.targetFirstNormalized.bilin
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 i))
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 j)) =
        S.targetFirstNormalized.bilin
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 i))
          (S.orthogonalizedProjectedAdaptedBasis f (Fin.natAdd 2 j))
      rfl
  apply Units.ext
  change G.det = A.det * D.det
  calc
    G.det = (Matrix.reindex e e G).det :=
      (Matrix.det_reindex_self e G).symm
    _ = A.det * D.det := by
      rw [hblock, Matrix.det_fromBlocks_zero₂₁]

/-- In the strict norm-order branch of Step 1, the first projected binary
discriminant is congruent to `-1` modulo the actual first fundamental
ideal. -/
theorem projectedAdaptedFirstGramUnit_congruent_negOne_of_strictNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.projectedAdaptedFirstGramUnit f) (-1 : Kˣ)
      (S.sourceJordan.fundamentalIdeal 0) := by
  let y := S.projectedAdaptedBasis f
  let A : K := S.projectedAdaptedFirstGramMatrix f 0 0
  let B : K := S.projectedAdaptedFirstGramMatrix f 0 1
  let C : K := S.projectedAdaptedFirstGramMatrix f 1 1
  let D : K := (S.projectedAdaptedFirstGramMatrix f).det
  let c : Kˣ := S.firstScale
  have hy0 : y 0 ∈ (S.targetJordan.component 0).lattice := by
    simpa only [y] using S.projectedAdaptedBasis_mem f 0
  have hy1 : y 1 ∈ (S.targetJordan.component 0).lattice := by
    simpa only [y] using S.projectedAdaptedBasis_mem f 1
  have hxComponent : (S.targetJordan.component 0).space.quadratic (y 0) ∈
      normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice := by
    exact ⟨y 0, hy0, 0, Submodule.zero_mem _, by simp⟩
  have hxFundamental : (S.targetJordan.component 0).space.quadratic (y 0) ∈
      S.targetJordan.fundamentalNormGroup 0 := by
    rw [← S.targetJordan_isSaturated 0]
    exact hxComponent
  have hx : (c : K) * A ∈
      S.targetJordan.fundamentalNormGroup 0 := by
    convert hxFundamental using 1
    change (c : K) *
        S.targetFirstNormalized.bilin (y 0) (y 0) =
      (S.targetJordan.component 0).space.bilin (y 0) (y 0)
    exact (S.targetFirst_bilin_eq_firstScale_mul_normalized (y 0) (y 0)).symm
  have hb1 : S.sourceHeadAdaptedBasis 1 ∈
      (S.sourceJordan.component 0).lattice := by
    rw [← S.sourceHeadAdaptedBasisLattice_eq]
    change S.sourceHeadAdaptedBasis 1 ∈
      Submodule.span (IntegerRing K) (Set.range S.sourceHeadAdaptedBasis)
    exact Submodule.subset_span ⟨1, rfl⟩
  have hb1NormalizedIso : S.sourceFirstNormalized.quadratic
      (S.sourceHeadAdaptedBasis 1) = 0 := by
    change S.sourceFirstNormalized.bilin
      (S.sourceHeadAdaptedBasis 1) (S.sourceHeadAdaptedBasis 1) = 0
    simpa using S.sourceHeadAdaptedBasis_bilin 1 1
  have hb1Iso : (S.sourceJordan.component 0).space.quadratic
      (S.sourceHeadAdaptedBasis 1) = 0 := by
    change ((S.firstScale⁻¹ : Kˣ) : K) *
      (S.sourceJordan.component 0).space.bilin
        (S.sourceHeadAdaptedBasis 1) (S.sourceHeadAdaptedBasis 1) = 0 at hb1NormalizedIso
    exact (mul_eq_zero.mp hb1NormalizedIso).resolve_left
      (Units.ne_zero (S.firstScale⁻¹))
  have hzProjected :=
    S.neg_firstProjection_quadratic_mem_targetFundamentalNormGroup_one
      f hb1 hb1Iso
  have hy1Eq : y 1 =
      S.firstProjectionMap f (S.sourceHeadAdaptedBasis 1) := by
    simp only [y, projectedAdaptedBasis_apply, projectedHeadFamily]
  have hz : -((c : K) * C) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    convert hzProjected using 1
    change -((c : K) * S.targetFirstNormalized.bilin (y 1) (y 1)) =
      -(S.targetJordan.component 0).space.bilin
        (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 1))
        (S.firstProjectionMap f (S.sourceHeadAdaptedBasis 1))
    rw [S.targetFirst_bilin_eq_firstScale_mul_normalized]
    rw [hy1Eq]
  have hli : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by ext; rfl
  have hri : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by ext; rfl
  have hpActual : (S.targetJordan.component 0).space.bilin (y 0) (y 1) ∈
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) := by
    rw [← S.targetJordan.scaleIdeal_eq 0]
    exact bilin_mem_scaleIdeal_of_mem
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice hy0 hy1
  have hp : (c : K) * B ∈
      principalIdeal (K := K)
        (S.targetJordan.scaleGenerator (boundaryLeftIndex 0) : K) := by
    have hpEq : (c : K) * B =
        (S.targetJordan.component 0).space.bilin (y 0) (y 1) := by
      change (c : K) * S.targetFirstNormalized.bilin (y 0) (y 1) =
        (S.targetJordan.component 0).space.bilin (y 0) (y 1)
      exact (S.targetFirst_bilin_eq_firstScale_mul_normalized (y 0) (y 1)).symm
    rw [hpEq]
    simpa only [hli] using hpActual
  have hsourceStrict :
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
    omega
  have targetGeneratorOrder_eq_source (i : Fin (n + 2)) :
      ordUnit K (S.targetJordan.fundamentalNormGenerator i) =
        ordUnit K (S.sourceJordan.fundamentalNormGenerator i) := by
    have htarget := S.targetJordan.fundamentalNormGenerator_spec i
    have hsourceOnTarget :=
      S.residualFundamentalType.fundamentalNormGenerator_spec_right i
    have hideal : principalIdeal (K := K)
          (S.targetJordan.fundamentalNormGenerator i : K) =
        principalIdeal (K := K)
          (S.sourceJordan.fundamentalNormGenerator i : K) :=
      htarget.2.symm.trans hsourceOnTarget.2
    exact (principalIdeal_eq_iff_ordUnit_eq
      (S.targetJordan.fundamentalNormGenerator i)
      (S.sourceJordan.fundamentalNormGenerator i)).1 hideal
  have htargetStrict :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.targetJordan.fundamentalNormGenerator 1) := by
    rw [targetGeneratorOrder_eq_source 0,
      targetGeneratorOrder_eq_source 1]
    exact hsourceStrict
  have hBsub : IsInMaximalIdeal K (B - 1) := by
    have h :=
      S.projectedAdaptedFirstGramMatrix_sub_source_isInMaximalIdeal f 0 1
    have hsource : S.sourceAdaptedFirstGramMatrix 0 1 = (1 : K) := by
      rw [S.sourceAdaptedFirstGramMatrix_eq]
      rfl
    simpa only [B, hsource] using h
  have hBunit : IsValuationUnit K B :=
    isValuationUnit_of_sub_isInMaximalIdeal
      (b := (1 : K)) (by simp [IsValuationUnit]) hBsub
  have hpOrder : ord K ((c : K) * B) =
      ((S.targetJordan.fundamentalScaleOrder
        (boundaryLeftIndex (0 : Fin (n + 1))) : Int) : WithTop Int) := by
    rw [ord_mul, ← coe_ordUnit, hBunit]
    simp only [add_zero, fundamentalScaleOrder,
      targetJordan_scaleGenerator, c, firstScale, hli]
  rcases S.targetJordan
      |>.exists_binaryDeterminant_squareAdjuster_mem_scaledFundamentalIdeal_with_order
        (0 : Fin (n + 1)) hx hz hp with ⟨rho, hrho, hrhoOrder⟩
  have hrhoOrder' : ord K rho =
      ((S.targetJordan.fundamentalScaleOrder 0 : Int) : WithTop Int) := by
    apply hrhoOrder
    · simpa only [hli, hri] using htargetStrict
    · simpa using hpOrder
  have hDformula : D = A * C - B ^ 2 := by
    have hzero : Fin.castAdd 2 (0 : Fin 2) = (0 : Fin 4) := by ext; rfl
    have hone : Fin.castAdd 2 (1 : Fin 2) = (1 : Fin 4) := by ext; rfl
    simpa only [D, A, B, C, projectedAdaptedFirstGramMatrix,
      hzero, hone] using
      S.projectedAdaptedFirstGramDet_formula f
  have hrho' : ((S.targetJordan.scaleGenerator 0 : K) ^ 2) * D + rho ^ 2 ∈
      S.targetJordan.scaledFundamentalIdeal 0 := by
    convert hrho using 1
    · rw [hDformula]
      simp only [c, firstScale, targetJordan_scaleGenerator]
      ring
  have hnormalizedTarget :=
    S.targetJordan.normalized_binaryError_mem_fundamentalIdeal
      (0 : Fin (n + 1)) hrho'
  have hnormalized :
      D + ((((S.targetJordan.scaleGenerator 0)⁻¹ : Kˣ) : K) * rho) ^ 2 ∈
        S.sourceJordan.fundamentalIdeal 0 := by
    rw [← S.residualFundamentalType.fundamentalIdeal_eq 0]
    exact hnormalizedTarget
  let tau : K := (((S.targetJordan.scaleGenerator 0)⁻¹ : Kˣ) : K) * rho
  have htauOrder : ord K tau = 0 := by
    dsimp only [tau]
    rw [ord_mul, ← coe_ordUnit, ordUnit_inv, hrhoOrder']
    simp only [fundamentalScaleOrder]
    norm_cast
    omega
  have htauNe : tau ≠ 0 := by
    intro htau
    rw [htau, ord_zero] at htauOrder
    exact WithTop.top_ne_zero htauOrder
  let tauUnit : Kˣ := Units.mk0 tau htauNe
  have htauUnit : IsValuationUnit K (tauUnit : K) := by
    unfold IsValuationUnit
    simpa only [tauUnit, Units.val_mk0] using htauOrder
  have hDunit : IsValuationUnit K
      (S.projectedAdaptedFirstGramUnit f : K) := by
    simpa only [coe_projectedAdaptedFirstGramUnit] using
      S.projectedAdaptedFirstGramDet_isValuationUnit f
  apply BONG.GoodBONG.unitsCongruentModulo_neg_one_of_add_sq_mem
    (S.projectedAdaptedFirstGramUnit f) tauUnit
    (S.sourceJordan.fundamentalIdeal 0) hDunit
  simpa only [coe_projectedAdaptedFirstGramUnit, D, tauUnit,
    Units.val_mk0, tau] using hnormalized

/-- In the strict norm-order branch of Step 1, the orthogonalized second
binary discriminant is also congruent to `-1` modulo the actual first
fundamental ideal. -/
theorem orthogonalizedSecondGramUnit_congruent_negOne_of_strictNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.orthogonalizedSecondGramUnit f) (-1 : Kˣ)
      (S.sourceJordan.fundamentalIdeal 0) := by
  let y := S.orthogonalizedProjectedAdaptedBasis f
  let x := y (Fin.natAdd 2 (0 : Fin 2))
  let z := y (Fin.natAdd 2 (1 : Fin 2))
  let A : K := S.orthogonalizedSecondGramMatrix f 0 0
  let B : K := S.orthogonalizedSecondGramMatrix f 0 1
  let C : K := S.orthogonalizedSecondGramMatrix f 1 1
  let D : K := (S.orthogonalizedSecondGramMatrix f).det
  let c : Kˣ := S.firstScale
  have hxMem : x ∈ (S.targetJordan.component 0).lattice := by
    dsimp only [x, y]
    rw [S.orthogonalizedProjectedAdaptedBasis_apply]
    exact S.orthogonalizedProjectedAdaptedFamily_mem f _
  have hzMem : z ∈ (S.targetJordan.component 0).lattice := by
    dsimp only [z, y]
    rw [S.orthogonalizedProjectedAdaptedBasis_apply]
    exact S.orthogonalizedProjectedAdaptedFamily_mem f _
  have hxComponent : (S.targetJordan.component 0).space.quadratic x ∈
      normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice :=
    ⟨x, hxMem, 0, Submodule.zero_mem _, by simp⟩
  have hxFundamental : (S.targetJordan.component 0).space.quadratic x ∈
      S.targetJordan.fundamentalNormGroup 0 := by
    rw [← S.targetJordan_isSaturated 0]
    exact hxComponent
  have hx : (c : K) * A ∈
      S.targetJordan.fundamentalNormGroup 0 := by
    convert hxFundamental using 1
    change (c : K) * S.targetFirstNormalized.bilin x x =
      (S.targetJordan.component 0).space.bilin x x
    exact (S.targetFirst_bilin_eq_firstScale_mul_normalized x x).symm
  have htail : Fin.natAdd 2 (1 : Fin 2) = (3 : Fin 4) := by
    ext
    rfl
  have hzActual :
      -(S.targetJordan.component 0).space.quadratic z ∈
        S.targetJordan.fundamentalNormGroup 1 := by
    simpa only [z, y, htail] using
      S.neg_orthogonalizedProjectedAdaptedBasis_three_quadratic_mem_targetFundamentalNormGroup_one
        f
  have hz : -((c : K) * C) ∈
      S.targetJordan.fundamentalNormGroup 1 := by
    convert hzActual using 1
    change -((c : K) * S.targetFirstNormalized.bilin z z) =
      -(S.targetJordan.component 0).space.bilin z z
    rw [S.targetFirst_bilin_eq_firstScale_mul_normalized]
  have hli : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by ext; rfl
  have hri : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by ext; rfl
  have hpActual : (S.targetJordan.component 0).space.bilin x z ∈
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) := by
    rw [← S.targetJordan.scaleIdeal_eq 0]
    exact bilin_mem_scaleIdeal_of_mem
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice hxMem hzMem
  have hp : (c : K) * B ∈
      principalIdeal (K := K)
        (S.targetJordan.scaleGenerator (boundaryLeftIndex 0) : K) := by
    have hpEq : (c : K) * B =
        (S.targetJordan.component 0).space.bilin x z := by
      change (c : K) * S.targetFirstNormalized.bilin x z =
        (S.targetJordan.component 0).space.bilin x z
      exact (S.targetFirst_bilin_eq_firstScale_mul_normalized x z).symm
    rw [hpEq]
    simpa only [hli] using hpActual
  have hsourceStrict :
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) := by
    have hfundGap := S.normalizedNormOrderGap_eq_fundamentalGap
    omega
  have htargetStrict :
      ordUnit K (S.targetJordan.fundamentalNormGenerator 0) <
        ordUnit K (S.targetJordan.fundamentalNormGenerator 1) := by
    rw [S.target_fundamentalNormGenerator_order_eq_source 0,
      S.target_fundamentalNormGenerator_order_eq_source 1]
    exact hsourceStrict
  have hBsubRelative : B - 1 ∈
      principalIdeal (K := K) (S.relativeSecondScale : K) := by
    have h :=
      S.orthogonalizedSecondGramMatrix_sub_source_mem_relativeSecondScaleIdeal
        f 0 1
    have hsource : S.sourceAdaptedSecondGramMatrix 0 1 = (1 : K) := by
      rw [S.sourceAdaptedSecondGramMatrix_eq]
      rfl
    simpa only [B, hsource] using h
  have hBsub : IsInMaximalIdeal K (B - 1) :=
    S.isInMaximalIdeal_of_mem_relativeSecondScaleIdeal hBsubRelative
  have hBunit : IsValuationUnit K B :=
    isValuationUnit_of_sub_isInMaximalIdeal
      (b := (1 : K)) (by simp [IsValuationUnit]) hBsub
  have hpOrder : ord K ((c : K) * B) =
      ((S.targetJordan.fundamentalScaleOrder
        (boundaryLeftIndex (0 : Fin (n + 1))) : Int) : WithTop Int) := by
    rw [ord_mul, ← coe_ordUnit, hBunit]
    simp only [add_zero, fundamentalScaleOrder,
      targetJordan_scaleGenerator, c, firstScale, hli]
  rcases S.targetJordan
      |>.exists_binaryDeterminant_squareAdjuster_mem_scaledFundamentalIdeal_with_order
        (0 : Fin (n + 1)) hx hz hp with ⟨rho, hrho, hrhoOrder⟩
  have hrhoOrder' : ord K rho =
      ((S.targetJordan.fundamentalScaleOrder 0 : Int) : WithTop Int) := by
    apply hrhoOrder
    · simpa only [hli, hri] using htargetStrict
    · simpa using hpOrder
  have hDformula : D = A * C - B ^ 2 := by
    simpa only [D, A, B, C] using
      S.orthogonalizedSecondGramDet_formula f
  have hrho' : ((S.targetJordan.scaleGenerator 0 : K) ^ 2) * D + rho ^ 2 ∈
      S.targetJordan.scaledFundamentalIdeal 0 := by
    convert hrho using 1
    · rw [hDformula]
      simp only [c, firstScale, targetJordan_scaleGenerator]
      ring
  have hnormalizedTarget :=
    S.targetJordan.normalized_binaryError_mem_fundamentalIdeal
      (0 : Fin (n + 1)) hrho'
  have hnormalized :
      D + ((((S.targetJordan.scaleGenerator 0)⁻¹ : Kˣ) : K) * rho) ^ 2 ∈
        S.sourceJordan.fundamentalIdeal 0 := by
    rw [← S.residualFundamentalType.fundamentalIdeal_eq 0]
    exact hnormalizedTarget
  let tau : K := (((S.targetJordan.scaleGenerator 0)⁻¹ : Kˣ) : K) * rho
  have htauOrder : ord K tau = 0 := by
    dsimp only [tau]
    rw [ord_mul, ← coe_ordUnit, ordUnit_inv, hrhoOrder']
    simp only [fundamentalScaleOrder]
    norm_cast
    omega
  have htauNe : tau ≠ 0 := by
    intro htau
    rw [htau, ord_zero] at htauOrder
    exact WithTop.top_ne_zero htauOrder
  let tauUnit : Kˣ := Units.mk0 tau htauNe
  have htauUnit : IsValuationUnit K (tauUnit : K) := by
    unfold IsValuationUnit
    simpa only [tauUnit, Units.val_mk0] using htauOrder
  have hDunit : IsValuationUnit K
      (S.orthogonalizedSecondGramUnit f : K) := by
    simpa only [coe_orthogonalizedSecondGramUnit] using
      S.orthogonalizedSecondGramDet_isValuationUnit f
  apply BONG.GoodBONG.unitsCongruentModulo_neg_one_of_add_sq_mem
    (S.orthogonalizedSecondGramUnit f) tauUnit
    (S.sourceJordan.fundamentalIdeal 0) hDunit
  simpa only [coe_orthogonalizedSecondGramUnit, D, tauUnit,
    Units.val_mk0, tau] using hnormalized

/-- The two binary congruences multiply to the normalized rank-four
determinant congruence required by 93:28(i). -/
theorem targetFirstNormalized_determinantCongruentOne_of_strictNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice)
      (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0) := by
  have hIdealIntegral : S.sourceJordan.fundamentalIdeal 0 ≤
      unitIdeal (K := K) := by
    intro z hz
    rw [mem_unitIdeal_iff_isIntegral, Dyadic.IsIntegral]
    exact le_of_lt
      (S.sourceJordan.isInMaximalIdeal_of_mem_fundamentalIdeal 0 hz)
  have hfirst :=
    S.projectedAdaptedFirstGramUnit_congruent_negOne_of_strictNormOrder
      f hgap
  have hsecond :=
    S.orthogonalizedSecondGramUnit_congruent_negOne_of_strictNormOrder
      f hgap
  have hproduct := BONG.GoodBONG.unitsCongruentModulo_mul
    hIdealIntegral hfirst hsecond
  have hgram : BONG.GoodBONG.UnitsCongruentModulo
      (gramUnitOfBasis S.targetFirstNormalized
        (S.orthogonalizedProjectedAdaptedBasis f))
      (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0) := by
    rw [S.orthogonalizedGramUnit_eq_mul_binaryGramUnits f]
    simpa using hproduct
  have hclass : unitSquareClass K
      (gramUnitOfBasis S.targetFirstNormalized
        (S.orthogonalizedProjectedAdaptedBasis f)) =
      unitSquareClass K
        (determinantUnit S.targetFirstNormalized
          (S.targetJordan.component 0).lattice) := by
    have h := unitSquareClass_gramUnitOfBasis_eq_determinantClass
      S.targetFirstNormalized (S.orthogonalizedProjectedAdaptedBasis f)
    rw [S.orthogonalizedProjectedAdaptedBasisLattice_eq f] at h
    simpa only [determinantClass] using h
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (gramUnitOfBasis S.targetFirstNormalized
      (S.orthogonalizedProjectedAdaptedBasis f))
    (determinantUnit S.targetFirstNormalized
      (S.targetJordan.component 0).lattice)
    (1 : Kˣ) (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0)
    hclass rfl hgram

/-- O'Meara 93:28(i) at the first unnormalized Jordan boundary in the
strict norm-order branch. -/
theorem firstBoundary_conditionI_of_strictNormOrder
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (hgap : ordUnit K S.firstNormGenerator <
      ordUnit K S.secondNormalizedNormGenerator) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.prefixDeterminantUnit 0)
      (S.sourceJordan.fundamentalIdeal 0) := by
  have hnormalized :=
    S.targetFirstNormalized_determinantCongruentOne_of_strictNormOrder
      f hgap
  let c : Kˣ := S.firstScale ^ 4
  let x : Kˣ := determinantUnit S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  let sourcePrefix : Kˣ := S.sourceJordan.prefixDeterminantUnit 0
  let targetPrefix : Kˣ := S.targetJordan.prefixDeterminantUnit 0
  have htargetClass :
      unitSquareClass K targetPrefix = unitSquareClass K (c * x) := by
    change determinantClass
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * x)
    rw [S.targetFirstPrefix_determinantClass]
    exact (unitSquareClass_mul K c x).symm
  have hsourceClass :
      unitSquareClass K sourcePrefix =
        unitSquareClass K (c * (1 : Kˣ)) := by
    change determinantClass
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).space
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1).lattice =
      unitSquareClass K (c * (1 : Kˣ))
    rw [S.sourceFirstPrefix_determinantClass, mul_one]
  have hscaled : BONG.GoodBONG.UnitsCongruentModulo
      (c * x) (c * (1 : Kˣ))
      (S.sourceJordan.fundamentalIdeal 0) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      c x (1 : Kˣ) (S.sourceJordan.fundamentalIdeal 0)).2 hnormalized
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (c * x) targetPrefix (c * (1 : Kˣ)) sourcePrefix
    (S.sourceJordan.fundamentalIdeal 0)
    htargetClass.symm hsourceClass.symm hscaled

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
