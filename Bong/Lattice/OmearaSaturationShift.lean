/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationGeometry
import Bong.Lattice.JordanReplaceComponent
import Bong.Lattice.OmearaGeneralPlaneChangeOfComplement
import Bong.Lattice.OmearaNormGroupShift
import Bong.Lattice.OmearaStableModularCancellation
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.NormIdealOrthogonalProduct

/-!
# The two coefficient shifts in one O'Meara saturation step

For a Jordan component of rank at least seven, O'Meara 93:21 splits two
scaled hyperbolic planes and changes their first coefficients so that they
represent a fundamental norm generator and a fundamental weight generator.
This file constructs the two 93:13 isometries and packages the resulting
replacement Jordan decomposition.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace JordanDecomposition

variable {t : Nat} (J : JordanDecomposition q L t) (i : Fin t)

/-- Every element of a fundamental norm group is divisible by the scale of
that fundamental layer. -/
theorem scaleInverse_mul_mem_integerRing_of_mem_fundamentalNormGroup
    {z : K} (hz : z ∈ J.fundamentalNormGroup i) :
    ((J.scaleGenerator i : Kˣ)⁻¹ : K) * z ∈ IntegerRing K := by
  have hzNorm : z ∈ normIdeal q (J.fundamentalLattice i) :=
    normGroupSet_subset_normIdeal q (J.fundamentalLattice i) hz
  have hzScale : z ∈ scaleIdeal q (J.fundamentalLattice i) :=
    normIdeal_le_scaleIdeal q (J.fundamentalLattice i) hzNorm
  have hzPrincipal : z ∈
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
    change z ∈ scaleIdeal q
      (scaleTruncation q L (ordUnit K (J.scaleGenerator i))) at hzScale
    rw [J.scaleIdeal_scaleTruncation_at_component,
      ← principalIdeal_eq_powerIdeal] at hzScale
    exact hzScale
  apply mem_integerRing_of_mul_mem_principalIdeal
    (Units.ne_zero (J.scaleGenerator i))
  have hcancel :
      (J.scaleGenerator i : K) *
          (((J.scaleGenerator i : Kˣ)⁻¹ : K) * z) = z := by
    field_simp [Units.ne_zero (J.scaleGenerator i)]
  rw [hcancel]
  exact hzPrincipal

/-- The scaled O'Meara plane `s A(alpha,0)` is `s`-modular whenever its
displayed coefficient is integral. -/
theorem scaledOmearaPlane_isModular
    (s : Kˣ) (alpha : K) (halpha : alpha ∈ IntegerRing K) :
    IsModular ((QuadraticSpace.omearaPlane alpha).rescaleUnit s)
      (hyperbolicPlaneLattice (K := K)) s := by
  let general := QuadraticSpace.omearaGeneralPlane alpha 0 (by simp)
  have hgeneral : IsModular general
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    omearaGeneralPlane_isModular_one alpha 0 (by simp) halpha
      (IntegerRing K).zero_mem (by simp [IsValuationUnit])
  let identify : Isometry general (QuadraticSpace.omearaPlane alpha)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := {
    toLinearEquiv :=
      (QuadraticSpace.omearaGeneralPlaneZeroRightIsometry alpha).toLinearEquiv
    map_bilin :=
      (QuadraticSpace.omearaGeneralPlaneZeroRightIsometry alpha).map_bilin
    map_mem := by intro x; rfl
  }
  have hunscaled : IsModular (QuadraticSpace.omearaPlane alpha)
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    hgeneral.mapLatticeIsometry identify
  have hscaled := hunscaled.rescaleQuadraticUnit s
  convert hscaled using 1 <;> simp

/-- If the two displayed generators lie in an ideal together with `2s`,
the norm ideal of `s A(s⁻¹ beta,0)` is contained in that ideal. -/
theorem normIdeal_scaledOmearaPlane_le
    (s : Kˣ) (beta : K)
    (halpha : ((s⁻¹ : Kˣ) : K) * beta ∈ IntegerRing K)
    (I : CoefficientIdeal (K := K))
    (hbeta : beta ∈ I) (htwo : (2 : K) * (s : K) ∈ I) :
    normIdeal
        ((QuadraticSpace.omearaPlane
          (((s⁻¹ : Kˣ) : K) * beta)).rescaleUnit s)
        (hyperbolicPlaneLattice (K := K)) ≤ I := by
  apply normIdeal_le_of_quadratic_mem
  intro x hx
  have hxcoord := (mem_omearaPlaneLattice_iff x).mp hx
  let x₀ : IntegerRing K := ⟨x 0, hxcoord.1⟩
  let x₁ : IntegerRing K := ⟨x 1, hxcoord.2⟩
  have hfirst : (x₀ ^ 2) • beta ∈ I := I.smul_mem (x₀ ^ 2) hbeta
  have hsecond : (x₀ * x₁) • ((2 : K) * (s : K)) ∈ I :=
    I.smul_mem (x₀ * x₁) htwo
  have hsum := I.add_mem hfirst hsecond
  change
    (((QuadraticSpace.omearaPlane
      (((s⁻¹ : Kˣ) : K) * beta)).rescaleUnit s).quadratic x) ∈ I
  rw [QuadraticSpace.rescaleUnit_quadratic]
  change (s : K) *
      (QuadraticSpace.omearaPlane
        (((s⁻¹ : Kˣ) : K) * beta)).bilin x x ∈ I
  rw [QuadraticSpace.omearaPlane_bilin_apply]
  change (s : K) *
      ((((s⁻¹ : Kˣ) : K) * beta) * x 0 * x 0 +
        x 0 * x 1 + x 1 * x 0) ∈ I
  have hidentity :
      (s : K) *
          ((((s⁻¹ : Kˣ) : K) * beta) * x 0 * x 0 +
            x 0 * x 1 + x 1 * x 0) =
          algebraMap (IntegerRing K) K (x₀ ^ 2) * beta +
          algebraMap (IntegerRing K) K (x₀ * x₁) *
            ((2 : K) * (s : K)) := by
    change (s : K) *
        ((((s⁻¹ : Kˣ) : K) * beta) * x 0 * x 0 +
          x 0 * x 1 + x 1 * x 0) =
      (x 0) ^ 2 * beta + (x 0 * x 1) * ((2 : K) * (s : K))
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero s]
    ring
  rw [hidentity]
  exact hsum

/-- The first standard vector of `s A(s⁻¹ beta,0)` represents `beta`. -/
theorem beta_mem_normGroupSet_scaledOmearaPlane (s : Kˣ) (beta : K) :
    beta ∈ normGroupSet
      ((QuadraticSpace.omearaPlane
        (((s⁻¹ : Kˣ) : K) * beta)).rescaleUnit s)
      (hyperbolicPlaneLattice (K := K)) := by
  let e₀ : Fin 2 → K := ![1, 0]
  have he₀ : e₀ ∈ hyperbolicPlaneLattice (K := K) := by
    rw [mem_omearaPlaneLattice_iff]
    simp [e₀]
  refine ⟨e₀, he₀, 0, (twoScaleIdeal _ _).zero_mem, ?_⟩
  rw [add_zero, QuadraticSpace.rescaleUnit_quadratic]
  symm
  change (s : K) *
      (QuadraticSpace.omearaPlane
        (((s⁻¹ : Kˣ) : K) * beta)).bilin e₀ e₀ = beta
  rw [QuadraticSpace.omearaPlane_bilin_apply]
  simp only [e₀, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, mul_one, mul_zero, add_zero, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero s]

variable {n : Nat} (J : JordanDecomposition q L (n + 2))
  (i : Fin (n + 2))

/-- Coefficient of the plane that will represent the fundamental norm
generator. -/
noncomputable def saturationNormCoefficient : K :=
  (((J.scaleGenerator i)⁻¹ : Kˣ) : K) *
    (J.fundamentalNormGenerator i : K)

/-- Coefficient of the plane that will represent the fundamental weight
generator. -/
noncomputable def saturationWeightCoefficient : K :=
  (((J.scaleGenerator i)⁻¹ : Kˣ) : K) *
    (J.fundamentalWeightGenerator i : K)

theorem saturationNormCoefficient_integral :
    J.saturationNormCoefficient i ∈ IntegerRing K := by
  simpa [saturationNormCoefficient, Units.val_inv_eq_inv_val] using
    J.scaleInverse_mul_mem_integerRing_of_mem_fundamentalNormGroup i
      (J.fundamentalNormGenerator_spec i).1

theorem saturationWeightCoefficient_integral :
    J.saturationWeightCoefficient i ∈ IntegerRing K := by
  simpa [saturationWeightCoefficient, Units.val_inv_eq_inv_val] using
    J.scaleInverse_mul_mem_integerRing_of_mem_fundamentalNormGroup i
      (J.fundamentalWeightGenerator_mem i)

@[simp]
theorem scale_mul_saturationNormCoefficient :
    (J.scaleGenerator i : K) * J.saturationNormCoefficient i =
      (J.fundamentalNormGenerator i : K) := by
  simp [saturationNormCoefficient, Units.ne_zero (J.scaleGenerator i)]

@[simp]
theorem scale_mul_saturationWeightCoefficient :
    (J.scaleGenerator i : K) * J.saturationWeightCoefficient i =
      (J.fundamentalWeightGenerator i : K) := by
  simp [saturationWeightCoefficient, Units.ne_zero (J.scaleGenerator i)]

/-- The first shifted plane in a saturation step. -/
noncomputable def saturationNormPlane : QuadraticSpace K (Fin 2 → K) :=
  (QuadraticSpace.omearaPlane (J.saturationNormCoefficient i)).rescaleUnit
    (J.scaleGenerator i)

/-- The second shifted plane in a saturation step. -/
noncomputable def saturationWeightPlane : QuadraticSpace K (Fin 2 → K) :=
  (QuadraticSpace.omearaPlane (J.saturationWeightCoefficient i)).rescaleUnit
    (J.scaleGenerator i)

/-- The changed component before it is mapped back into the original
ambient quadratic space. -/
noncomputable def saturationShiftedComponent
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    QuadraticSpace K
      ((Fin 2 → K) ×
        ((Fin 2 → K) × (S.decomposition.component 2).carrier)) :=
  (J.saturationNormPlane i).orthogonalSum
    ((J.saturationWeightPlane i).orthogonalSum
      (S.decomposition.component 2).space)

noncomputable def saturationShiftedComponentLattice
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    Lattice K
      ((Fin 2 → K) ×
        ((Fin 2 → K) × (S.decomposition.component 2).carrier)) :=
  product (hyperbolicPlaneLattice (K := K))
    (product (hyperbolicPlaneLattice (K := K))
      (S.decomposition.component 2).lattice)

/-- The full shifted coordinate model, retaining the exact complement of
the selected Jordan component in the base. -/
noncomputable def saturationShiftedFullSpace
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    QuadraticSpace K
      ((Fin 2 → K) × ((Fin 2 → K) ×
        ((S.decomposition.component 2).carrier ×
          (J.selectedRemainder i).carrier))) :=
  (J.saturationNormPlane i).orthogonalSum
    ((J.saturationWeightPlane i).orthogonalSum
      (J.saturationBase i S))

noncomputable def saturationShiftedFullLattice
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    Lattice K
      ((Fin 2 → K) × ((Fin 2 → K) ×
        ((S.decomposition.component 2).carrier ×
          (J.selectedRemainder i).carrier))) :=
  product (hyperbolicPlaneLattice (K := K))
    (product (hyperbolicPlaneLattice (K := K))
      (J.saturationBaseLattice i S))

/-- The two applications of O'Meara 93:13, followed by the original
two-hyperbolic-plane display, give an integral isometry from the shifted
coordinate model to the original lattice. -/
noncomputable def saturationShiftedFullIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    Isometry (J.saturationShiftedFullSpace i S) q
      (J.saturationShiftedFullLattice i S) L := by
  let s := J.scaleGenerator i
  let B := J.saturationBase i S
  let BL := J.saturationBaseLattice i S
  let Pzero := (QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit s
  let Pnorm := J.saturationNormPlane i
  let Pweight := J.saturationWeightPlane i
  have hbase :=
    J.fundamentalNormGroup_subset_saturationBaseTruncation i S hrank
  have hnorm : ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet B (omearaScaleTruncation B BL s) :=
    hbase (J.fundamentalNormGenerator_spec i).1
  have hweight : ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      normGroupSet B (omearaScaleTruncation B BL s) :=
    hbase (J.fundamentalWeightGenerator_mem i)
  let normalizeWeightRaw := omeara9313 B BL s 0
    (J.fundamentalWeightGenerator i : K) hweight
  let normalizeWeight : Isometry
      (Pweight.orthogonalSum B) (Pzero.orthogonalSum B)
      (product (hyperbolicPlaneLattice (K := K)) BL)
      (product (hyperbolicPlaneLattice (K := K)) BL) := by
    simpa only [Pweight, Pzero, saturationWeightPlane,
      saturationWeightCoefficient, zero_add] using normalizeWeightRaw
  let keepNorm := Isometry.refl Pnorm (hyperbolicPlaneLattice (K := K))
  let normalizeTail := keepNorm.orthogonalProductBasic normalizeWeight
  have hnormInZeroTail : ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet (Pzero.orthogonalSum B)
        (omearaScaleTruncation (Pzero.orthogonalSum B)
          (product (hyperbolicPlaneLattice (K := K)) BL) s) :=
    normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
      Pzero (hyperbolicPlaneLattice (K := K)) B BL s hnorm
  let normalizeNormRaw := omeara9313 (Pzero.orthogonalSum B)
    (product (hyperbolicPlaneLattice (K := K)) BL) s 0
    (J.fundamentalNormGenerator i : K) hnormInZeroTail
  let normalizeNorm : Isometry
      (Pnorm.orthogonalSum (Pzero.orthogonalSum B))
      (Pzero.orthogonalSum (Pzero.orthogonalSum B))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) BL))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) BL)) := by
    simpa only [Pnorm, Pzero, saturationNormPlane,
      saturationNormCoefficient, zero_add] using normalizeNormRaw
  let normalizeBoth := normalizeTail.trans normalizeNorm
  let identifyZero :=
    (scaledZeroOmearaPlaneLatticeIsometry s).orthogonalProductBasic
      ((scaledZeroOmearaPlaneLatticeIsometry s).orthogonalProductBasic
        (Isometry.refl B BL))
  exact normalizeBoth.trans <| identifyZero.trans <|
    J.saturationDisplayedIsometry i S

/-- Reassociate the changed component and the unchanged remainder without
changing any coordinate or lattice. -/
noncomputable def saturationShiftedGroupingIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    Isometry
      ((J.saturationShiftedComponent i S).orthogonalSum
        (J.selectedRemainder i).space)
      (J.saturationShiftedFullSpace i S)
      (product (J.saturationShiftedComponentLattice i S)
        (J.selectedRemainder i).lattice)
      (J.saturationShiftedFullLattice i S) := by
  let C := S.decomposition.component 2
  let R := J.selectedRemainder i
  let Pnorm := J.saturationNormPlane i
  let Pweight := J.saturationWeightPlane i
  let associateOuter : Isometry
      ((Pnorm.orthogonalSum (Pweight.orthogonalSum C.space)).orthogonalSum
        R.space)
      (Pnorm.orthogonalSum ((Pweight.orthogonalSum C.space).orthogonalSum
        R.space))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (product (hyperbolicPlaneLattice (K := K)) C.lattice)) R.lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product
          (product (hyperbolicPlaneLattice (K := K)) C.lattice) R.lattice)) :=
    orthogonalProductAssoc
  let associateInner :=
    (Isometry.refl Pnorm (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
      (orthogonalProductAssoc : Isometry
        ((Pweight.orthogonalSum C.space).orthogonalSum R.space)
        (Pweight.orthogonalSum (C.space.orthogonalSum R.space))
        (product
          (product (hyperbolicPlaneLattice (K := K)) C.lattice) R.lattice)
        (product (hyperbolicPlaneLattice (K := K))
          (product C.lattice R.lattice)))
  exact associateOuter.trans associateInner

/-- The selected changed component and the unchanged remainder, mapped back
into the original ambient lattice. -/
noncomputable def saturationReplacementPair
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    OrthogonalDecomposition q L 2 := by
  let selected := J.saturationShiftedComponent i S
  let selectedL := J.saturationShiftedComponentLattice i S
  let R := J.selectedRemainder i
  let D := orthogonalProductDecomposition selected R.space selectedL R.lattice
  let F := (J.saturationShiftedGroupingIsometry i S).trans
    (J.saturationShiftedFullIsometry i S hrank)
  exact D.mapIsometry F

-- Unfolding the nested mapped product component requires substantial
-- dependent-type normalization.
set_option maxHeartbeats 1000000 in
/-- The coordinate changed component is integrally isometric to the head of
the replacement pair. -/
noncomputable def saturationShiftedComponentIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    Isometry (J.saturationShiftedComponent i S)
      ((J.saturationReplacementPair i S hrank).component 0).space
      (J.saturationShiftedComponentLattice i S)
      ((J.saturationReplacementPair i S hrank).component 0).lattice := by
  let selected := J.saturationShiftedComponent i S
  let selectedL := J.saturationShiftedComponentLattice i S
  let R := J.selectedRemainder i
  let D := orthogonalProductDecomposition selected R.space selectedL R.lattice
  let F := (J.saturationShiftedGroupingIsometry i S).trans
    (J.saturationShiftedFullIsometry i S hrank)
  let left := orthogonalProductLeftComponentIsometry
    selected R.space selectedL
  let mapped := (D.component 0).mapLatticeIsometry F
  change Isometry selected ((D.mapIsometry F).component 0).space selectedL
    ((D.mapIsometry F).component 0).lattice
  exact left.trans mapped

-- As above, this bound is used only for normalization of the mapped right
-- product component.
set_option maxHeartbeats 1000000 in
/-- The old exact remainder is integrally isometric to the tail of the
replacement pair. -/
noncomputable def saturationRemainderIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    Isometry (J.selectedRemainder i).space
      ((J.saturationReplacementPair i S hrank).component 1).space
      (J.selectedRemainder i).lattice
      ((J.saturationReplacementPair i S hrank).component 1).lattice := by
  let selected := J.saturationShiftedComponent i S
  let selectedL := J.saturationShiftedComponentLattice i S
  let R := J.selectedRemainder i
  let D := orthogonalProductDecomposition selected R.space selectedL R.lattice
  let F := (J.saturationShiftedGroupingIsometry i S).trans
    (J.saturationShiftedFullIsometry i S hrank)
  let right := orthogonalProductRightComponentIsometry
    selected R.space R.lattice
  let mapped := (D.component 1).mapLatticeIsometry F
  change Isometry R.space ((D.mapIsometry F).component 1).space R.lattice
    ((D.mapIsometry F).component 1).lattice
  exact right.trans mapped

/-- The changed coordinate component remains modular at the old Jordan
scale. -/
theorem saturationShiftedComponent_modular
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    IsModular (J.saturationShiftedComponent i S)
      (J.saturationShiftedComponentLattice i S)
      (J.scaleGenerator i) := by
  exact (scaledOmearaPlane_isModular (J.scaleGenerator i)
    (J.saturationNormCoefficient i)
    (J.saturationNormCoefficient_integral i)).orthogonalProduct
      ((scaledOmearaPlane_isModular (J.scaleGenerator i)
        (J.saturationWeightCoefficient i)
        (J.saturationWeightCoefficient_integral i)).orthogonalProduct
          S.complement_modular)

/-- The changed coordinate component has positive rank. -/
theorem saturationShiftedComponent_finrank_pos
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    0 < finrank K
      ((Fin 2 → K) ×
        ((Fin 2 → K) × (S.decomposition.component 2).carrier)) := by
  letI : Module.Finite K (S.decomposition.component 2).carrier :=
    (S.decomposition.component 2).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_prod]
  simp

/-- The doubled scale generator of the selected fundamental layer belongs
to its norm ideal. -/
theorem two_mul_scale_mem_fundamentalNormIdeal :
    (2 : K) * (J.scaleGenerator i : K) ∈
      normIdeal q (J.fundamentalLattice i) := by
  apply twoScaleIdeal_le_normIdeal q (J.fundamentalLattice i)
  unfold twoScaleIdeal
  have hscale : scaleIdeal q (J.fundamentalLattice i) =
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
    change scaleIdeal q
      (scaleTruncation q L (ordUnit K (J.scaleGenerator i))) = _
    rw [J.scaleIdeal_scaleTruncation_at_component,
      ← principalIdeal_eq_powerIdeal]
  rw [hscale, twiceIdeal_principalIdeal]
  exact generator_mem_principalIdeal _

/-- The modular complement left after splitting the two hyperbolic planes
has norm ideal contained in the selected fundamental norm ideal. -/
theorem saturationComplementNormIdeal_le_fundamental
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    normIdeal (S.decomposition.component 2).space
        (S.decomposition.component 2).lattice ≤
      normIdeal q (J.fundamentalLattice i) := by
  have hcomponent :
      normIdeal (S.decomposition.component 2).space
          (S.decomposition.component 2).lattice ≤
        normIdeal (J.component i).space (J.component i).lattice := by
    rw [S.decomposition.normIdeal_eq_iSup_component]
    exact le_iSup
      (fun j : Fin 3 ↦ normIdeal (S.decomposition.component j).space
        (S.decomposition.component j).lattice) 2
  exact hcomponent.trans (J.componentNormIdeal_le_fundamental i)

/-- The changed component represents the selected fundamental norm
generator. -/
theorem fundamentalNormGenerator_mem_saturationShiftedComponent
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet (J.saturationShiftedComponent i S)
        (J.saturationShiftedComponentLattice i S) := by
  rw [saturationShiftedComponent, saturationShiftedComponentLattice,
    mem_normGroupSet_orthogonalProduct_iff]
  refine ⟨(J.fundamentalNormGenerator i : K), ?_, 0,
    zero_mem_normGroupSet _ _, by simp⟩
  simpa only [saturationNormPlane, saturationNormCoefficient] using
    beta_mem_normGroupSet_scaledOmearaPlane (J.scaleGenerator i)
      (J.fundamentalNormGenerator i : K)

/-- The changed component also represents the selected fundamental weight
generator. -/
theorem fundamentalWeightGenerator_mem_saturationShiftedComponent
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      normGroupSet (J.saturationShiftedComponent i S)
        (J.saturationShiftedComponentLattice i S) := by
  rw [saturationShiftedComponent, saturationShiftedComponentLattice,
    mem_normGroupSet_orthogonalProduct_iff]
  refine ⟨0, zero_mem_normGroupSet _ _,
    (J.fundamentalWeightGenerator i : K), ?_, by simp⟩
  rw [mem_normGroupSet_orthogonalProduct_iff]
  refine ⟨(J.fundamentalWeightGenerator i : K), ?_, 0,
    zero_mem_normGroupSet _ _, by simp⟩
  simpa only [saturationWeightPlane, saturationWeightCoefficient] using
    beta_mem_normGroupSet_scaledOmearaPlane (J.scaleGenerator i)
      (J.fundamentalWeightGenerator i : K)

/-- The norm ideal of the changed component is exactly the fundamental norm
ideal generator. -/
theorem saturationShiftedComponent_normIdeal_eq
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    normIdeal (J.saturationShiftedComponent i S)
        (J.saturationShiftedComponentLattice i S) =
      principalIdeal (K := K) (J.fundamentalNormGenerator i : K) := by
  let I := normIdeal q (J.fundamentalLattice i)
  have hnorm : ((J.fundamentalNormGenerator i : Kˣ) : K) ∈ I :=
    normGroupSet_subset_normIdeal q (J.fundamentalLattice i)
      (J.fundamentalNormGenerator_spec i).1
  have hweight : ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈ I :=
    normGroupSet_subset_normIdeal q (J.fundamentalLattice i)
      (J.fundamentalWeightGenerator_mem i)
  have htwo : (2 : K) * (J.scaleGenerator i : K) ∈ I :=
    J.two_mul_scale_mem_fundamentalNormIdeal i
  have hnormPlane :
      normIdeal (J.saturationNormPlane i)
          (hyperbolicPlaneLattice (K := K)) ≤ I := by
    simpa only [saturationNormPlane, saturationNormCoefficient] using
      normIdeal_scaledOmearaPlane_le (J.scaleGenerator i)
        (J.fundamentalNormGenerator i : K)
        (J.saturationNormCoefficient_integral i) I hnorm htwo
  have hweightPlane :
      normIdeal (J.saturationWeightPlane i)
          (hyperbolicPlaneLattice (K := K)) ≤ I := by
    simpa only [saturationWeightPlane, saturationWeightCoefficient] using
      normIdeal_scaledOmearaPlane_le (J.scaleGenerator i)
        (J.fundamentalWeightGenerator i : K)
        (J.saturationWeightCoefficient_integral i) I hweight htwo
  have hupper : normIdeal (J.saturationShiftedComponent i S)
      (J.saturationShiftedComponentLattice i S) ≤ I := by
    rw [saturationShiftedComponent, saturationShiftedComponentLattice,
      normIdeal_orthogonalProduct, normIdeal_orthogonalProduct]
    exact _root_.sup_le hnormPlane
      (_root_.sup_le hweightPlane
        (J.saturationComplementNormIdeal_le_fundamental i S))
  have hlower : principalIdeal (K := K)
      (J.fundamentalNormGenerator i : K) ≤
      normIdeal (J.saturationShiftedComponent i S)
        (J.saturationShiftedComponentLattice i S) := by
    rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    exact normGroupSet_subset_normIdeal _ _
      (J.fundamentalNormGenerator_mem_saturationShiftedComponent i S)
  exact le_antisymm
    (hupper.trans_eq (J.fundamentalNormGenerator_spec i).2) hlower

/-- The head of the replacement pair is modular at the old Jordan scale. -/
theorem saturationReplacementHead_modular
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    IsModular ((J.saturationReplacementPair i S hrank).component 0).space
      ((J.saturationReplacementPair i S hrank).component 0).lattice
      (J.scaleGenerator i) :=
  (J.saturationShiftedComponent_modular i S).mapLatticeIsometry
    (J.saturationShiftedComponentIsometry i S hrank)

/-- The head of the replacement pair has the old component scale ideal. -/
theorem saturationReplacementHead_scaleIdeal_eq
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    scaleIdeal ((J.saturationReplacementPair i S hrank).component 0).space
        ((J.saturationReplacementPair i S hrank).component 0).lattice =
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
  apply (J.saturationReplacementHead_modular i S hrank).scaleIdeal_eq_principal
  rw [← (J.saturationShiftedComponentIsometry i S hrank).toLinearEquiv.finrank_eq]
  exact J.saturationShiftedComponent_finrank_pos i S

/-- The head of the replacement pair has the selected fundamental norm
ideal. -/
theorem saturationReplacementHead_normIdeal_eq
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    normIdeal ((J.saturationReplacementPair i S hrank).component 0).space
        ((J.saturationReplacementPair i S hrank).component 0).lattice =
      principalIdeal (K := K) (J.fundamentalNormGenerator i : K) := by
  let f := J.saturationShiftedComponentIsometry i S hrank
  calc
    normIdeal ((J.saturationReplacementPair i S hrank).component 0).space
        ((J.saturationReplacementPair i S hrank).component 0).lattice =
        normIdeal ((J.saturationReplacementPair i S hrank).component 0).space
          (map f.toLinearEquiv (J.saturationShiftedComponentLattice i S)) := by
            rw [f.map_eq]
    _ = normIdeal (J.saturationShiftedComponent i S)
          (J.saturationShiftedComponentLattice i S) :=
      normIdeal_map_isometry f.toQuadraticSpaceIsometry _
    _ = principalIdeal (K := K)
          (J.fundamentalNormGenerator i : K) :=
      J.saturationShiftedComponent_normIdeal_eq i S

/-- One concrete rank-at-least-seven O'Meara 93:21 step.  It replaces only
the selected component, keeps all Jordan scales, and uses the intrinsic
fundamental norm generator as the new displayed norm generator. -/
noncomputable def saturationReplaceComponent
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    JordanDecomposition q L (n + 2) :=
  J.replaceComponent i (J.saturationReplacementPair i S hrank)
    (J.saturationRemainderIsometry i S hrank)
    (J.fundamentalNormGenerator i)
    (J.saturationReplacementHead_modular i S hrank)
    (J.saturationReplacementHead_scaleIdeal_eq i S hrank)
    (J.saturationReplacementHead_normIdeal_eq i S hrank)

@[simp]
theorem saturationReplaceComponent_scaleGenerator
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) (j : Fin (n + 2)) :
    (J.saturationReplaceComponent i S hrank).scaleGenerator j =
      J.scaleGenerator j :=
  rfl

@[simp]
theorem saturationReplaceComponent_fundamentalLattice
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) (j : Fin (n + 2)) :
    (J.saturationReplaceComponent i S hrank).fundamentalLattice j =
      J.fundamentalLattice j :=
  rfl

@[simp]
theorem saturationReplaceComponent_fundamentalNormGroup
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) (j : Fin (n + 2)) :
    (J.saturationReplaceComponent i S hrank).fundamentalNormGroup j =
      J.fundamentalNormGroup j :=
  rfl

/-- The new displayed component represents the old intrinsic norm
generator. -/
theorem fundamentalNormGenerator_mem_saturationReplacement
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet ((J.saturationReplaceComponent i S hrank).component i).space
        ((J.saturationReplaceComponent i S hrank).component i).lattice := by
  rw [saturationReplaceComponent, replaceComponent_component_self]
  rw [normGroupSet_eq_of_latticeIsometry
    (J.saturationShiftedComponentIsometry i S hrank)]
  exact J.fundamentalNormGenerator_mem_saturationShiftedComponent i S

/-- The new displayed component represents the old intrinsic weight
generator. -/
theorem fundamentalWeightGenerator_mem_saturationReplacement
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      normGroupSet ((J.saturationReplaceComponent i S hrank).component i).space
        ((J.saturationReplaceComponent i S hrank).component i).lattice := by
  rw [saturationReplaceComponent, replaceComponent_component_self]
  rw [normGroupSet_eq_of_latticeIsometry
    (J.saturationShiftedComponentIsometry i S hrank)]
  exact J.fundamentalWeightGenerator_mem_saturationShiftedComponent i S

/-- A concrete rank-at-least-seven saturation step saturates its selected
Jordan component. -/
theorem saturationReplaceComponent_selected_isSaturated
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    normGroupSet ((J.saturationReplaceComponent i S hrank).component i).space
        ((J.saturationReplaceComponent i S hrank).component i).lattice =
      (J.saturationReplaceComponent i S hrank).fundamentalNormGroup i := by
  let J' := J.saturationReplaceComponent i S hrank
  apply J'.componentNormGroup_eq_fundamental_of_generators_mem i
  · change ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet (J'.component i).space (J'.component i).lattice
    exact J.fundamentalNormGenerator_mem_saturationReplacement i S hrank
  · change ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      normGroupSet (J'.component i).space (J'.component i).lattice
    exact J.fundamentalWeightGenerator_mem_saturationReplacement i S hrank

end JordanDecomposition

end Lattice

end Bong
