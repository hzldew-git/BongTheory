/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationIteration
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.NormRescale
import Bong.Lattice.NormGroupRepresentation
import Bong.Bong.Beli2009OrthogonalIdealProof

/-!
# O'Meara's rank-three saturation stabilization

O'Meara 93:21 reduces components of rank at least three to the already
proved rank-at-least-seven case by adjoining two standard hyperbolic planes
at every Jordan scale.  This file constructs the enlarged Jordan splitting
and proves the essential invariant statement: its fundamental norm groups
are exactly those of the original splitting.

The proof is intrinsic.  At every scale truncation the old component and
the two added hyperbolic planes are rescaled by the same factor.  The norm
group of either rescaled hyperbolic plane is contained in the norm group of
the positive-rank rescaled modular component, so the two planes contribute
no new norm-group elements.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section Absorption

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- A common rescaling of a standard scaled hyperbolic plane is still
absorbed by every positive-rank modular lattice rescaled by the same
factor. -/
theorem normGroupSet_rescaledHyperbolic_subset_of_rescaledModular
    (hL : IsModular q L s) (hpos : 0 < finrank K V) (c : Kˣ) :
    normGroupSet (QuadraticSpace.hyperbolicPlane s)
        (rescale c (hyperbolicPlaneLattice (K := K))) ⊆
      normGroupSet q (rescale c L) := by
  let twoS : Kˣ :=
    Units.mk0 (2 * (s : K))
      (mul_ne_zero (by norm_num) (Units.ne_zero s))
  have hHNorm :
      normIdeal (QuadraticSpace.hyperbolicPlane s)
          (rescale c (hyperbolicPlaneLattice (K := K))) =
        principalIdeal (K := K) ((c ^ 2 * twoS : Kˣ) : K) := by
    exact normIdeal_rescale_eq_principal_of_finrank_pos
      (q := QuadraticSpace.hyperbolicPlane s)
      (L := hyperbolicPlaneLattice (K := K)) (by simp) c
      twoS
      (by
        simpa [twoS] using normIdeal_hyperbolicPlaneLattice (K := K) s)
  have htargetTwo :
      twoScaleIdeal q (rescale c L) =
        principalIdeal (K := K) ((c ^ 2 * twoS : Kˣ) : K) := by
    rw [twoScaleIdeal,
      (hL.rescale c).scaleIdeal_eq_principal hpos,
      twiceIdeal_principalIdeal]
    congr 1
    change (2 : K) * ((s : K) * (c : K) ^ 2) =
      (c : K) ^ 2 * (2 * (s : K))
    ring
  intro z hz
  apply twoScaleIdeal_subset_normGroupSet q (rescale c L)
  rw [htargetTwo, ← hHNorm]
  exact normGroupSet_subset_normIdeal
    (QuadraticSpace.hyperbolicPlane s)
    (rescale c (hyperbolicPlaneLattice (K := K))) hz

/-- After a common lattice rescaling, adjoining two standard hyperbolic
planes at the modular scale leaves the norm group unchanged. -/
theorem normGroupSet_two_rescaledHyperbolic_eq_modular
    (hL : IsModular q L s) (hpos : 0 < finrank K V) (c : Kˣ) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum q))
        (rescale c
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicPlaneLattice (K := K)) L))) =
      normGroupSet q (rescale c L) := by
  rw [← product_rescale, ← product_rescale]
  apply Set.Subset.antisymm
  · intro z hz
    rw [mem_normGroupSet_orthogonalProduct_iff] at hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    rw [mem_normGroupSet_orthogonalProduct_iff] at hb
    rcases hb with ⟨d, hd, e, he, rfl⟩
    exact add_mem_normGroupSet q (rescale c L)
      (normGroupSet_rescaledHyperbolic_subset_of_rescaledModular
        hL hpos c ha)
      (add_mem_normGroupSet q (rescale c L)
        (normGroupSet_rescaledHyperbolic_subset_of_rescaledModular
          hL hpos c hd) he)
  · intro z hz
    rw [mem_normGroupSet_orthogonalProduct_iff]
    refine ⟨0, zero_mem_normGroupSet _ _, z, ?_, by simp⟩
    rw [mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨0, zero_mem_normGroupSet _ _, z, hz, by simp⟩

/-- The unrescaled form of the two-plane absorption identity. -/
theorem normGroupSet_two_scaledHyperbolic_eq_modular
    (hL : IsModular q L s) (hpos : 0 < finrank K V) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum q))
        (product (hyperbolicPlaneLattice (K := K))
          (product (hyperbolicPlaneLattice (K := K)) L)) =
      normGroupSet q L := by
  simpa using normGroupSet_two_rescaledHyperbolic_eq_modular
    hL hpos (1 : Kˣ)

end Absorption

namespace OrthogonalDecomposition

variable {V : Type v} {W : Type w}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- Two finite orthogonal sums have the same norm group when corresponding
component norm groups and component scale ideals agree. -/
theorem normGroupSet_eq_of_componentwise_eq
    (D : OrthogonalDecomposition q L t)
    (E : OrthogonalDecomposition r M t)
    (hscale : ∀ i,
      scaleIdeal (D.component i).space (D.component i).lattice =
        scaleIdeal (E.component i).space (E.component i).lattice)
    (hgroup : ∀ i,
      normGroupSet (D.component i).space (D.component i).lattice =
        normGroupSet (E.component i).space (E.component i).lattice) :
    normGroupSet q L = normGroupSet r M := by
  rw [D.normGroupSet_eq_normGroupExpression,
    E.normGroupSet_eq_normGroupExpression]
  have hambientScale : scaleIdeal q L = scaleIdeal r M := by
    rw [D.scaleIdeal_eq_iSup_component,
      E.scaleIdeal_eq_iSup_component]
    simp_rw [hscale]
  unfold normGroupExpression setPlusIdeal indexedSetSum twoScaleIdeal
  rw [hambientScale]
  simp_rw [hgroup]

end OrthogonalDecomposition

namespace JordanDecomposition

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {n : Nat} (J : JordanDecomposition q L (n + 2))

/-- The carrier of the component obtained by adjoining two hyperbolic
planes at the component scale. -/
abbrev saturationStableCarrier (i : Fin (n + 2)) :=
  (Fin 2 → K) × ((Fin 2 → K) × (J.component i).carrier)

/-- The quadratic form on one twice-hyperbolically stabilized component. -/
noncomputable def saturationStableForm (i : Fin (n + 2)) :
    QuadraticSpace K (J.saturationStableCarrier i) :=
  (QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
    ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
      (J.component i).space)

/-- The lattice on one twice-hyperbolically stabilized component. -/
noncomputable def saturationStableLattice (i : Fin (n + 2)) :
    Lattice K (J.saturationStableCarrier i) :=
  product (hyperbolicPlaneLattice (K := K))
    (product (hyperbolicPlaneLattice (K := K))
      (J.component i).lattice)

/-- Each stabilized component remains modular at the old scale. -/
theorem saturationStable_modular (i : Fin (n + 2)) :
    IsModular (J.saturationStableForm i) (J.saturationStableLattice i)
      (J.scaleGenerator i) :=
  (hyperbolicPlaneLattice_isModular (K := K) (J.scaleGenerator i)).orthogonalProduct
    ((hyperbolicPlaneLattice_isModular (K := K)
      (J.scaleGenerator i)).orthogonalProduct (J.modular i))

/-- Stabilization adds four to the component rank. -/
theorem saturationStable_finrank (i : Fin (n + 2)) :
    finrank K (J.saturationStableCarrier i) = J.componentRank i + 4 := by
  letI : Module.Finite K (J.component i).carrier :=
    (J.component i).lattice.moduleFinite
  unfold saturationStableCarrier componentRank
  rw [Module.finrank_prod, Module.finrank_prod,
    Module.finrank_fin_fun]
  omega

/-- A chosen norm-generating anisotropic vector of a stabilized
component. -/
noncomputable def saturationStableNormGeneratorVector
    (i : Fin (n + 2)) : J.saturationStableCarrier i :=
  Classical.choose <|
    exists_isNormGenerator_of_finrank_pos
      (J.saturationStableForm i) (J.saturationStableLattice i)
      (by rw [J.saturationStable_finrank i]; omega)

theorem saturationStableNormGeneratorVector_spec
    (i : Fin (n + 2)) :
    IsNormGenerator (J.saturationStableForm i)
        (J.saturationStableLattice i)
        (J.saturationStableNormGeneratorVector i) ∧
      (J.saturationStableForm i).IsAnisotropic
        (J.saturationStableNormGeneratorVector i) :=
  Classical.choose_spec <|
    exists_isNormGenerator_of_finrank_pos
      (J.saturationStableForm i) (J.saturationStableLattice i)
      (by rw [J.saturationStable_finrank i]; omega)

/-- The selected nonzero norm value on a stabilized component. -/
noncomputable def saturationStableNormGenerator
    (i : Fin (n + 2)) : Kˣ :=
  Units.mk0
    ((J.saturationStableForm i).quadratic
      (J.saturationStableNormGeneratorVector i))
    (J.saturationStableNormGeneratorVector_spec i).2

theorem saturationStable_normIdeal_eq (i : Fin (n + 2)) :
    normIdeal (J.saturationStableForm i) (J.saturationStableLattice i) =
      principalIdeal (K := K) (J.saturationStableNormGenerator i : K) :=
  (J.saturationStableNormGeneratorVector_spec i).1.normIdeal_eq

theorem saturationStable_scaleIdeal_eq (i : Fin (n + 2)) :
    scaleIdeal (J.saturationStableForm i) (J.saturationStableLattice i) =
      principalIdeal (K := K) (J.scaleGenerator i : K) :=
  (J.saturationStable_modular i).scaleIdeal_eq_principal
    (by rw [J.saturationStable_finrank i]; omega)

/-- The Jordan decomposition of the coordinate product of all stabilized
components. -/
noncomputable def saturationStableJordan :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) J.saturationStableCarrier
        J.saturationStableForm)
      (BONG.blockProductLattice (n + 1) J.saturationStableCarrier
        J.saturationStableLattice)
      (n + 2) :=
  BONG.blockProductJordanDecomposition
    J.saturationStableCarrier J.saturationStableForm
    J.saturationStableLattice J.scaleGenerator
    J.saturationStableNormGenerator J.saturationStable_modular
    J.saturationStable_scaleIdeal_eq J.saturationStable_normIdeal_eq
    (fun _ _ hij ↦ J.scaleOrder_strict hij)

@[simp]
theorem saturationStableJordan_scaleGenerator (i : Fin (n + 2)) :
    J.saturationStableJordan.scaleGenerator i = J.scaleGenerator i :=
  rfl

@[simp]
theorem saturationStableJordan_componentRank (i : Fin (n + 2)) :
    J.saturationStableJordan.componentRank i = J.componentRank i + 4 := by
  rw [saturationStableJordan,
    BONG.blockProductJordanDecomposition_componentRank,
    J.saturationStable_finrank]

/-- Corresponding truncation components of the stabilized and original
Jordan splittings have the same scale ideal. -/
theorem saturationStable_truncation_component_scaleIdeal_eq
    (k : Int) (i : Fin (n + 2)) :
    scaleIdeal
        ((J.saturationStableJordan.scaleTruncationDecomposition k).component i).space
        ((J.saturationStableJordan.scaleTruncationDecomposition k).component i).lattice =
      scaleIdeal ((J.scaleTruncationDecomposition k).component i).space
        ((J.scaleTruncationDecomposition k).component i).lattice := by
  let c := J.scaleTruncationFactor k i
  have hc : J.saturationStableJordan.scaleTruncationFactor k i = c := by
    simp only [c, JordanDecomposition.scaleTruncationFactor,
      J.saturationStableJordan_scaleGenerator]
  rw [J.saturationStableJordan.scaleTruncationDecomposition_component,
    J.scaleTruncationDecomposition_component, hc]
  let f := BONG.blockProductComponentIsometry
    J.saturationStableCarrier J.saturationStableForm
      J.saturationStableLattice i
  let fc := f.rescaleLattices c
  calc
    scaleIdeal
        (J.saturationStableJordan.component i).space
        (rescale c (J.saturationStableJordan.component i).lattice) =
        scaleIdeal (J.saturationStableForm i)
          (rescale c (J.saturationStableLattice i)) := by
      change scaleIdeal
          ((BONG.blockProductOrthogonalDecomposition
            J.saturationStableCarrier J.saturationStableForm
              J.saturationStableLattice).component i).space
          (rescale c
            ((BONG.blockProductOrthogonalDecomposition
              J.saturationStableCarrier J.saturationStableForm
                J.saturationStableLattice).component i).lattice) = _
      rw [← fc.map_eq]
      exact scaleIdeal_map_isometry fc.toQuadraticSpaceIsometry
        (rescale c (J.saturationStableLattice i))
    _ = principalIdeal (K := K)
        ((J.scaleGenerator i * c ^ 2 : Kˣ) : K) :=
      ((J.saturationStable_modular i).rescale c).scaleIdeal_eq_principal
        (by rw [J.saturationStable_finrank i]; omega)
    _ = scaleIdeal (J.component i).space
        (rescale c (J.component i).lattice) :=
      ((J.modular i).rescale c).scaleIdeal_eq_principal
        (J.component_finrank_pos i) |>.symm

/-- Corresponding truncation components of the stabilized and original
Jordan splittings have the same norm group. -/
theorem saturationStable_truncation_component_normGroup_eq
    (k : Int) (i : Fin (n + 2)) :
    normGroupSet
        ((J.saturationStableJordan.scaleTruncationDecomposition k).component i).space
        ((J.saturationStableJordan.scaleTruncationDecomposition k).component i).lattice =
      normGroupSet ((J.scaleTruncationDecomposition k).component i).space
        ((J.scaleTruncationDecomposition k).component i).lattice := by
  let c := J.scaleTruncationFactor k i
  have hc : J.saturationStableJordan.scaleTruncationFactor k i = c := by
    simp only [c, JordanDecomposition.scaleTruncationFactor,
      J.saturationStableJordan_scaleGenerator]
  rw [J.saturationStableJordan.scaleTruncationDecomposition_component,
    J.scaleTruncationDecomposition_component, hc]
  let f := BONG.blockProductComponentIsometry
    J.saturationStableCarrier J.saturationStableForm
      J.saturationStableLattice i
  let fc := f.rescaleLattices c
  calc
    normGroupSet
        (J.saturationStableJordan.component i).space
        (rescale c (J.saturationStableJordan.component i).lattice) =
        normGroupSet (J.saturationStableForm i)
          (rescale c (J.saturationStableLattice i)) :=
      normGroupSet_eq_of_latticeIsometry fc
    _ = normGroupSet (J.component i).space
        (rescale c (J.component i).lattice) :=
      normGroupSet_two_rescaledHyperbolic_eq_modular
        (J.modular i) (J.component_finrank_pos i) c

/-- O'Meara's two-plane stabilization leaves every fundamental norm group
unchanged. -/
theorem saturationStableJordan_fundamentalNormGroup
    (i : Fin (n + 2)) :
    J.saturationStableJordan.fundamentalNormGroup i =
      J.fundamentalNormGroup i := by
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  rw [J.saturationStableJordan_scaleGenerator]
  exact OrthogonalDecomposition.normGroupSet_eq_of_componentwise_eq
    (J.saturationStableJordan.scaleTruncationDecomposition
      (ordUnit K (J.scaleGenerator i)))
    (J.scaleTruncationDecomposition
      (ordUnit K (J.scaleGenerator i)))
    (J.saturationStable_truncation_component_scaleIdeal_eq
      (ordUnit K (J.scaleGenerator i)))
    (J.saturationStable_truncation_component_normGroup_eq
      (ordUnit K (J.scaleGenerator i)))

/-- If the original Jordan splitting is saturated, adjoining the same two
hyperbolic planes at every component scale preserves saturation.  This is
the direct form of the first stabilization used in the sufficiency proof of
O'Meara 93:28. -/
theorem saturationStableJordan_isSaturated_of_isSaturated
    (hJ : J.IsSaturated) :
    J.saturationStableJordan.IsSaturated := by
  intro i
  let f := BONG.blockProductComponentIsometry
    J.saturationStableCarrier J.saturationStableForm
      J.saturationStableLattice i
  calc
    normGroupSet (J.saturationStableJordan.component i).space
        (J.saturationStableJordan.component i).lattice =
        normGroupSet (J.saturationStableForm i)
          (J.saturationStableLattice i) :=
      normGroupSet_eq_of_latticeIsometry f
    _ = normGroupSet (J.component i).space
        (J.component i).lattice :=
      normGroupSet_two_scaledHyperbolic_eq_modular
        (J.modular i) (J.component_finrank_pos i)
    _ = J.fundamentalNormGroup i := hJ i
    _ = J.saturationStableJordan.fundamentalNormGroup i :=
      (J.saturationStableJordan_fundamentalNormGroup i).symm

/-- All stabilized components have rank at least seven as soon as the
original components have rank at least three. -/
theorem saturationStableJordan_componentRank_atLeastSeven
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (n + 2)) :
    7 ≤ J.saturationStableJordan.componentRank i := by
  rw [J.saturationStableJordan_componentRank]
  have hi := hrank i
  omega

/-- Saturate the stabilized Jordan splitting using the already proved
rank-at-least-seven case of O'Meara 93:21. -/
noncomputable def saturatedStabilizedJordan
    (hrank : ∀ i, 3 ≤ J.componentRank i) :=
  J.saturationStableJordan.saturatedJordanOfComponentRanksAtLeastSeven
    (J.saturationStableJordan_componentRank_atLeastSeven hrank)

theorem saturatedStabilizedJordan_isSaturated
    (hrank : ∀ i, 3 ≤ J.componentRank i) :
    (J.saturatedStabilizedJordan hrank).IsSaturated :=
  J.saturationStableJordan.saturatedJordanOfComponentRanksAtLeastSeven_isSaturated
    (J.saturationStableJordan_componentRank_atLeastSeven hrank)

@[simp]
theorem saturatedStabilizedJordan_scaleGenerator
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (n + 2)) :
    (J.saturatedStabilizedJordan hrank).scaleGenerator i =
      J.scaleGenerator i := by
  rw [saturatedStabilizedJordan,
    saturatedJordanOfComponentRanksAtLeastSeven_scaleGenerator,
    J.saturationStableJordan_scaleGenerator]

@[simp]
theorem saturatedStabilizedJordan_componentRank
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (n + 2)) :
    (J.saturatedStabilizedJordan hrank).componentRank i =
      J.componentRank i + 4 := by
  rw [saturatedStabilizedJordan,
    saturatedJordanOfComponentRanksAtLeastSeven_componentRank,
    J.saturationStableJordan_componentRank]

theorem saturatedStabilizedJordan_fundamentalNormGroup
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (n + 2)) :
    (J.saturatedStabilizedJordan hrank).fundamentalNormGroup i =
      J.fundamentalNormGroup i := by
  calc
    (J.saturatedStabilizedJordan hrank).fundamentalNormGroup i =
        J.saturationStableJordan.fundamentalNormGroup i := by
      unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
      rw [J.saturatedStabilizedJordan_scaleGenerator hrank,
        J.saturationStableJordan_scaleGenerator]
    _ = J.fundamentalNormGroup i :=
      J.saturationStableJordan_fundamentalNormGroup i

end JordanDecomposition

end Lattice

end Bong
