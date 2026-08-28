/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StabilizationPrefixes
import Bong.Lattice.PairedHyperbolicDeterminant
import Bong.Lattice.PairedHyperbolicRepresentation
import Bong.Lattice.Omeara9328GeneratorChoice
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# Preservation of O'Meara 93:28 data under rank stabilization

The twice-hyperbolic stabilization leaves the fundamental boundary ideals
unchanged.  Its prefix determinant acquires an explicit paired-hyperbolic
factor, and equal fundamental type gives the same refined square class for
that factor on both sides.  Hence condition 93:28(i) is preserved without
any law parameter.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} {W : Type w}
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Stabilization preserves the order of every chosen fundamental norm
generator, although the chosen representatives themselves may differ. -/
theorem saturationStableJordan_fundamentalNormGenerator_order
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 2)) :
    ordUnit K (J.saturationStableJordan.fundamentalNormGenerator i) =
      ordUnit K (J.fundamentalNormGenerator i) := by
  have hcommon := isNormGeneratorValue_of_normGroupSet_eq
    (J.fundamentalNormGenerator_spec i)
    (J.saturationStableJordan_fundamentalNormGroup i).symm
    (J.saturationStableJordan.exists_fundamentalNormGenerator i)
  have hown := J.saturationStableJordan.fundamentalNormGenerator_spec i
  apply (principalIdeal_eq_iff_ordUnit_eq
    (J.saturationStableJordan.fundamentalNormGenerator i)
    (J.fundamentalNormGenerator i)).mp
  exact hown.2.symm.trans hcommon.2

/-- Stabilization preserves each boundary norm-order sum. -/
theorem saturationStableJordan_boundaryNormOrderSum
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    J.saturationStableJordan.boundaryNormOrderSum i =
      J.boundaryNormOrderSum i := by
  unfold boundaryNormOrderSum
  rw [J.saturationStableJordan_fundamentalNormGenerator_order,
    J.saturationStableJordan_fundamentalNormGenerator_order]

/-- Stabilization preserves the product-defect contribution at every
boundary. -/
theorem saturationStableJordan_boundaryProductDefectSum
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    J.saturationStableJordan.boundaryProductDefectSum i =
      J.boundaryProductDefectSum i := by
  unfold boundaryProductDefectSum
  rw [J.saturationStableJordan_fundamentalNormGroup,
    J.saturationStableJordan_fundamentalNormGroup]

/-- Stabilization preserves the even-parity dyadic boundary contribution. -/
theorem saturationStableJordan_boundaryParityIdeal
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    J.saturationStableJordan.boundaryParityIdeal i =
      J.boundaryParityIdeal i := by
  unfold boundaryParityIdeal fundamentalScaleOrder
  rw [J.saturationStableJordan_boundaryNormOrderSum,
    J.saturationStableJordan_scaleGenerator]

/-- Stabilization preserves O'Meara's scaled boundary ideal. -/
theorem saturationStableJordan_scaledFundamentalIdeal
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    J.saturationStableJordan.scaledFundamentalIdeal i =
      J.scaledFundamentalIdeal i := by
  unfold scaledFundamentalIdeal
  rw [J.saturationStableJordan_boundaryNormOrderSum,
    J.saturationStableJordan_boundaryProductDefectSum,
    J.saturationStableJordan_boundaryParityIdeal]

/-- The fundamental ideals `f_i` are literally unchanged by simultaneous
rank stabilization. -/
theorem saturationStableJordan_fundamentalIdeal
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    J.saturationStableJordan.fundamentalIdeal i =
      J.fundamentalIdeal i := by
  unfold fundamentalIdeal
  rw [J.saturationStableJordan_scaledFundamentalIdeal,
    J.saturationStableJordan_scaleGenerator]

namespace FundamentalNormGeneratorChoice

/-- Reuse exactly the same scalar generators after stabilization.  Their
validity follows from equality of the intrinsic fundamental norm groups. -/
noncomputable def saturationStable
    {J : JordanDecomposition q L (N + 2)}
    (A : FundamentalNormGeneratorChoice J) :
    FundamentalNormGeneratorChoice J.saturationStableJordan where
  value := A.value
  spec i :=
    isNormGeneratorValue_of_normGroupSet_eq
      (A.spec i)
      (J.saturationStableJordan_fundamentalNormGroup i).symm
      (J.saturationStableJordan.exists_fundamentalNormGenerator i)

@[simp]
theorem saturationStable_value
    {J : JordanDecomposition q L (N + 2)}
    (A : FundamentalNormGeneratorChoice J) (i : Fin (N + 2)) :
    A.saturationStable.value i = A.value i :=
  rfl

end FundamentalNormGeneratorChoice

/-- Stabilization preserves every intrinsic fundamental weight ideal. -/
theorem saturationStableJordan_fundamentalWeightIdeal
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 2)) :
    J.saturationStableJordan.fundamentalWeightIdeal i =
      J.fundamentalWeightIdeal i := by
  have hscale :
      J.saturationStableJordan.fundamentalScaleOrder i =
        J.fundamentalScaleOrder i := by
    unfold fundamentalScaleOrder
    rw [J.saturationStableJordan_scaleGenerator]
  have htwo : twoScaleIdeal q (J.fundamentalLattice i) =
      twoScaleIdeal
        (BONG.blockOrthogonalForm (N + 1) J.saturationStableCarrier
          J.saturationStableForm)
        (J.saturationStableJordan.fundamentalLattice i) := by
    rw [J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      J.saturationStableJordan.fundamentalTwoScaleIdeal_eq_powerIdeal,
      hscale]
  exact (weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    (J.fundamentalNormGenerator_spec i)
    (J.saturationStableJordan.exists_fundamentalNormGenerator i)
    (J.saturationStableJordan_fundamentalNormGroup i).symm htwo).symm

/-- Hence stabilization also preserves the integral orders of the
fundamental weight ideals. -/
theorem saturationStableJordan_fundamentalWeightOrder
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 2)) :
    J.saturationStableJordan.fundamentalWeightOrder i =
      J.fundamentalWeightOrder i := by
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  simpa only [fundamentalWeightIdeal] using
    J.saturationStableJordan_fundamentalWeightIdeal i

/-- The explicit threshold `4 a_i w_i⁻¹` is unchanged when the same
coherent generator is reused after stabilization. -/
theorem saturationStableJordan_fourNormOverWeightIdealWith
    {J : JordanDecomposition q L (N + 2)}
    (A : FundamentalNormGeneratorChoice J) (i : Fin (N + 2)) :
    J.saturationStableJordan.fourNormOverWeightIdealWith
        A.saturationStable i =
      J.fourNormOverWeightIdealWith A i := by
  unfold fourNormOverWeightIdealWith
  rw [FundamentalNormGeneratorChoice.saturationStable_value,
    J.saturationStableJordan_fundamentalWeightOrder]

set_option maxHeartbeats 0 in
-- Determinant normalization through the dependent prefix presentation is expensive.
/-- Refined determinant class of a stabilized proper prefix. -/
theorem unitSquareClass_saturationStable_prefixDeterminantUnit
    (J : JordanDecomposition q L (N + 2)) (i : Fin (N + 1)) :
    unitSquareClass K
        (J.saturationStableJordan.prefixDeterminantUnit i) =
      unitSquareClass K
          (pairedHyperbolicDeterminantFactor (i.val + 1)
            (J.prefixScaleGenerator (m := i.val) (by omega))) *
        unitSquareClass K (J.prefixDeterminantUnit i) := by
  let hk : i.val + 1 ≤ N + 2 := by omega
  let f := J.saturationStablePrefixGatherIsometry (m := i.val) hk
  have hdet := determinantClass_eq_of_isometry f
  have htower := determinantClass_pairedHyperbolicExtension
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (i.val + 1)).space
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (i.val + 1)).lattice
    (i.val + 1) (J.prefixScaleGenerator hk)
  have h := hdet.trans htower
  simpa only [prefixDeterminantUnit,
    QuadraticSublattice.refinedDeterminantUnit, determinantClass] using h

namespace SameFundamentalType

variable {J : JordanDecomposition q L (N + 2)}
  {H : JordanDecomposition r M (N + 2)}

/-- Equal fundamental type identifies all scale orders in every restricted
prefix list. -/
theorem prefixScaleGenerator_order_eq
    (F : SameFundamentalType J H)
    {m : Nat} (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :
    ordUnit K (H.prefixScaleGenerator hk i) =
      ordUnit K (J.prefixScaleGenerator hk i) := by
  unfold prefixScaleGenerator
  have hidx := prefixIndexEquiv_component_eq
    J.toOrthogonalDecomposition H.toOrthogonalDecomposition hk i
  rw [← hidx]
  exact F.scaleGenerator_order_eq_sameIndex _

/-- Consequently the determinant factors of corresponding stabilized
prefixes have the same refined square class. -/
theorem prefixPairedHyperbolicDeterminantFactor_eq
    (F : SameFundamentalType J H)
    {m : Nat} (hk : m + 1 ≤ N + 2) :
    unitSquareClass K
        (pairedHyperbolicDeterminantFactor (m + 1)
          (H.prefixScaleGenerator hk)) =
      unitSquareClass K
        (pairedHyperbolicDeterminantFactor (m + 1)
          (J.prefixScaleGenerator hk)) :=
  pairedHyperbolicDeterminantFactor_eq_of_orders _ _ _
    (F.prefixScaleGenerator_order_eq hk)

end SameFundamentalType

/-- O'Meara 93:28(i) survives simultaneous two-plane stabilization. -/
theorem omeara9328ConditionI_saturationStable
    {J : JordanDecomposition q L (N + 2)}
    {H : JordanDecomposition r M (N + 2)}
    (F : SameFundamentalType J H)
    (hI : J.Omeara9328ConditionI H) :
    J.saturationStableJordan.Omeara9328ConditionI
      H.saturationStableJordan := by
  intro i
  rw [J.saturationStableJordan_fundamentalIdeal]
  let hk : i.val + 1 ≤ N + 2 := by omega
  let fJ : Kˣ := pairedHyperbolicDeterminantFactor (i.val + 1)
    (J.prefixScaleGenerator hk)
  let fH : Kˣ := pairedHyperbolicDeterminantFactor (i.val + 1)
    (H.prefixScaleGenerator hk)
  let dJ : Kˣ := J.prefixDeterminantUnit i
  let dH : Kˣ := H.prefixDeterminantUnit i
  let sJ : Kˣ := J.saturationStableJordan.prefixDeterminantUnit i
  let sH : Kˣ := H.saturationStableJordan.prefixDeterminantUnit i
  have hclassJ : unitSquareClass K sJ = unitSquareClass K (fJ * dJ) := by
    rw [unitSquareClass_mul]
    exact J.unitSquareClass_saturationStable_prefixDeterminantUnit i
  have hclassH : unitSquareClass K sH = unitSquareClass K (fH * dH) := by
    rw [unitSquareClass_mul]
    exact H.unitSquareClass_saturationStable_prefixDeterminantUnit i
  have hfactor : unitSquareClass K fH = unitSquareClass K fJ :=
    F.prefixPairedHyperbolicDeterminantFactor_eq hk
  have htarget : unitSquareClass K (fJ * dH) = unitSquareClass K sH := by
    rw [unitSquareClass_mul, ← hfactor, ← unitSquareClass_mul]
    exact hclassH.symm
  have hsource : unitSquareClass K (fJ * dJ) = unitSquareClass K sJ :=
    hclassJ.symm
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (fJ * dH) (fJ * dJ) (J.fundamentalIdeal i) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      fJ dH dJ (J.fundamentalIdeal i)).2 (hI i)
  exact BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (fJ * dH) sH (fJ * dJ) sJ (J.fundamentalIdeal i)
    htarget hsource hcommon

/-- O'Meara 93:28(ii) survives simultaneous two-plane stabilization when
the same coherent fundamental norm generators are retained. -/
theorem omeara9328ConditionIIWith_saturationStable
    {J : JordanDecomposition q L (N + 2)}
    {H : JordanDecomposition r M (N + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hII : J.Omeara9328ConditionIIWith H A) :
    J.saturationStableJordan.Omeara9328ConditionIIWith
      H.saturationStableJordan A.saturationStable := by
  intro i htrigger
  rw [J.saturationStableJordan_fundamentalIdeal,
    J.saturationStableJordan_fourNormOverWeightIdealWith] at htrigger
  exact saturationStablePrefix_embedsInto F (by omega)
    (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
    (hII i htrigger)

/-- O'Meara 93:28(iii) survives simultaneous two-plane stabilization with
the same coherent fundamental norm generators. -/
theorem omeara9328ConditionIIIWith_saturationStable
    {J : JordanDecomposition q L (N + 2)}
    {H : JordanDecomposition r M (N + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    J.saturationStableJordan.Omeara9328ConditionIIIWith
      H.saturationStableJordan A.saturationStable := by
  intro i htrigger
  rw [J.saturationStableJordan_fundamentalIdeal,
    J.saturationStableJordan_fourNormOverWeightIdealWith] at htrigger
  exact saturationStablePrefix_embedsInto F (by omega)
    (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
    (hIII i htrigger)

/-- All three semantic hypotheses of 93:28 are preserved by simultaneous
rank stabilization. -/
theorem omeara9328ConditionsWith_saturationStable
    {J : JordanDecomposition q L (N + 2)}
    {H : JordanDecomposition r M (N + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (h : J.Omeara9328ConditionsWith H A) :
    J.saturationStableJordan.Omeara9328ConditionsWith
      H.saturationStableJordan A.saturationStable := by
  exact ⟨omeara9328ConditionI_saturationStable F h.1,
    omeara9328ConditionIIWith_saturationStable F A h.2.1,
    omeara9328ConditionIIIWith_saturationStable F A h.2.2⟩

end JordanDecomposition
end Lattice

end Bong
