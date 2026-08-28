/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328BoundaryAugmentation
import Bong.Lattice.OmearaCommonAdjunctionConditions
import Bong.Lattice.Omeara9328StabilizationConditions
import Bong.Lattice.Omeara9328StabilizationCancellation
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Cancelling the auxiliary adjunctions in O'Meara 93:28

The necessity proof is first carried out after paired-hyperbolic
stabilization and a common saturated adjunction.  This file proves the
reverse implications for all three conditions, using determinant-factor
cancellation and finite-dimensional Witt cancellation.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w x z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K X} {e : QuadraticSpace K Z}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K X}
  {n : Nat}

/-- Cancel two hyperbolic planes at every level of a paired stabilization
from a quadratic-space representation. -/
theorem embedsInto_of_pairedHyperbolicExtension
    {p : QuadraticSpace K V} {a : QuadraticSpace K W}
    (L : Lattice K V) (M : Lattice K W)
    [FiniteDimensional K Z] :
    (t : Nat) → (sourceScale targetScale : Fin t → Kˣ) →
      (∀ i, ordUnit K (sourceScale i) = ordUnit K (targetScale i)) →
      QuadraticSpace.EmbedsInto
        (pairedHyperbolicExtensionForm p t sourceScale)
        ((pairedHyperbolicExtensionForm a t targetScale).orthogonalSum e) →
      QuadraticSpace.EmbedsInto p (a.orthogonalSum e)
  | 0, sourceScale, targetScale, _, h => by
      let sourceBase :=
        (pairedHyperbolicExtensionBaseIsometry p L sourceScale)
          |>.toQuadraticSpaceIsometry
      let targetBase :=
        (pairedHyperbolicExtensionBaseIsometry a M targetScale)
          |>.toQuadraticSpaceIsometry
      rcases h with ⟨f⟩
      exact ⟨(targetBase.orthogonalSum
          (QuadraticSpace.Isometry.refl e)).toRepresentation.trans
        (f.trans sourceBase.symm.toRepresentation)⟩
  | t + 1, sourceScale, targetScale, hord, h => by
      let sourceHead := QuadraticSpace.hyperbolicPlane (sourceScale 0)
      let targetHead := QuadraticSpace.hyperbolicPlane (targetScale 0)
      let sourceTail := pairedHyperbolicExtensionForm p t (Fin.tail sourceScale)
      let targetTail := pairedHyperbolicExtensionForm a t (Fin.tail targetScale)
      let sourceTailLattice := pairedHyperbolicExtensionLattice L t
      let targetTailLattice := pairedHyperbolicExtensionLattice M t
      letI : Module.Finite K (PairedHyperbolicExtension K V t) :=
        sourceTailLattice.moduleFinite
      letI : Module.Finite K (PairedHyperbolicExtension K W t) :=
        targetTailLattice.moduleFinite
      let head := (scaledHyperbolicChangeScaleIsometry
        (sourceScale 0) (targetScale 0) (hord 0)).toQuadraticSpaceIsometry
      rcases h with ⟨f⟩
      let targetReframe : QuadraticSpace.Isometry
          ((targetHead.orthogonalSum
            (targetHead.orthogonalSum targetTail)).orthogonalSum e)
          (targetHead.orthogonalSum
            (targetHead.orthogonalSum (targetTail.orthogonalSum e))) :=
        (QuadraticSpace.orthogonalSumAssoc targetHead
          (targetHead.orthogonalSum targetTail) e).trans <|
          (QuadraticSpace.Isometry.refl targetHead).orthogonalSum
            (QuadraticSpace.orthogonalSumAssoc targetHead targetTail e)
      have total :
          (targetHead.orthogonalSum
            (targetHead.orthogonalSum (targetTail.orthogonalSum e))).Represents
          (sourceHead.orthogonalSum (sourceHead.orthogonalSum sourceTail)) :=
        ⟨targetReframe.toRepresentation.trans f⟩
      have once := QuadraticSpace.orthogonalSumCancelRepresents
        sourceHead targetHead (sourceHead.orthogonalSum sourceTail)
        (targetHead.orthogonalSum (targetTail.orthogonalSum e)) head total
      have twice := QuadraticSpace.orthogonalSumCancelRepresents
        sourceHead targetHead sourceTail (targetTail.orthogonalSum e) head once
      exact embedsInto_of_pairedHyperbolicExtension L M t
        (Fin.tail sourceScale) (Fin.tail targetScale)
        (fun i ↦ hord i.succ) twice

/-- Cancel a simultaneous paired-hyperbolic stabilization from a prefix
representation. -/
theorem saturationStablePrefix_embedsInto_cancel
    [FiniteDimensional K Z]
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    {m : Nat} (hk : m + 1 ≤ n + 2)
    (e : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.saturationStableJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1))
      (H.saturationStableJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)) e) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)) e := by
  let sourcePrefix :=
    J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let targetPrefix :=
    H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let sourceGather := J.saturationStablePrefixGatherIsometry hk
  let targetGather := H.saturationStablePrefixGatherIsometry hk
  have hscale : ∀ i,
      ordUnit K (J.prefixScaleGenerator hk i) =
        ordUnit K (H.prefixScaleGenerator hk i) := by
    intro i
    unfold prefixScaleGenerator
    have hidx := prefixIndexEquiv_component_eq
      J.toOrthogonalDecomposition H.toOrthogonalDecomposition hk i
    rw [← hidx]
    exact (F.scaleGenerator_order_eq_sameIndex _).symm
  have towerRepresentation : QuadraticSpace.EmbedsInto
      (pairedHyperbolicExtensionForm sourcePrefix.space (m + 1)
        (J.prefixScaleGenerator hk))
      ((pairedHyperbolicExtensionForm targetPrefix.space (m + 1)
        (H.prefixScaleGenerator hk)).orthogonalSum e) := by
    rcases h with ⟨f⟩
    exact ⟨(targetGather.toQuadraticSpaceIsometry.orthogonalSum
        (QuadraticSpace.Isometry.refl e)).toRepresentation.trans
      (f.trans sourceGather.symm.toQuadraticSpaceIsometry.toRepresentation)⟩
  exact embedsInto_of_pairedHyperbolicExtension
    sourcePrefix.lattice targetPrefix.lattice (m + 1)
      (J.prefixScaleGenerator hk) (H.prefixScaleGenerator hk)
      hscale towerRepresentation

/-- Condition 93:28(i) descends through simultaneous paired-hyperbolic
stabilization. -/
theorem omeara9328ConditionI_of_saturationStable
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (hI : J.saturationStableJordan.Omeara9328ConditionI
      H.saturationStableJordan) :
    J.Omeara9328ConditionI H := by
  intro i
  have hStable := hI i
  rw [J.saturationStableJordan_fundamentalIdeal] at hStable
  let hk : i.val + 1 ≤ n + 2 := by omega
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
  have htarget : unitSquareClass K sH = unitSquareClass K (fJ * dH) := by
    rw [unitSquareClass_mul, ← hfactor, ← unitSquareClass_mul]
    exact hclassH
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (fJ * dH) (fJ * dJ) (J.fundamentalIdeal i) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      sH (fJ * dH) sJ (fJ * dJ) (J.fundamentalIdeal i)
      htarget hclassJ hStable
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    fJ dH dJ (J.fundamentalIdeal i)).1 hcommon

/-- Condition 93:28(ii) descends through simultaneous stabilization. -/
theorem omeara9328ConditionIIWith_of_saturationStable
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hII : J.saturationStableJordan.Omeara9328ConditionIIWith
      H.saturationStableJordan A.saturationStable) :
    J.Omeara9328ConditionIIWith H A := by
  intro i htrigger
  have htriggerStable : J.saturationStableJordan.fundamentalIdeal i <
      J.saturationStableJordan.fourNormOverWeightIdealWith
        A.saturationStable (boundaryRightIndex i) := by
    rw [J.saturationStableJordan_fundamentalIdeal,
      J.saturationStableJordan_fourNormOverWeightIdealWith]
    exact htrigger
  simpa only [FundamentalNormGeneratorChoice.saturationStable_value] using
    saturationStablePrefix_embedsInto_cancel F (by omega)
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
      (hII i htriggerStable)

/-- Condition 93:28(iii) descends through simultaneous stabilization. -/
theorem omeara9328ConditionIIIWith_of_saturationStable
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (hIII : J.saturationStableJordan.Omeara9328ConditionIIIWith
      H.saturationStableJordan A.saturationStable) :
    J.Omeara9328ConditionIIIWith H A := by
  intro i htrigger
  have htriggerStable : J.saturationStableJordan.fundamentalIdeal i <
      J.saturationStableJordan.fourNormOverWeightIdealWith
        A.saturationStable (boundaryLeftIndex i) := by
    rw [J.saturationStableJordan_fundamentalIdeal,
      J.saturationStableJordan_fourNormOverWeightIdealWith]
    exact htrigger
  simpa only [FundamentalNormGeneratorChoice.saturationStable_value] using
    saturationStablePrefix_embedsInto_cancel F (by omega)
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
      (hIII i htriggerStable)

/-- The full 93:28 package descends through simultaneous stabilization. -/
theorem omeara9328ConditionsWith_of_saturationStable
    {J : JordanDecomposition q L (n + 2)}
    {H : JordanDecomposition r M (n + 2)}
    (F : SameFundamentalType J H)
    (A : FundamentalNormGeneratorChoice J)
    (h : J.saturationStableJordan.Omeara9328ConditionsWith
      H.saturationStableJordan A.saturationStable) :
    J.Omeara9328ConditionsWith H A :=
  ⟨omeara9328ConditionI_of_saturationStable F h.1,
    omeara9328ConditionIIWith_of_saturationStable F A h.2.1,
    omeara9328ConditionIIIWith_of_saturationStable F A h.2.2⟩

/-- Cancel the literal common prefix from a representation between two
common adjunctions. -/
theorem commonAdjunctionPrefix_embedsInto_cancel
    [FiniteDimensional K Z]
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    {m : Nat} (hk : m + 1 ≤ n + 2)
    (e : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      ((P.commonAdjunctionJordan J FPJ hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1))
      ((P.commonAdjunctionJordan H FPH hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)) e) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)) e := by
  let commonPrefix :=
    P.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let sourcePrefix :=
    J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let targetPrefix :=
    H.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)
  let sourceGather := P.commonAdjunctionPrefixGatherIsometry J FPJ hP hk
  let targetGather := P.commonAdjunctionPrefixGatherIsometry H FPH hP hk
  letI : Module.Finite K commonPrefix.carrier :=
    commonPrefix.lattice.moduleFinite
  letI : Module.Finite K sourcePrefix.carrier :=
    sourcePrefix.lattice.moduleFinite
  letI : Module.Finite K targetPrefix.carrier :=
    targetPrefix.lattice.moduleFinite
  rcases h with ⟨f⟩
  let targetReframe : QuadraticSpace.Isometry
      (((P.commonAdjunctionJordan H FPH hP).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (m + 1)).space.orthogonalSum e)
      (commonPrefix.space.orthogonalSum (targetPrefix.space.orthogonalSum e)) :=
    (targetGather.toQuadraticSpaceIsometry.orthogonalSum
      (QuadraticSpace.Isometry.refl e)).trans
        (QuadraticSpace.orthogonalSumAssoc
          commonPrefix.space targetPrefix.space e)
  have total :
      (commonPrefix.space.orthogonalSum
        (targetPrefix.space.orthogonalSum e)).Represents
      (commonPrefix.space.orthogonalSum sourcePrefix.space) :=
    ⟨targetReframe.toRepresentation.trans
      (f.trans sourceGather.symm.toQuadraticSpaceIsometry.toRepresentation)⟩
  exact QuadraticSpace.orthogonalSumCancelRepresents
    commonPrefix.space commonPrefix.space sourcePrefix.space
      (targetPrefix.space.orthogonalSum e)
      (QuadraticSpace.Isometry.refl commonPrefix.space) total

/-- Condition 93:28(i) descends after cancelling a common saturated
adjunction. -/
theorem omeara9328ConditionI_of_commonAdjunction
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (hP : P.IsSaturated)
    (hI : (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionI
      (P.commonAdjunctionJordan H FPH hP)) :
    J.Omeara9328ConditionI H := by
  intro i
  have hAug := hI i
  rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP] at hAug
  let dP : Kˣ := P.prefixDeterminantUnit i
  let dJ : Kˣ := J.prefixDeterminantUnit i
  let dH : Kˣ := H.prefixDeterminantUnit i
  let dPJ : Kˣ :=
    (P.commonAdjunctionJordan J FPJ hP).prefixDeterminantUnit i
  let dPH : Kˣ :=
    (P.commonAdjunctionJordan H FPH hP).prefixDeterminantUnit i
  have hsource : unitSquareClass K dPJ = unitSquareClass K (dP * dJ) := by
    rw [unitSquareClass_mul]
    exact P.unitSquareClass_commonAdjunction_prefixDeterminantUnit J FPJ hP i
  have htarget : unitSquareClass K dPH = unitSquareClass K (dP * dH) := by
    rw [unitSquareClass_mul]
    exact P.unitSquareClass_commonAdjunction_prefixDeterminantUnit H FPH hP i
  have hcommon : BONG.GoodBONG.UnitsCongruentModulo
      (dP * dH) (dP * dJ) (J.fundamentalIdeal i) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      dPH (dP * dH) dPJ (dP * dJ) (J.fundamentalIdeal i)
      htarget hsource hAug
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    dP dH dJ (J.fundamentalIdeal i)).1 hcommon

/-- Condition 93:28(ii) descends after cancelling a common saturated
adjunction. -/
theorem omeara9328ConditionIIWith_of_commonAdjunction
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (hII : (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionIIWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP)) :
    J.Omeara9328ConditionIIWith H A := by
  intro i htrigger
  have htriggerAug :
      (P.commonAdjunctionJordan J FPJ hP).fundamentalIdeal i <
        (P.commonAdjunctionJordan J FPJ hP).fourNormOverWeightIdealWith
          (A.commonAdjunction FPJ hP) (boundaryRightIndex i) := by
    rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP,
      P.commonAdjunctionJordan_fourNormOverWeightIdealWith_eq_right
        J FPJ hP A]
    exact htrigger
  simpa only [FundamentalNormGeneratorChoice.commonAdjunction_value] using
    commonAdjunctionPrefix_embedsInto_cancel FPJ FPH hP (by omega)
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
      (hII i htriggerAug)

/-- Condition 93:28(iii) descends after cancelling a common saturated
adjunction. -/
theorem omeara9328ConditionIIIWith_of_commonAdjunction
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (hIII : (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionIIIWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP)) :
    J.Omeara9328ConditionIIIWith H A := by
  intro i htrigger
  have htriggerAug :
      (P.commonAdjunctionJordan J FPJ hP).fundamentalIdeal i <
        (P.commonAdjunctionJordan J FPJ hP).fourNormOverWeightIdealWith
          (A.commonAdjunction FPJ hP) (boundaryLeftIndex i) := by
    rw [P.commonAdjunctionJordan_fundamentalIdeal_eq_right J FPJ hP,
      P.commonAdjunctionJordan_fourNormOverWeightIdealWith_eq_right
        J FPJ hP A]
    exact htrigger
  simpa only [FundamentalNormGeneratorChoice.commonAdjunction_value] using
    commonAdjunctionPrefix_embedsInto_cancel FPJ FPH hP (by omega)
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
      (hIII i htriggerAug)

/-- The full 93:28 package descends after cancelling a common saturated
adjunction. -/
theorem omeara9328ConditionsWith_of_commonAdjunction
    {P : JordanDecomposition q L (n + 2)}
    {J : JordanDecomposition r M (n + 2)}
    {H : JordanDecomposition s N (n + 2)}
    (FPJ : SameFundamentalType P J)
    (FPH : SameFundamentalType P H)
    (A : FundamentalNormGeneratorChoice J)
    (hP : P.IsSaturated)
    (h : (P.commonAdjunctionJordan J FPJ hP).Omeara9328ConditionsWith
      (P.commonAdjunctionJordan H FPH hP) (A.commonAdjunction FPJ hP)) :
    J.Omeara9328ConditionsWith H A :=
  ⟨omeara9328ConditionI_of_commonAdjunction FPJ FPH hP h.1,
    omeara9328ConditionIIWith_of_commonAdjunction FPJ FPH A hP h.2.1,
    omeara9328ConditionIIIWith_of_commonAdjunction FPJ FPH A hP h.2.2⟩

end Lattice.JordanDecomposition

end Bong
