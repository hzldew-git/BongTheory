/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourConditionTransfer

/-!
# Lifting the 93:28 conditions from the rank-four residual system

The negative-adjunction reduction is reversible at the level of O'Meara's
three semantic conditions.  Determinant congruences are lifted by restoring
the two common determinant factors and cancelling them.  Prefix-space
representations are lifted by restoring the common negative source prefix
and common hyperbolic tower, then applying ordinary Witt cancellation.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The determinant congruence at one boundary lifts from the rank-four
residual pair to the original saturated pair.  The pointwise form is useful
in the necessity proof, where the first-boundary calculation is transported
through reverse duality before the remaining boundaries are assembled. -/
theorem boundary_conditionI_of_rankFour
    (i : Fin (n + 1))
    (hresidual : BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.prefixDeterminantUnit i)
      (S.sourceJordan.prefixDeterminantUnit i)
      (S.sourceJordan.fundamentalIdeal i)) :
    BONG.GoodBONG.UnitsCongruentModulo
      (H.prefixDeterminantUnit i) (J.prefixDeterminantUnit i)
      (J.fundamentalIdeal i) := by
  rw [S.sourceJordan_fundamentalIdeal_eq] at hresidual
  let hk : i.val + 1 ≤ n + 2 := by omega
  let sourcePrefix :=
    J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1)
  let towerForm := BONG.blockOrthogonalForm i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerForm hk)
  let towerLattice := BONG.blockProductLattice i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerLattice hk)
  let dN : Kˣ := determinantUnit
    (sourcePrefix.space.rescaleUnit (-1 : Kˣ)) sourcePrefix.lattice
  let dP : Kˣ := determinantUnit towerForm towerLattice
  let dJ : Kˣ := J.prefixDeterminantUnit i
  let dH : Kˣ := H.prefixDeterminantUnit i
  let dS : Kˣ := S.sourceJordan.prefixDeterminantUnit i
  let dT : Kˣ := S.targetJordan.prefixDeterminantUnit i
  have hsource :
      unitSquareClass K (dN * dJ) = unitSquareClass K (dP * dS) := by
    rw [unitSquareClass_mul, unitSquareClass_mul]
    exact S.sourcePrefixDeterminantRelation i
  have htarget :
      unitSquareClass K (dN * dH) = unitSquareClass K (dP * dT) := by
    rw [unitSquareClass_mul, unitSquareClass_mul]
    exact S.targetPrefixDeterminantRelation i
  have htower : BONG.GoodBONG.UnitsCongruentModulo
      (dP * dT) (dP * dS) (J.fundamentalIdeal i) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      dP dT dS (J.fundamentalIdeal i)).2 hresidual
  have hnegative : BONG.GoodBONG.UnitsCongruentModulo
      (dN * dH) (dN * dJ) (J.fundamentalIdeal i) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (dP * dT) (dN * dH) (dP * dS) (dN * dJ)
      (J.fundamentalIdeal i) htarget.symm hsource.symm htower
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    dN dH dJ (J.fundamentalIdeal i)).1 hnegative

/-- Condition 93:28(i) lifts from the rank-four residual pair to the
original saturated pair. -/
theorem omeara9328ConditionI_of_rankFour
    (hI : S.sourceJordan.Omeara9328ConditionI S.targetJordan) :
    J.Omeara9328ConditionI H := by
  intro i
  exact S.boundary_conditionI_of_rankFour i (hI i)

/-- Every representation between corresponding rank-four residual prefixes
lifts to a representation between the original prefixes. -/
theorem prefix_embedsInto_of_rankFour
    [FiniteDimensional K Z]
    (i : Fin (n + 1)) (s : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1))
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1)) s := by
  let hk : i.val + 1 ≤ n + 2 := by omega
  let JP := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let HP := H.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let SP := S.sourceJordan.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (i.val + 1)
  let TP := S.targetJordan.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (i.val + 1)
  let N := JP.space.rescaleUnit (-1 : Kˣ)
  let P := BONG.blockOrthogonalForm i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerForm hk)
  let PL := BONG.blockProductLattice i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerLattice hk)
  letI : Module.Finite K (∀ j, S.prefixCommonTowerCarrier hk j) :=
    PL.moduleFinite
  letI : Module.Finite K JP.carrier := JP.lattice.moduleFinite
  letI : Module.Finite K HP.carrier := HP.lattice.moduleFinite
  letI : Module.Finite K SP.carrier := SP.lattice.moduleFinite
  letI : Module.Finite K TP.carrier := TP.lattice.moduleFinite
  rcases h with ⟨f⟩
  let commonToNegative : QuadraticSpace.Isometry
      (P.orthogonalSum SP.space) (N.orthogonalSum JP.space) :=
    ((S.sourcePrefixGatheredReduction hk).toQuadraticSpaceIsometry.symm).trans
      (S.sourceNegativeAdjunctionPrefixProductIsometry hk).toQuadraticSpaceIsometry
  let negativeToTargetCommon : QuadraticSpace.Isometry
      (N.orthogonalSum HP.space) (P.orthogonalSum TP.space) :=
    ((S.targetNegativeAdjunctionPrefixProductIsometry hk).toQuadraticSpaceIsometry.symm).trans
      (S.targetPrefixGatheredReduction hk).toQuadraticSpaceIsometry
  let targetFromCommon : QuadraticSpace.Isometry
      (P.orthogonalSum (TP.space.orthogonalSum s))
      (N.orthogonalSum (HP.space.orthogonalSum s)) :=
    (QuadraticSpace.orthogonalSumAssoc P TP.space s).symm.trans <|
      ((negativeToTargetCommon.symm).orthogonalSum
        (QuadraticSpace.Isometry.refl s)).trans <|
        QuadraticSpace.orthogonalSumAssoc N HP.space s
  let commonRepresentation : QuadraticSpace.Representation
      (P.orthogonalSum SP.space)
      (P.orthogonalSum (TP.space.orthogonalSum s)) :=
    (QuadraticSpace.Representation.refl P).orthogonalSum f
  have total :
      (N.orthogonalSum (HP.space.orthogonalSum s)).Represents
        (N.orthogonalSum JP.space) :=
    ⟨targetFromCommon.toRepresentation.trans
      (commonRepresentation.trans commonToNegative.symm.toRepresentation)⟩
  exact QuadraticSpace.orthogonalSumCancelRepresents
    N N JP.space (HP.space.orthogonalSum s)
    (QuadraticSpace.Isometry.refl N) total

/-- Condition 93:28(ii) lifts from the rank-four residual pair. -/
theorem omeara9328ConditionIIWith_of_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (hII : S.sourceJordan.Omeara9328ConditionIIWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A)) :
    J.Omeara9328ConditionIIWith H A := by
  intro i htrigger
  have htrigger' : S.sourceJordan.fundamentalIdeal i <
      S.sourceJordan.fourNormOverWeightIdealWith
        (S.sourceFundamentalNormGeneratorChoice A)
          (boundaryRightIndex i) := by
    rw [S.sourceJordan_fundamentalIdeal_eq,
      S.sourceJordan_fourNormOverWeightIdealWith_eq]
    exact htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value] using
    S.prefix_embedsInto_of_rankFour i
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
      (hII i htrigger')

/-- Condition 93:28(iii) lifts from the rank-four residual pair. -/
theorem omeara9328ConditionIIIWith_of_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (hIII : S.sourceJordan.Omeara9328ConditionIIIWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A)) :
    J.Omeara9328ConditionIIIWith H A := by
  intro i htrigger
  have htrigger' : S.sourceJordan.fundamentalIdeal i <
      S.sourceJordan.fourNormOverWeightIdealWith
        (S.sourceFundamentalNormGeneratorChoice A)
          (boundaryLeftIndex i) := by
    rw [S.sourceJordan_fundamentalIdeal_eq,
      S.sourceJordan_fourNormOverWeightIdealWith_eq]
    exact htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value] using
    S.prefix_embedsInto_of_rankFour i
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
      (hIII i htrigger')

/-- The complete 93:28 condition package lifts from the residual system. -/
theorem omeara9328ConditionsWith_of_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (h : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A)) :
    J.Omeara9328ConditionsWith H A :=
  ⟨S.omeara9328ConditionI_of_rankFour h.1,
    S.omeara9328ConditionIIWith_of_rankFour A h.2.1,
    S.omeara9328ConditionIIIWith_of_rankFour A h.2.2⟩

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
