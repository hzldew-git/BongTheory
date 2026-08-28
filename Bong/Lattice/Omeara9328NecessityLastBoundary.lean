/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NecessityFirstBoundary
import Bong.Lattice.Omeara9328RankFourConditionLift
import Bong.Lattice.Omeara9328ReverseDualCondition
import Bong.Lattice.OrthogonalDecompositionFirstPrefix
import Bong.QuadraticSpace.HyperbolicBoundaryWitt

/-!
# O'Meara 93:28 necessity at the last boundary

This file formalizes the end-boundary case of O'Meara's Step 2.  The first
boundary theorem is applied to the reverse-dual residual chains with the
negative coherent norm-generator choice.  The resulting representation by
`[-a]` is reversed using the split quaternary Witt maneuver, transported to
the original last suffixes, and then converted to condition (ii) on the
original prefixes by complementary-summand cancellation.
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

namespace FundamentalNormGeneratorChoice

noncomputable def negReverseDual
    {m : Nat} {J : JordanDecomposition q L m}
    (A : FundamentalNormGeneratorChoice J) :
    FundamentalNormGeneratorChoice J.reverseDual where
  value := fun i ↦ -A.reverseDual.value i
  spec := fun i ↦ (A.reverseDual.spec i).neg

@[simp]
theorem negReverseDual_value
    {m : Nat} {J : JordanDecomposition q L m}
    (A : FundamentalNormGeneratorChoice J) (i : Fin m) :
    A.negReverseDual.value i = -A.reverseDual.value i :=
  rfl

end FundamentalNormGeneratorChoice

@[simp]
theorem negReverseDual_fourNormOverWeightIdealWith
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (A : FundamentalNormGeneratorChoice J) (i : Fin (m + 1)) :
    J.reverseDual.fourNormOverWeightIdealWith A.negReverseDual i =
      J.fourNormOverWeightIdealWith A (Fin.rev i) := by
  unfold fourNormOverWeightIdealWith
  rw [FundamentalNormGeneratorChoice.negReverseDual_value,
    ordUnit_neg]
  exact J.reverseDual_fourNormOverWeightIdealWith A i

noncomputable def negReverseDualGeneratorLineIsometry
    {m : Nat} (J : JordanDecomposition q L m)
    (A : FundamentalNormGeneratorChoice J) (i : Fin m) :
    QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine (A.negReverseDual.value i))
      (QuadraticSpace.scaledLine (-A.value (Fin.rev i))) where
  toLinearEquiv := J.reverseDualGeneratorLineLinearEquiv A i
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.scaledLine_bilin_apply,
      reverseDualGeneratorLineLinearEquiv_apply,
      FundamentalNormGeneratorChoice.negReverseDual_value,
      FundamentalNormGeneratorChoice.reverseDual_value,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring

noncomputable def twoHyperbolicPairsToScaledTowerIsometry (s : Kˣ) :
    QuadraticSpace.Isometry
      (QuadraticSpace.twoHyperbolicPairsDiagonalForm (K := K))
      (QuadraticSpace.scaledZeroOmearaTowerForm s 2) := by
  let pair : Fin 2 → Kˣ := ![(1 : Kˣ), -1]
  have hpairSquare : IsSquare (-(pair 0 / pair 1)) := by
    refine ⟨1, ?_⟩
    simp [pair]
  let pairToHyperbolicRaw :=
    (QuadraticSpace.finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      (pair 0) (pair 1) hpairSquare).some
  have hpairCoefficients : BONG.GoodBONG.diagonalUnitCoefficients pair =
      ![(pair 0 : K), (pair 1 : K)] := by
    funext i
    fin_cases i <;> rfl
  let pairToHyperbolic : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients pair)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero pair))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
    simpa only [hpairCoefficients] using pairToHyperbolicRaw
  have hpairsCoefficients :
      BONG.GoodBONG.diagonalUnitCoefficients
          (BONG.GoodBONG.twoHyperbolicPairsUnits (K := K)) =
        BONG.GoodBONG.diagonalUnitCoefficients
          (Fin.append pair pair) := by
    funext i
    fin_cases i <;> rfl
  let pairsToHyperbolic : QuadraticSpace.Isometry
      (QuadraticSpace.twoHyperbolicPairsDiagonalForm (K := K))
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ))) := by
    have h := (QuadraticSpace.finiteDiagonalOrthogonalSumIsometry
      pair pair).symm.trans
        (pairToHyperbolic.orthogonalSum pairToHyperbolic)
    simpa only [QuadraticSpace.twoHyperbolicPairsDiagonalForm,
      hpairsCoefficients] using h
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairsToTowerOne := pairsToHyperbolic.trans <|
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  exact pairsToTowerOne.trans
    (QuadraticSpace.scaledZeroOmearaTowerChangeScaleSpaceIsometry
      (1 : Kˣ) s 2)

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

noncomputable def reverseResidualSystem :
    Omeara9328RankFourReductionSystem
      S.sourceJordan.reverseDual S.targetJordan.reverseDual where
  sourceSaturated := S.sourceJordan_isSaturated.reverseDual
  targetSaturated := S.targetJordan_isSaturated.reverseDual
  fundamentalType := S.residualFundamentalType.reverseDual
  componentRank_atLeastTwo := by
    intro i
    rw [reverseDual_componentRank, S.sourceJordan_componentRank]
    omega

noncomputable def reverseResidualIsometry
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (S.reverseResidualSystem).sourceCarrier
        (S.reverseResidualSystem).sourceForm)
      (BONG.blockOrthogonalForm (n + 1)
        (S.reverseResidualSystem).targetCarrier
        (S.reverseResidualSystem).targetForm)
      (BONG.blockProductLattice (n + 1)
        (S.reverseResidualSystem).sourceCarrier
        (S.reverseResidualSystem).sourceLattice)
      (BONG.blockProductLattice (n + 1)
        (S.reverseResidualSystem).targetCarrier
        (S.reverseResidualSystem).targetLattice) :=
  (S.reverseResidualSystem).residualIsometryOfOriginalIsometry f.dual

theorem reverseResidual_firstBoundary_conditionI
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    BONG.GoodBONG.UnitsCongruentModulo
      (S.targetJordan.reverseDual.prefixDeterminantUnit 0)
      (S.sourceJordan.reverseDual.prefixDeterminantUnit 0)
      (S.sourceJordan.reverseDual.fundamentalIdeal 0) := by
  let R := S.reverseResidualSystem
  let g := S.reverseResidualIsometry f
  exact R.boundary_conditionI_of_rankFour 0
    (R.firstBoundary_conditionI g)

theorem reverseResidual_firstBoundary_conditionIII
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)) :
    S.sourceJordan.reverseDual.fundamentalIdeal 0 <
        S.sourceJordan.reverseDual.fourNormOverWeightIdeal
          (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (S.sourceJordan.reverseDual.fundamentalNormGenerator
            (boundaryLeftIndex 0))) := by
  intro htrigger
  let R := S.reverseResidualSystem
  let g := S.reverseResidualIsometry f
  let A := canonicalFundamentalNormGeneratorChoice
    S.sourceJordan.reverseDual
  have htriggerR : R.sourceJordan.fundamentalIdeal 0 <
      R.sourceJordan.fourNormOverWeightIdealWith
        (R.sourceFundamentalNormGeneratorChoice A)
          (boundaryLeftIndex 0) := by
    rw [R.sourceJordan_fundamentalIdeal_eq,
      R.sourceJordan_fourNormOverWeightIdealWith_eq]
    simpa only [A, fourNormOverWeightIdealWith_canonical] using htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value, Fin.val_zero,
    zero_add] using
    R.prefix_embedsInto_of_rankFour 0
      (QuadraticSpace.scaledLine
        (S.sourceJordan.reverseDual.fundamentalNormGenerator
          (boundaryLeftIndex 0)))
      (R.firstBoundary_conditionIIIWith
        (R.sourceFundamentalNormGeneratorChoice A) g htriggerR)

theorem reverseResidual_firstBoundary_conditionIIIWithNeg
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    S.sourceJordan.reverseDual.fundamentalIdeal 0 <
        S.sourceJordan.reverseDual.fourNormOverWeightIdealWith
          A.negReverseDual (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.targetJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (A.negReverseDual.value (boundaryLeftIndex 0))) := by
  intro htrigger
  let R := S.reverseResidualSystem
  let g := S.reverseResidualIsometry f
  let N := A.negReverseDual
  have htriggerR : R.sourceJordan.fundamentalIdeal 0 <
      R.sourceJordan.fourNormOverWeightIdealWith
        (R.sourceFundamentalNormGeneratorChoice N)
          (boundaryLeftIndex 0) := by
    rw [R.sourceJordan_fundamentalIdeal_eq,
      R.sourceJordan_fourNormOverWeightIdealWith_eq]
    exact htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value, Fin.val_zero,
    zero_add] using
    R.prefix_embedsInto_of_rankFour 0
      (QuadraticSpace.scaledLine
        (N.value (boundaryLeftIndex 0)))
      (R.firstBoundary_conditionIIIWith
        (R.sourceFundamentalNormGeneratorChoice N) g htriggerR)

theorem reverseResidual_firstBoundary_conditionIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    S.sourceJordan.reverseDual.fundamentalIdeal 0 <
        S.sourceJordan.reverseDual.fourNormOverWeightIdealWith
          A.negReverseDual (boundaryLeftIndex 0) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.targetJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (S.sourceJordan.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice 1)
        (QuadraticSpace.scaledLine
          (-A.negReverseDual.value (boundaryLeftIndex 0))) := by
  intro htrigger
  let R := S.reverseResidualSystem
  let sourcePrefix := S.sourceJordan.reverseDual.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice 1
  let targetPrefix := S.targetJordan.reverseDual.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice 1
  let sourceComponentToPrefix :=
    S.sourceJordan.reverseDual.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry.toQuadraticSpaceIsometry
  let targetComponentToPrefix :=
    S.targetJordan.reverseDual.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry.toQuadraticSpaceIsometry
  have hrevZero : Fin.rev (0 : Fin (n + 2)) = Fin.last (n + 1) := by
    apply Fin.ext
    simp
  let componentToTower : QuadraticSpace.Isometry
      (S.sourceJordan.reverseDual.component 0).space
      (QuadraticSpace.scaledZeroOmearaTowerForm
        (S.sourceJordan.scaleGenerator (Fin.last (n + 1))) 2) := by
    change QuadraticSpace.Isometry
      (S.sourceJordan.component (Fin.rev (0 : Fin (n + 2)))).space
      (QuadraticSpace.scaledZeroOmearaTowerForm
        (S.sourceJordan.scaleGenerator (Fin.last (n + 1))) 2)
    rw [hrevZero]
    exact (S.sourceJordan_componentSpace_hyperbolic
      (Fin.last (n + 1))).some
  let pairsToTower := twoHyperbolicPairsToScaledTowerIsometry
    (S.sourceJordan.scaleGenerator (Fin.last (n + 1)))
  have hsplit : sourcePrefix.space.IsIsometric
      (QuadraticSpace.twoHyperbolicPairsDiagonalForm (K := K)) :=
    ⟨sourceComponentToPrefix.symm.trans
      (componentToTower.trans pairsToTower.symm)⟩
  have htargetRank : finrank K targetPrefix.carrier = 4 := by
    rw [← targetComponentToPrefix.toLinearEquiv.finrank_eq]
    change S.targetJordan.reverseDual.componentRank 0 = 4
    rw [reverseDual_componentRank, S.targetJordan_componentRank]
  letI : Module.Finite K targetPrefix.carrier :=
    targetPrefix.lattice.moduleFinite
  have hnegative :=
    S.reverseResidual_firstBoundary_conditionIIIWithNeg f A htrigger
  apply QuadraticSpace.reverseHyperbolicQuaternaryBoundary
    sourcePrefix.space targetPrefix.space
      (-A.negReverseDual.value (boundaryLeftIndex 0))
      htargetRank hsplit
  change QuadraticSpace.EmbedsInto sourcePrefix.space
    (targetPrefix.space.orthogonalSum
      (QuadraticSpace.scaledLine
        (A.negReverseDual.value (boundaryLeftIndex 0)))) at hnegative
  simpa using hnegative

theorem residualLastSuffix_conditionIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    let j : Fin (n + 1) := Fin.last n
    S.sourceJordan.fundamentalIdeal j <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryRightIndex j) →
      QuadraticSpace.EmbedsInto
        (S.targetJordan.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space
        ((S.sourceJordan.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space.orthogonalSum
          (QuadraticSpace.scaledLine
            (A.value (boundaryRightIndex j)))) := by
  dsimp only
  intro htrigger
  let j : Fin (n + 1) := Fin.last n
  let N := A.negReverseDual
  have hrevZero : Fin.rev (0 : Fin (n + 1)) = j := by
    apply Fin.ext
    simp [j]
  have hleftIndex :
      Fin.rev (boundaryLeftIndex (0 : Fin (n + 1))) =
        boundaryRightIndex j := by
    rw [rev_boundaryLeftIndex, hrevZero]
  have htriggerRev :
      S.sourceJordan.reverseDual.fundamentalIdeal 0 <
        S.sourceJordan.reverseDual.fourNormOverWeightIdealWith N
          (boundaryLeftIndex 0) := by
    rw [S.sourceJordan.reverseDual_fundamentalIdeal,
      negReverseDual_fourNormOverWeightIdealWith,
      hrevZero, hleftIndex]
    exact htrigger
  have hrev :=
    S.reverseResidual_firstBoundary_conditionIIWith f A htriggerRev
  let sourceDualRaw :=
    S.sourceJordan.reverseDualBoundaryPrefixSpaceIsometry j
  let targetDualRaw :=
    S.targetJordan.reverseDualBoundaryPrefixSpaceIsometry j
  have hprefixLen : (Fin.rev j).val + 1 = 1 := by
    simp [j]
  let sourceDual : QuadraticSpace.Isometry
      (S.sourceJordan.reverseDual.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).space
      (S.sourceJordan.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (j.val + 1)).space := by
    rw [hprefixLen] at sourceDualRaw
    exact sourceDualRaw
  let targetDual : QuadraticSpace.Isometry
      (S.targetJordan.reverseDual.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice 1).space
      (S.targetJordan.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (j.val + 1)).space := by
    rw [hprefixLen] at targetDualRaw
    exact targetDualRaw
  let lineDual := S.sourceJordan.reverseDualGeneratorLineIsometry A
    (boundaryLeftIndex (0 : Fin (n + 1)))
  let lineIdentify : QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine
        (-N.value (boundaryLeftIndex (0 : Fin (n + 1)))))
      (QuadraticSpace.scaledLine
        (A.value (boundaryRightIndex j))) := by
    simpa only [N, FundamentalNormGeneratorChoice.negReverseDual_value,
      neg_neg, hleftIndex] using lineDual
  rcases hrev with ⟨g⟩
  exact ⟨(sourceDual.orthogonalSum lineIdentify).toRepresentation.trans
    (g.trans targetDual.symm.toRepresentation)⟩

theorem residualLastBoundary_conditionIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    let j : Fin (n + 1) := Fin.last n
    S.sourceJordan.fundamentalIdeal j <
        S.sourceJordan.fourNormOverWeightIdealWith A
          (boundaryRightIndex j) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (S.sourceJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1))
        (S.targetJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1))
        (QuadraticSpace.scaledLine
          (A.value (boundaryRightIndex j))) := by
  dsimp only
  intro htrigger
  let j : Fin (n + 1) := Fin.last n
  let sourcePrefix := S.sourceJordan.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let sourceSuffix := S.sourceJordan.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  let targetPrefix := S.targetJordan.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice (j.val + 1)
  let targetSuffix := S.targetJordan.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  have suffixRepresentation :=
    S.residualLastSuffix_conditionIIWith f A htrigger
  let sourceSplit :=
    S.sourceJordan.toOrthogonalDecomposition
      |>.prefixSuffixLatticeIsometry (j.val + 1)
  let targetSplit :=
    S.targetJordan.toOrthogonalDecomposition
      |>.prefixSuffixLatticeIsometry (j.val + 1)
  let total : QuadraticSpace.Isometry
      (sourcePrefix.space.orthogonalSum sourceSuffix.space)
      (targetPrefix.space.orthogonalSum targetSuffix.space) :=
    sourceSplit.toQuadraticSpaceIsometry.trans <|
      f.toQuadraticSpaceIsometry.trans
        targetSplit.symm.toQuadraticSpaceIsometry
  letI : Module.Finite K sourcePrefix.carrier :=
    sourcePrefix.lattice.moduleFinite
  letI : Module.Finite K sourceSuffix.carrier :=
    sourceSuffix.lattice.moduleFinite
  letI : Module.Finite K targetPrefix.carrier :=
    targetPrefix.lattice.moduleFinite
  letI : Module.Finite K targetSuffix.carrier :=
    targetSuffix.lattice.moduleFinite
  exact QuadraticSpace.embedsInto_first_of_embedsInto_second
    total suffixRepresentation

theorem lastBoundary_conditionIIWith
    (f : Isometry
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice))
    (A : FundamentalNormGeneratorChoice J) :
    let j : Fin (n + 1) := Fin.last n
    J.fundamentalIdeal j <
        J.fourNormOverWeightIdealWith A (boundaryRightIndex j) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1))
        (H.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (j.val + 1))
        (QuadraticSpace.scaledLine
          (A.value (boundaryRightIndex j))) := by
  dsimp only
  intro htrigger
  let j : Fin (n + 1) := Fin.last n
  let AR := S.sourceFundamentalNormGeneratorChoice A
  have htriggerResidual : S.sourceJordan.fundamentalIdeal j <
      S.sourceJordan.fourNormOverWeightIdealWith AR
        (boundaryRightIndex j) := by
    rw [S.sourceJordan_fundamentalIdeal_eq,
      S.sourceJordan_fourNormOverWeightIdealWith_eq]
    exact htrigger
  have hresidual :=
    S.residualLastBoundary_conditionIIWith f AR htriggerResidual
  simpa only [sourceFundamentalNormGeneratorChoice_value] using
    S.prefix_embedsInto_of_rankFour j
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex j)))
      hresidual

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
