import Bong.Lattice.Omeara9328EqualOrderDeterminantOneModels
import Bong.Lattice.RankFourDeterminantHyperbolic
import Bong.Lattice.PairedHyperbolicRepresentation
import Bong.Lattice.OrthogonalSumRescale
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.OrthogonalDecompositionFirstPrefix
import Bong.Lattice.Omeara9328CoefficientShiftConditions

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- A representation remains a representation after multiplying both forms
by the same nonzero scalar. -/
def Representation.rescaleUnitBoth
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (f : Representation q r) (a : Kˣ) :
    Representation (q.rescaleUnit a) (r.rescaleUnit a) where
  toLinearMap := f.toLinearMap
  injective := f.injective
  map_bilin := by
    intro x y
    simp only [rescaleUnit_bilin_apply]
    rw [f.map_bilin]

/-- Rescaling a line multiplies its coefficient. -/
def scaledLineRescaleUnitIsometry (a b : Kˣ) :
    Isometry ((scaledLine b).rescaleUnit a) (scaledLine (a * b)) where
  toLinearEquiv := LinearEquiv.refl K K
  map_bilin := by
    intro x y
    simp only [rescaleUnit_bilin_apply, scaledLine_bilin_apply,
      LinearEquiv.refl_apply, Units.val_mul]
    ring

end QuadraticSpace

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

namespace Omeara9328RankFourReductionSystem.EqualNormOrderErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.EqualNormOrderErrorData z)

/-- The first coordinate of the exchanged plane represents its new first
coefficient, which is the coherently chosen second norm generator. -/
theorem newPlaneRepresentsSecondGenerator :
    D.exchangeSetup.newPlane.Represents
      (QuadraticSpace.scaledLine D.secondGenerator) := by
  refine ⟨{
    toLinearMap :=
      { toFun := fun x ↦ ![x, 0]
        map_add' := by
          intro x y
          funext i
          fin_cases i <;> simp
        map_smul' := by
          intro c x
          funext i
          fin_cases i <;> simp }
    injective := ?_
    map_bilin := ?_ }⟩
  · intro x y hxy
    have hzero := congrFun hxy 0
    simpa using hzero
  · intro x y
    unfold Omeara9319ExchangeSetup.newPlane
    rw [QuadraticSpace.omearaGeneralPlane_bilin_apply,
      D.exchangeSetup_newCoefficient]
    simp

end Omeara9328RankFourReductionSystem.EqualNormOrderErrorData

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- Condition 93:28(ii) at the first boundary, transported to the normalized
rank-four heads with the same explicit second generator. -/
theorem normalizedConditionIIRepresentation
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    (S.targetFirstNormalized.orthogonalSum
        (QuadraticSpace.scaledLine
          (S.secondNormalizedNormGeneratorWith A))).Represents
      S.sourceFirstNormalized := by
  let sourcePrefix :=
    S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1
  let targetPrefix :=
    S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1
  letI : Module.Finite K sourcePrefix.carrier := sourcePrefix.lattice.moduleFinite
  letI : Module.Finite K targetPrefix.carrier := targetPrefix.lattice.moduleFinite
  have hindex : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by
    apply Fin.ext
    simp [boundaryRightIndex]
  have hrawRaw := conditions.2.1 (0 : Fin (n + 1)) htrigger
  change
    ((S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        |>.orthogonalSum
          (QuadraticSpace.scaledLine
            (A.value (boundaryRightIndex (0 : Fin (n + 1)))))).Represents
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
    at hrawRaw
  have hraw :
      (targetPrefix.space.orthogonalSum
          (QuadraticSpace.scaledLine (A.value 1))).Represents
        sourcePrefix.space := by
    simpa only [hindex] using hrawRaw
  rcases hraw with ⟨f⟩
  let fScaled := f.rescaleUnitBoth S.firstScale⁻¹
  let distribute := QuadraticSpace.rescaleUnitOrthogonalSumIsometry
    targetPrefix.space (QuadraticSpace.scaledLine (A.value 1))
      S.firstScale⁻¹
  let sourcePrefixIso :=
    S.sourceJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry
  let targetPrefixIso :=
    S.targetJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry
  let sourceNormalize : QuadraticSpace.Isometry S.sourceFirstNormalized
      (sourcePrefix.space.rescaleUnit S.firstScale⁻¹) := by
    exact sourcePrefixIso.toQuadraticSpaceIsometry.rescaleUnitBoth
      S.firstScale⁻¹
  let targetNormalize : QuadraticSpace.Isometry
      (targetPrefix.space.rescaleUnit S.firstScale⁻¹)
      S.targetFirstNormalized := by
    exact (targetPrefixIso.toQuadraticSpaceIsometry.rescaleUnitBoth
      S.firstScale⁻¹).symm
  let lineNormalize : QuadraticSpace.Isometry
      ((QuadraticSpace.scaledLine (A.value 1)).rescaleUnit S.firstScale⁻¹)
      (QuadraticSpace.scaledLine
        (S.secondNormalizedNormGeneratorWith A)) := by
    exact QuadraticSpace.scaledLineRescaleUnitIsometry
      S.firstScale⁻¹ (A.value 1)
  let normalizeTarget := distribute.trans
    (targetNormalize.orthogonalSum lineNormalize)
  exact ⟨normalizeTarget.toRepresentation.trans
    (fScaled.trans sourceNormalize.toRepresentation)⟩

/-- In the triggered half of Step 4, the corrected determinant-one head
represents a hyperbolic plane. -/
theorem equalOrderNewHeadRepresentsHyperbolicOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    let D := S.equalOrderErrorData A conditions hgap
    D.newHead.Represents
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  let D := S.equalOrderErrorData A conditions hgap
  change D.newHead.Represents
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
  letI : Module.Finite K (S.sourceJordan.component 0).carrier :=
    (S.sourceJordan.component 0).lattice.moduleFinite
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  letI : Module.Finite K (D.headSplit.decomposition.component 1).carrier :=
    D.newHeadLattice.moduleFinite
  rcases S.normalizedConditionIIRepresentation A conditions htrigger with
    ⟨sourceInOldLine⟩
  rcases D.newPlaneRepresentsSecondGenerator with ⟨lineInNewPlane⟩
  let replaceLine :=
    (QuadraticSpace.Representation.refl S.targetFirstNormalized).orthogonalSum
      lineInNewPlane
  let sourceInOldNew := replaceLine.trans sourceInOldLine
  let swap : QuadraticSpace.Isometry
      (S.targetFirstNormalized.orthogonalSum D.exchangeSetup.newPlane)
      D.headAmbient :=
    (orthogonalProductSwap
      (q := S.targetFirstNormalized) (r := D.exchangeSetup.newPlane)
      (L := (S.targetJordan.component 0).lattice)
      (M := hyperbolicPlaneLattice (K := K))).toQuadraticSpaceIsometry
  let targetToSplit := swap.trans D.headSplit.displayedIsometry.toQuadraticSpaceIsometry
  have sourceInSplit :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        D.newHead).Represents S.sourceFirstNormalized :=
    ⟨targetToSplit.toRepresentation.trans sourceInOldNew⟩
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  let sourceToPair := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    pairToTower.symm
  have pairInSplit :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        D.newHead).Represents
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ))) :=
    sourceInSplit.trans ⟨sourceToPair.symm.toRepresentation⟩
  exact QuadraticSpace.orthogonalSumLeftCancelRepresents
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) D.newHead pairInSplit

/-- Consequently the corrected head is the standard two-plane hyperbolic
tower over the field, without an additional local-classification law. -/
theorem equalOrderNewHeadIsHyperbolicOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    let D := S.equalOrderErrorData A conditions hgap
    D.newHead.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let D := S.equalOrderErrorData A conditions hgap
  change D.newHead.IsIsometric
    (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)
  letI : Module.Finite K (D.headSplit.decomposition.component 1).carrier :=
    D.newHeadLattice.moduleFinite
  have hpair :=
    QuadraticSpace.rankFour_isIsometric_hyperbolicPair_of_determinantClass_eq_one
      D.newHead D.newHeadLattice D.headSplit_complement_finrank
      (S.equalOrder_newHead_determinantClass_eq_one A conditions hgap)
      (S.equalOrderNewHeadRepresentsHyperbolicOfConditionII
        A conditions hgap htrigger)
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  rcases hpair with ⟨f⟩
  exact ⟨f.trans pairToTower⟩

/-- In the condition-(ii) branch, the normalized source head and corrected
head are integrally isometric. -/
noncomputable def equalOrderSourceToNewHeadIsometryOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    let D := S.equalOrderErrorData A conditions hgap
    Isometry S.sourceFirstNormalized D.newHead
      (S.sourceJordan.component 0).lattice D.newHeadLattice := by
  let D := S.equalOrderErrorData A conditions hgap
  change Isometry S.sourceFirstNormalized D.newHead
    (S.sourceJordan.component 0).lattice D.newHeadLattice
  exact D.sourceToNewHeadIsometryOfHyperbolic
    (S.equalOrderNewHeadIsHyperbolicOfConditionII
      A conditions hgap htrigger)

/-- The normalized source head maps integrally to the actual first component
of the installed target replacement. -/
noncomputable def equalOrderSourceToNormalizedReplacementHeadIsometryOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    let R := S.equalOrderJordanReplacement A conditions hgap
    Isometry S.sourceFirstNormalized
      (S.equalOrderTargetFirstNormalized A conditions hgap)
      (S.sourceJordan.component 0).lattice
      (R.target.component 0).lattice := by
  let D := S.equalOrderErrorData A conditions hgap
  let R := S.equalOrderJordanReplacement A conditions hgap
  change Isometry S.sourceFirstNormalized
    (S.equalOrderTargetFirstNormalized A conditions hgap)
    (S.sourceJordan.component 0).lattice
    (R.target.component 0).lattice
  exact (S.equalOrderSourceToNewHeadIsometryOfConditionII
    A conditions hgap htrigger).trans
      (S.equalOrderNormalizedHeadIsometry A conditions hgap)

/-- Undo a normalization by `s⁻¹` after rescaling back by `s`. -/
noncomputable def undoInverseRescaleLatticeIsometry
    {X : Type v} [AddCommGroup X] [Module K X]
    (p : QuadraticSpace K X) (N : Lattice K X) (s : Kˣ) :
    Isometry ((p.rescaleUnit s⁻¹).rescaleUnit s) p N N := by
  let combine := rescaleUnitMulLatticeIsometry p N s⁻¹ s
  have hs : s * s⁻¹ = (1 : Kˣ) := by simp
  let finish : Isometry (p.rescaleUnit (s * s⁻¹)) p N N := by
    simpa only [hs] using Isometry.rescaleUnitOne p N
  exact combine.trans finish

/-- After restoring the first Jordan scale, the source head is integrally
isometric to the actual replacement head. -/
noncomputable def equalOrderSourceToReplacementHeadIsometryOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    let R := S.equalOrderJordanReplacement A conditions hgap
    Isometry (S.sourceJordan.component 0).space
      (R.target.component 0).space
      (S.sourceJordan.component 0).lattice
      (R.target.component 0).lattice := by
  let R := S.equalOrderJordanReplacement A conditions hgap
  let normalized :=
    S.equalOrderSourceToNormalizedReplacementHeadIsometryOfConditionII
      A conditions hgap htrigger
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  let undoTarget := undoInverseRescaleLatticeIsometry
    (R.target.component 0).space (R.target.component 0).lattice S.firstScale
  exact undoSource.symm.trans (scaled.trans undoTarget)

/-- Complete Step-4 replacement object in the condition-(ii) branch.  The
new target decomposition is on the original target lattice, retains all
three 93:28 conditions, and has its first component aligned with the fixed
source head. -/
noncomputable def equalOrderHeadAlignedReplacementOfConditionII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryRightIndex 0)) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let R := S.equalOrderJordanReplacement A conditions hgap
  let head := S.equalOrderSourceToReplacementHeadIsometryOfConditionII
    A conditions hgap htrigger
  let boundary := omeara9328BoundaryZeroConditionsWith_of_headIsometry
    S.sourceJordan R.target A head
  exact R.headAlignedReplacement S.residualFundamentalType A conditions
    boundary head

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
