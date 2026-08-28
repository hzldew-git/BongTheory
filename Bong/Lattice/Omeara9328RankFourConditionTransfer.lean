/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328RankFourPrefixes
import Bong.Lattice.OmearaFundamentalScaleNormAlgebra
import Bong.Lattice.PairedHyperbolicRepresentation
import Bong.QuadraticSpace.OrthogonalSumCancellation

/-!
# Transfer of O'Meara 93:28 conditions to the rank-four reduction

The common negatively adjoined source prefix is displayed in two ways:
as `(-J_(k)) ⊥ J_(k)` and as a common hyperbolic tower plus the source
rank-four residual.  The target has the analogous displays with `H_(k)`
and the target residual.  Cancelling the common determinant factor and the
common quadratic-space summand transfers all three conditions of 93:28.
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

/-- Reuse the source fundamental norm generators on the rank-four source
system.  Equality of fundamental norm groups proves that these are still
norm generators after the rank change. -/
noncomputable def sourceFundamentalNormGeneratorChoice
    (A : FundamentalNormGeneratorChoice J) :
    FundamentalNormGeneratorChoice S.sourceJordan where
  value := A.value
  spec := by
    intro i
    exact isNormGeneratorValue_of_normGroupSet_eq
      (A.spec i) (S.sourceJordan_fundamentalNormGroup i).symm
      (S.sourceJordan.exists_fundamentalNormGenerator i)

@[simp]
theorem sourceFundamentalNormGeneratorChoice_value
    (A : FundamentalNormGeneratorChoice J) (i : Fin (n + 2)) :
    (S.sourceFundamentalNormGeneratorChoice A).value i = A.value i :=
  rfl

theorem sourceJordan_fundamentalScaleOrder_eq (i : Fin (n + 2)) :
    S.sourceJordan.fundamentalScaleOrder i = J.fundamentalScaleOrder i := by
  unfold fundamentalScaleOrder
  rw [S.sourceJordan_scaleGenerator]

theorem sourceJordan_fundamentalIdeal_eq (i : Fin (n + 1)) :
    S.sourceJordan.fundamentalIdeal i = J.fundamentalIdeal i :=
  fundamentalIdeal_eq_of_scaleOrder_normGroup_eq
    S.sourceJordan_fundamentalScaleOrder_eq
    S.sourceJordan_fundamentalNormGroup i

theorem sourceJordan_fourNormOverWeightIdealWith_eq
    (A : FundamentalNormGeneratorChoice J) (i : Fin (n + 2)) :
    S.sourceJordan.fourNormOverWeightIdealWith
        (S.sourceFundamentalNormGeneratorChoice A) i =
      J.fourNormOverWeightIdealWith A i :=
  fourNormOverWeightIdealWith_eq_of_scaleOrder_normGroup_eq
    S.sourceJordan_fundamentalScaleOrder_eq
    S.sourceJordan_fundamentalNormGroup A
    (S.sourceFundamentalNormGeneratorChoice A) (fun _ ↦ rfl) i

/-- Determinant relation for the source residual prefix. -/
theorem sourcePrefixDeterminantRelation (i : Fin (n + 1)) :
    determinantClass
        ((J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space.rescaleUnit (-1 : Kˣ))
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice *
      determinantClass
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice =
    determinantClass
        (BONG.blockOrthogonalForm i.val
          (S.prefixCommonTowerCarrier (m := i.val) (by omega))
          (S.prefixCommonTowerForm (m := i.val) (by omega)))
        (BONG.blockProductLattice i.val
          (S.prefixCommonTowerCarrier (m := i.val) (by omega))
          (S.prefixCommonTowerLattice (m := i.val) (by omega))) *
      determinantClass
        (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice := by
  let hk : i.val + 1 ≤ n + 2 := by omega
  have hproduct := determinantClass_eq_of_isometry
    (S.sourceNegativeAdjunctionPrefixProductIsometry hk)
  have hgather := determinantClass_eq_of_isometry
    (S.sourcePrefixGatheredReduction hk)
  rw [determinantClass_orthogonalProduct] at hproduct hgather
  exact hproduct.symm.trans hgather

/-- Determinant relation for the target residual prefix, with the same
negative source prefix and the same common tower as in the source relation.
-/
theorem targetPrefixDeterminantRelation (i : Fin (n + 1)) :
    determinantClass
        ((J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space.rescaleUnit (-1 : Kˣ))
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice *
      determinantClass
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice =
    determinantClass
        (BONG.blockOrthogonalForm i.val
          (S.prefixCommonTowerCarrier (m := i.val) (by omega))
          (S.prefixCommonTowerForm (m := i.val) (by omega)))
        (BONG.blockProductLattice i.val
          (S.prefixCommonTowerCarrier (m := i.val) (by omega))
          (S.prefixCommonTowerLattice (m := i.val) (by omega))) *
      determinantClass
        (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).space
        (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (i.val + 1)).lattice := by
  let hk : i.val + 1 ≤ n + 2 := by omega
  have hproduct := determinantClass_eq_of_isometry
    (S.targetNegativeAdjunctionPrefixProductIsometry hk)
  have hgather := determinantClass_eq_of_isometry
    (S.targetPrefixGatheredReduction hk)
  rw [determinantClass_orthogonalProduct] at hproduct hgather
  exact hproduct.symm.trans hgather

/-- O'Meara 93:28(i) passes from the original saturated pair to the
rank-four residual pair. -/
theorem omeara9328ConditionI_rankFour
    (hI : J.Omeara9328ConditionI H) :
    S.sourceJordan.Omeara9328ConditionI S.targetJordan := by
  intro i
  rw [S.sourceJordan_fundamentalIdeal_eq]
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
  have hnegative : BONG.GoodBONG.UnitsCongruentModulo
      (dN * dH) (dN * dJ) (J.fundamentalIdeal i) :=
    (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
      dN dH dJ (J.fundamentalIdeal i)).2 (hI i)
  have htower : BONG.GoodBONG.UnitsCongruentModulo
      (dP * dT) (dP * dS) (J.fundamentalIdeal i) :=
    BONG.GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      (dN * dH) (dP * dT) (dN * dJ) (dP * dS)
      (J.fundamentalIdeal i) htarget hsource hnegative
  exact (BONG.GoodBONG.unitsCongruentModulo_mul_left_iff
    dP dT dS (J.fundamentalIdeal i)).1 htower

/-- Every representation between corresponding original prefixes descends
to the rank-four residual prefixes.  The proof adds the common negative
source prefix, changes both displayed decompositions, and cancels the
literal common hyperbolic tower. -/
theorem rankFourPrefix_embedsInto
    [FiniteDimensional K Z]
    (i : Fin (n + 1)) (s : QuadraticSpace K Z)
    (h : QuadraticSublattice.EmbedsIntoOrthogonalSum
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
      (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1)) s) :
    QuadraticSublattice.EmbedsIntoOrthogonalSum
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1))
      (S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (i.val + 1)) s := by
  let hk : i.val + 1 ≤ n + 2 := by omega
  let JP := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let HP := H.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let SP := S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let TP := S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)
  let N := JP.space.rescaleUnit (-1 : Kˣ)
  let P := BONG.blockOrthogonalForm i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerForm hk)
  let PL := BONG.blockProductLattice i.val
    (S.prefixCommonTowerCarrier hk) (S.prefixCommonTowerLattice hk)
  letI : Module.Finite K (∀ j, S.prefixCommonTowerCarrier hk j) :=
    PL.moduleFinite
  letI : Module.Finite K SP.carrier := SP.lattice.moduleFinite
  letI : Module.Finite K TP.carrier := TP.lattice.moduleFinite
  rcases h with ⟨f⟩
  let sourceToNegative : QuadraticSpace.Isometry
      (P.orthogonalSum SP.space) (N.orthogonalSum JP.space) :=
    ((S.sourcePrefixGatheredReduction hk).toQuadraticSpaceIsometry.symm).trans
      (S.sourceNegativeAdjunctionPrefixProductIsometry hk).toQuadraticSpaceIsometry
  let targetMiddle : QuadraticSpace.Isometry
      (N.orthogonalSum HP.space) (P.orthogonalSum TP.space) :=
    ((S.targetNegativeAdjunctionPrefixProductIsometry hk).toQuadraticSpaceIsometry.symm).trans
        (S.targetPrefixGatheredReduction hk).toQuadraticSpaceIsometry
  let targetFromNegative : QuadraticSpace.Isometry
      (N.orthogonalSum (HP.space.orthogonalSum s))
      (P.orthogonalSum (TP.space.orthogonalSum s)) :=
    (QuadraticSpace.orthogonalSumAssoc N HP.space s).symm.trans <|
      (targetMiddle.orthogonalSum
        (QuadraticSpace.Isometry.refl s)).trans <|
        QuadraticSpace.orthogonalSumAssoc P TP.space s
  let negativeRepresentation : QuadraticSpace.Representation
      (N.orthogonalSum JP.space)
      (N.orthogonalSum (HP.space.orthogonalSum s)) :=
    (QuadraticSpace.Representation.refl N).orthogonalSum f
  have total :
      (P.orthogonalSum (TP.space.orthogonalSum s)).Represents
        (P.orthogonalSum SP.space) :=
    ⟨targetFromNegative.toRepresentation.trans
      (negativeRepresentation.trans sourceToNegative.toRepresentation)⟩
  exact QuadraticSpace.orthogonalSumCancelRepresents
    P P SP.space (TP.space.orthogonalSum s)
    (QuadraticSpace.Isometry.refl P) total

/-- O'Meara 93:28(ii) passes to the rank-four residual systems while
retaining the same coherent scalar norm generators. -/
theorem omeara9328ConditionIIWith_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (hII : J.Omeara9328ConditionIIWith H A) :
    S.sourceJordan.Omeara9328ConditionIIWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A) := by
  intro i htrigger
  rw [S.sourceJordan_fundamentalIdeal_eq,
    S.sourceJordan_fourNormOverWeightIdealWith_eq] at htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value] using
    S.rankFourPrefix_embedsInto i
      (QuadraticSpace.scaledLine (A.value (boundaryRightIndex i)))
      (hII i htrigger)

/-- O'Meara 93:28(iii) passes to the rank-four residual systems. -/
theorem omeara9328ConditionIIIWith_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (hIII : J.Omeara9328ConditionIIIWith H A) :
    S.sourceJordan.Omeara9328ConditionIIIWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A) := by
  intro i htrigger
  rw [S.sourceJordan_fundamentalIdeal_eq,
    S.sourceJordan_fourNormOverWeightIdealWith_eq] at htrigger
  simpa only [sourceFundamentalNormGeneratorChoice_value] using
    S.rankFourPrefix_embedsInto i
      (QuadraticSpace.scaledLine (A.value (boundaryLeftIndex i)))
      (hIII i htrigger)

/-- The complete semantic hypothesis package of 93:28 survives the
simultaneous rank-four reduction. -/
theorem omeara9328ConditionsWith_rankFour
    (A : FundamentalNormGeneratorChoice J)
    (h : J.Omeara9328ConditionsWith H A) :
    S.sourceJordan.Omeara9328ConditionsWith S.targetJordan
      (S.sourceFundamentalNormGeneratorChoice A) :=
  ⟨S.omeara9328ConditionI_rankFour h.1,
    S.omeara9328ConditionIIWith_rankFour A h.2.1,
    S.omeara9328ConditionIIIWith_rankFour A h.2.2⟩

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
