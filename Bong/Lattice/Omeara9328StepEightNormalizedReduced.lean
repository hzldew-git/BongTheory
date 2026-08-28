/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightNormalizedCommon

/-!
# Final rank-four data in O'Meara 93:28, Step 8
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition
namespace Omeara9328RankFourReductionSystem.StepEightCase

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}
  (S : Omeara9328RankFourReductionSystem J H)

/-- Simultaneous rank-four reduction of the common-adjunction pair. -/
noncomputable def commonReductionSystem (E : S.StepEightCase) :
    Omeara9328RankFourReductionSystem (E.commonSource S) (E.commonTarget S) :=
  ⟨E.commonSource_isSaturated S, E.commonTarget_isSaturated S,
    E.commonFundamentalType S, E.commonSource_componentRank_atLeastTwo S⟩

/-- Coherent generators on the final rank-four source. -/
noncomputable def reducedChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (E : S.StepEightCase) :=
  (E.commonReductionSystem S).sourceFundamentalNormGeneratorChoice
    (E.commonChoice S A)

/-- Conditions on the final rank-four pair. -/
theorem reducedConditions
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :
    (E.commonReductionSystem S).sourceJordan.Omeara9328ConditionsWith
      (E.commonReductionSystem S).targetJordan (E.reducedChoice S A) :=
  (E.commonReductionSystem S).omeara9328ConditionsWith_rankFour
    (E.commonChoice S A) (E.commonConditions S A conditions)

/-- The first relative scale of the final rank-four pair is one. -/
theorem reducedRelativeScale_order_eq_one (E : S.StepEightCase) :
    ordUnit K (E.commonReductionSystem S).relativeSecondScale = 1 :=
  (E.commonReductionSystem S).relativeScaleOrder_eq_one_of_commonStable
    (E.saturatedToStable S) (E.saturatedSource_isSaturated S)
      (S.sourceJordan.stepEightJordan_firstScaleGap_eq_one (E.sourceScaleGap S))

/-- Steps 4--7 align the head after the Step-8 first-gap reduction. -/
noncomputable def reducedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :=
  (E.commonReductionSystem S).scaleOneHeadAlignedReplacement
    (E.reducedChoice S A) (E.reducedConditions S A conditions)
      (E.reducedRelativeScale_order_eq_one S)

/-- Ambient isometry of the final rank-four residual pair. -/
noncomputable def reducedAmbient
    (ambient : q.IsIsometric r) (E : S.StepEightCase) :
    (BONG.blockOrthogonalForm (n + 2)
      (E.commonReductionSystem S).sourceCarrier
      (E.commonReductionSystem S).sourceForm).IsIsometric
      (BONG.blockOrthogonalForm (n + 2)
        (E.commonReductionSystem S).targetCarrier
        (E.commonReductionSystem S).targetForm) :=
  ⟨(E.commonReductionSystem S).residualAmbientIsometry
    (E.commonAmbient S ambient)⟩

set_option maxHeartbeats 1000000 in
-- Matching the opaque common-reduction carrier to the generic scale lemma is expensive.
/-- The aligned tail has the raw Step-8 tail scale spread. -/
theorem reducedTail_scaleSpread_eq_raw (E : S.StepEightCase) :
    (E.commonReductionSystem S).sourceJordan.tail.scaleSpread =
      (E.rawSource S).tail.scaleSpread :=
  (E.commonReductionSystem S).tail_scaleSpread_eq_of_commonStable
    (E.saturatedToStable S) (E.saturatedSource_isSaturated S)

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
