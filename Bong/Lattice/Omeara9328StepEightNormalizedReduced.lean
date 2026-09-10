/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightBundledReduced

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

/-- Compatibility name for the canonical bundled rank-four reduction. -/
noncomputable abbrev commonReductionSystem (E : S.StepEightCase) :=
  E.bundledReductionSystem S

/-- Coherent generators on the final rank-four source. -/
noncomputable abbrev reducedChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (E : S.StepEightCase) :=
  E.bundledReducedChoice S A

/-- Conditions on the final rank-four pair. -/
theorem reducedConditions
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :
    (E.commonReductionSystem S).sourceJordan.Omeara9328ConditionsWith
      (E.commonReductionSystem S).targetJordan (E.reducedChoice S A) :=
  E.bundledReducedConditions S A conditions

/-- The first relative scale of the final rank-four pair is one. -/
theorem reducedRelativeScale_order_eq_one (E : S.StepEightCase) :
    ordUnit K (E.commonReductionSystem S).relativeSecondScale = 1 :=
  E.bundledRelativeScale_order_eq_one S

/-- Steps 4--7 align the head after the Step-8 first-gap reduction. -/
noncomputable abbrev reducedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :=
  E.bundledReducedReplacement S A conditions

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
    ((E.commonBundle S).ambientOf ambient)⟩

/-- The aligned tail has the raw Step-8 tail scale spread. -/
theorem reducedTail_scaleSpread_eq_raw (E : S.StepEightCase) :
    (E.commonReductionSystem S).sourceJordan.tail.scaleSpread =
      (E.rawSource S).tail.scaleSpread :=
  E.bundledTail_scaleSpread_eq_raw S

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
