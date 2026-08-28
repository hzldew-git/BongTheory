/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightCommonBundle
import Bong.Lattice.Omeara9328HeadAlignedReduction

/-!
# Rank-four reduction of the closed Step-8 common bundle
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

/-- Simultaneous rank-four reduction of the packaged common pair. -/
noncomputable def bundledReductionSystem (E : S.StepEightCase) :
    Omeara9328RankFourReductionSystem
      (E.commonBundle S).sourceJordan (E.commonBundle S).targetJordan :=
  ⟨(E.commonBundle S).sourceSaturated,
    (E.commonBundle S).targetSaturated,
    (E.commonBundle S).fundamentalType,
    (E.commonBundle S).componentRank_atLeastTwo⟩

/-- Coherent generators on the final rank-four source. -/
noncomputable def bundledReducedChoice
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (E : S.StepEightCase) :=
  (E.bundledReductionSystem S).sourceFundamentalNormGeneratorChoice
    ((E.commonBundle S).choice A)

/-- The three 93:28 conditions on the final rank-four pair. -/
theorem bundledReducedConditions
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :
    (E.bundledReductionSystem S).sourceJordan.Omeara9328ConditionsWith
      (E.bundledReductionSystem S).targetJordan
        (E.bundledReducedChoice S A) :=
  (E.bundledReductionSystem S).omeara9328ConditionsWith_rankFour
    ((E.commonBundle S).choice A) ((E.commonBundle S).conditions A conditions)

/-- The final rank-four source keeps every raw Step-8 scale order. -/
theorem bundledSourceScaleOrder_eq_raw (E : S.StepEightCase)
    (i : Fin (n + 3)) :
    ordUnit K ((E.bundledReductionSystem S).sourceJordan.scaleGenerator i) =
      ordUnit K ((E.rawSource S).scaleGenerator i) :=
  calc
    ordUnit K ((E.bundledReductionSystem S).sourceJordan.scaleGenerator i) =
        ordUnit K ((E.commonBundle S).sourceJordan.scaleGenerator i) :=
      congrArg (ordUnit K)
        ((E.bundledReductionSystem S).sourceJordan_scaleGenerator i)
    _ = ordUnit K ((E.rawSource S).scaleGenerator i) :=
      (E.commonBundle S).scaleOrder_eq_raw i

/-- The inserted first scale gap is one in the final rank-four pair. -/
theorem bundledRelativeScale_order_eq_one (E : S.StepEightCase) :
    ordUnit K (E.bundledReductionSystem S).relativeSecondScale = 1 := by
  calc
    ordUnit K (E.bundledReductionSystem S).relativeSecondScale =
        (E.bundledReductionSystem S).sourceJordan.fundamentalScaleOrder 1 -
          (E.bundledReductionSystem S).sourceJordan.fundamentalScaleOrder 0 :=
      (E.bundledReductionSystem S).relativeSecondScale_order
    _ = (E.rawSource S).fundamentalScaleOrder 1 -
          (E.rawSource S).fundamentalScaleOrder 0 := by
      unfold fundamentalScaleOrder
      exact congrArg₂ (fun a b : Int ↦ a - b)
        (E.bundledSourceScaleOrder_eq_raw S 1)
        (E.bundledSourceScaleOrder_eq_raw S 0)
    _ = 1 := S.sourceJordan.stepEightJordan_firstScaleGap_eq_one
      (E.sourceScaleGap S)

/-- Steps 4--7 align the head of the final rank-four pair. -/
noncomputable def bundledReducedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith S.targetJordan A)
    (E : S.StepEightCase) :=
  (E.bundledReductionSystem S).scaleOneHeadAlignedReplacement
    (E.bundledReducedChoice S A)
    (E.bundledReducedConditions S A conditions)
    (E.bundledRelativeScale_order_eq_one S)

/-- Deleting the aligned head has the raw Step-8 tail scale spread. -/
theorem bundledTail_scaleSpread_eq_raw (E : S.StepEightCase) :
    (E.bundledReductionSystem S).sourceJordan.tail.scaleSpread =
      (E.rawSource S).tail.scaleSpread := by
  apply scaleSpread_eq_of_scaleGenerator_order_eq
    (E.rawSource S).tail (E.bundledReductionSystem S).sourceJordan.tail
  intro i
  simp only [tail_scaleGenerator]
  exact E.bundledSourceScaleOrder_eq_raw S i.succ

end Omeara9328RankFourReductionSystem.StepEightCase
end Lattice.JordanDecomposition

end Bong
