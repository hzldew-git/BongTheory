/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328ScaleOneDispatcher
import Bong.Lattice.Omeara9328StepEightConditions

/-!
# O'Meara 93:28, the exhaustive first-boundary dispatcher

For a saturated rank-four reduction system, Steps 4--7 either align the
first components immediately, or the numerical hypotheses of Step 8 hold.
This is the complete order-theoretic case split in the printed proof; in
particular, the Step-8 branch carries no additional local law.
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

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The three intrinsic inequalities needed to perform Step 8. -/
structure StepEightCase : Type where
  scaleGap_gt_one :
    1 < ordUnit K S.relativeSecondScale
  normGap_atLeastTwo :
    ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 1)
  firstNorm_below_twoScale :
    ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) <
      S.sourceJordan.fundamentalScaleOrder 0 +
        (ramificationIndex K : Int)

/-- The first boundary is either already reducible by Steps 4--7, or it is
exactly the strict-scale-gap case of Step 8. -/
abbrev FirstBoundaryOutcome
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :=
  Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A ⊕
    S.StepEightCase

/-- Exhaustive numerical dispatcher for O'Meara 93:28, Steps 4--8. -/
noncomputable def firstBoundaryOutcome
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A) :
    S.FirstBoundaryOutcome A := by
  let u₁ := ordUnit K S.firstNormGenerator
  let u₂ := ordUnit K (S.secondNormalizedNormGeneratorWith A)
  have hlower : u₁ ≤ u₂ :=
    S.firstNormGenerator_order_le_secondWith A
  have hfirstLe : u₁ ≤ (ramificationIndex K : Int) :=
    S.firstNormGenerator_order_le_ramificationIndex
  by_cases hequal : u₂ = u₁
  · have hcanonical : ordUnit K S.secondNormalizedNormGenerator =
        ordUnit K S.firstNormGenerator := by
      rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
      exact hequal
    exact Sum.inl <|
      S.equalOrderHeadAlignedReplacement A conditions hcanonical
  by_cases hfirst : u₁ = (ramificationIndex K : Int)
  · have hsecond : ordUnit K S.firstNormGenerator <
        ordUnit K S.secondNormalizedNormGenerator := by
      rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
      omega
    exact Sum.inl <|
      S.firstNormTwoHeadAlignedReplacement A conditions hfirst hsecond
  have hfirstLt : u₁ < (ramificationIndex K : Int) := by omega
  by_cases hadjacent : u₂ = u₁ + 1
  · exact Sum.inl <|
      S.adjacentOrderHeadAlignedReplacement A conditions
        hadjacent hfirstLt
  by_cases hscale : ordUnit K S.relativeSecondScale = 1
  · have hupper : u₂ ≤ u₁ + 2 :=
      S.secondWith_order_le_first_add_two A hscale
    have hgapTwo : u₂ = u₁ + 2 := by omega
    exact Sum.inl <|
      S.gapTwoHeadAlignedReplacement A conditions hgapTwo hscale
  · apply Sum.inr
    constructor
    · have hpositive : 0 < ordUnit K S.relativeSecondScale := by
        have hstrict := S.sourceJordan.scaleOrder_strict
          (i := (0 : Fin (n + 2))) (j := (1 : Fin (n + 2))) (by simp)
        have hstrict' :
            S.sourceJordan.fundamentalScaleOrder 0 <
              S.sourceJordan.fundamentalScaleOrder 1 := by
          simpa [fundamentalScaleOrder] using hstrict
        have hrelative := S.relativeSecondScale_order
        omega
      omega
    · have hgap := S.normalizedNormOrderGap_eq_fundamentalGap
      have hchoice := S.secondNormalizedNormGeneratorWith_order_eq A
      omega
    · have hfirstOrder := S.firstNormGenerator_order
      omega

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
