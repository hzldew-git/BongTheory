/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328EqualOrderTwistAbsorption
import Bong.Lattice.Omeara9328FirstNormTwoHyperbolic
import Bong.Lattice.Omeara9328GapTwoNontrigger

/-!
# O'Meara 93:28, Steps 4--7: the scale-one dispatcher

When the first two normalized Jordan scales differ by one, O'Meara 93:25
forces the normalized norm-order gap to be `0`, `1`, or `2`.  The first
normalized norm order is at most the ramification index.  These elementary
bounds make Steps 4--7 exhaustive and select the already formalized head
replacement without an additional case law.
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

/-- The norm order of a normalized unimodular component is bounded by the
order of `2`. -/
theorem firstNormGenerator_order_le_ramificationIndex :
    ordUnit K S.firstNormGenerator ≤ (ramificationIndex K : Int) := by
  have hnorm := normGeneratorOrder_le_weightIdealOrder
    S.firstNormGenerator S.firstNormGenerator_source
  have hweight : weightIdealOrder S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice ≤
        (ramificationIndex K : Int) := by
    have h := twoScaleIdeal_le_weightIdeal S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.sourceFirstNormalized_unimodular
        (by rw [S.sourceFirstNormalized_finrank]; omega),
      weightIdeal_eq_powerIdeal] at h
    let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
    have htwo : principalIdeal (K := K) (2 : K) =
        powerIdeal (K := K) (ramificationIndex K : Int) := by
      calc
        principalIdeal (K := K) (2 : K) =
            principalIdeal (K := K) (two : K) := rfl
        _ = powerIdeal (K := K) (ordUnit K two) :=
          principalIdeal_eq_powerIdeal two
        _ = powerIdeal (K := K) (ramificationIndex K : Int) := by
          congr 1
          apply WithTop.coe_injective
          rw [coe_ordUnit]
          exact (ramificationIndex_spec K).symm
    rw [htwo, powerIdeal_le_iff] at h
    exact h
  exact hnorm.trans hweight

/-- O'Meara 93:25 makes the normalized second norm order no smaller than
the first. -/
theorem firstNormGenerator_order_le_secondWith
    (A : FundamentalNormGeneratorChoice S.sourceJordan) :
    ordUnit K S.firstNormGenerator ≤
      ordUnit K (S.secondNormalizedNormGeneratorWith A) := by
  have hmono := S.sourceJordan.fundamentalNormGenerator_order_mono
    (i := (0 : Fin (n + 2))) (j := (1 : Fin (n + 2))) (by simp)
  have hgap := S.normalizedNormOrderGap_eq_fundamentalGap
  have hchoice := S.secondNormalizedNormGeneratorWith_order_eq A
  omega

/-- If the adjacent scale gap is one, the dual inequality of 93:25 bounds
the normalized norm-order gap by two. -/
theorem secondWith_order_le_first_add_two
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    ordUnit K (S.secondNormalizedNormGeneratorWith A) ≤
      ordUnit K S.firstNormGenerator + 2 := by
  have hdual :=
    S.sourceJordan.fundamentalNormGenerator_order_sub_two_scale_anti
      (i := (0 : Fin (n + 2))) (j := (1 : Fin (n + 2))) (by simp)
  have hrelative := S.relativeSecondScale_order
  have hgap := S.normalizedNormOrderGap_eq_fundamentalGap
  have hchoice := S.secondNormalizedNormGeneratorWith_order_eq A
  omega

/-- Complete dispatcher for O'Meara 93:28, Steps 4--7. -/
noncomputable def scaleOneHeadAlignedReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let u₁ := ordUnit K S.firstNormGenerator
  let u₂ := ordUnit K (S.secondNormalizedNormGeneratorWith A)
  have hlower : u₁ ≤ u₂ :=
    S.firstNormGenerator_order_le_secondWith A
  have hupper : u₂ ≤ u₁ + 2 :=
    S.secondWith_order_le_first_add_two A hscale
  have hfirstLe : u₁ ≤ (ramificationIndex K : Int) :=
    S.firstNormGenerator_order_le_ramificationIndex
  by_cases hequal : u₂ = u₁
  · have hcanonical : ordUnit K S.secondNormalizedNormGenerator =
        ordUnit K S.firstNormGenerator := by
      rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
      exact hequal
    exact S.equalOrderHeadAlignedReplacement A conditions hcanonical
  by_cases hfirst : u₁ = (ramificationIndex K : Int)
  · have hsecond : ordUnit K S.firstNormGenerator <
        ordUnit K S.secondNormalizedNormGenerator := by
      rw [← S.secondNormalizedNormGeneratorWith_order_eq A]
      omega
    exact S.firstNormTwoHeadAlignedReplacement A conditions hfirst hsecond
  have hfirstLt : u₁ < (ramificationIndex K : Int) := by omega
  by_cases hadjacent : u₂ = u₁ + 1
  · exact S.adjacentOrderHeadAlignedReplacement A conditions
      hadjacent hfirstLt
  · have hgapTwo : u₂ = u₁ + 2 := by omega
    exact S.gapTwoHeadAlignedReplacement A conditions hgapTwo hscale

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
