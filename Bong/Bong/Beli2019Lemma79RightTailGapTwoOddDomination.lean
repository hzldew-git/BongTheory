/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddSeparated
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd domination split

If the odd-index comparison prefix has the central defect, extended capped
domination is applied to its even prefix of length `i - 1`.  A witness at
or above the target boundary proves the beta estimate immediately; the
remaining alternative is the low witness used in lines 5959--5975.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The odd comparison-prefix domination either closes the beta bound or
returns the precise low witness and both capped inequalities. -/
theorem caseEight_gapTwo_odd_beta_bound_or_exists_lowWitness
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) ∨
      ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val - 1 ∧
        c.order j.castSucc < b.order first.castSucc ∧
        c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat) ∧
        ((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
              WithTop Rat) <=
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat) := by
  have hlengthEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    omega
  have hlengthPos : 0 < i.val - 1 := by
    by_contra hnot
    have hzero : i.val - 1 = 0 := Nat.eq_zero_of_not_pos hnot
    have htop : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) = ⊤ := by
      rw [hzero]
      norm_num
      exact c.truncatedPrefixDefect_self_one_zero_eq_top
    rw [htop] at hcomparison
    exact WithTop.top_ne_coe hcomparison
  have hiTwo : 2 <= i.val := by omega
  have hnextBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  rcases c.exists_even_capped_domination_order_bound_through_next
      (i.val - 1) hlengthPos hnextBound hlengthEven with
    ⟨j, hjEven, hjlt, hjPair, hjCoefficient⟩
  have hprevious :
      (Fin.mk (i.val - 1) hnextBound : Fin (n + 2)) =
        evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have hpreviousAlpha :
      (Fin.mk (i.val - 1 - 1) (by omega) : Fin (n + 1)) =
        evenTargetPreviousAlphaIndex i := by
    apply Fin.ext
    rfl
  rw [hcomparison] at hjPair hjCoefficient
  rw [hprevious, hpreviousAlpha] at hjCoefficient
  by_cases hsource : b.order first.castSucc <= c.order j.castSucc
  · left
    apply WithTop.coe_le_coe.mpr
    have hprimaryTop :=
      lemma79_even_representationAlphaValue_le_primaryCoefficient
        b c i hiTwo
    have hprimary : b.representationAlphaValue c i <=
        ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) := by
      exact_mod_cast hprimaryTop
    have hjCoefficientQ :
        ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
            Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) <=
          ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first := by
      exact_mod_cast hjCoefficient
    have hcentral := H.centralCoefficient_eq
      (caseEightLastAlphaIndex i) hfirstLast le_rfl
    rw [caseEightLastAlphaIndex_succ i] at hcentral
    have hsourceQ : (b.order first.castSucc : Rat) <=
        (c.order j.castSucc : Rat) := by
      exact_mod_cast hsource
    push_cast at hprimary hjCoefficientQ hsourceQ hcentral ⊢
    linarith
  · right
    exact ⟨j, hjEven, hjlt, lt_of_not_ge hsource, hjPair, hjCoefficient⟩

end BONG.GoodBONG

end Bong
