/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoIndexPrefixes
import Bong.Bong.Beli2019Lemma79RightTailCentralCoefficient
import Bong.Bong.Beli2019CappedDominationOrderBound
import Bong.Bong.Beli2019Lemma79EvenTargetIntegralSplit

/-!
# Beli (2019), Lemma 7.9(ii), case 8: even domination split

Assume the comparison self-prefix of even length `i` is the central
gap-two defect.  Capped domination selects an earlier odd paper index
(an even zero-based pair start).  If its order is at least the source
order at the gap-two boundary, the primary representation candidate is
already at most `beta_i`.  Otherwise we retain the precise low-order
witness needed by the remaining arithmetic.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The domination witness at an even current index either proves the final
beta bound immediately or has order strictly below the source boundary.
The latter branch retains both capped-defect inequalities used to analyze
strictness and equality later in the paper. -/
theorem caseEight_gapTwo_even_beta_bound_or_exists_lowWitness
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hcomparison :
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) ∨
      ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val ∧
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
  rcases c.exists_even_capped_domination_order_bound i.val i.pos
      i.lt_large.le hiEven with ⟨j, hjEven, hjlt, hjPair, hjCoefficient⟩
  have hprevious :
      (⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have hpreviousAlpha :
      (⟨i.val - 2, by
        have hiPos := i.pos
        have hiLarge := i.lt_large
        omega⟩ : Fin (n + 1)) = evenTargetPreviousAlphaIndex i := by
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
        ((b.order ⟨i.val, i.lt_large⟩ -
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
