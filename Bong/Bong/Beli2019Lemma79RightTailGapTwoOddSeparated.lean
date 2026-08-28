/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddSeparatedDefect

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the separated odd branch

When the comparison self-prefix does not have the central defect, sharp
multiplication bounds the mixed primary defect by that central value.
Together with `T_i >= S_u`, the primary representation candidate is at
most `beta_i`.  This completes lines 5953--5957 of the v2 paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The unequal comparison-prefix alternative at an odd gap-two index
satisfies the desired beta estimate. -/
theorem caseEight_gapTwo_odd_beta_bound_of_comparisonPrefix_ne
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (hcomparisonOrder : b.order first.castSucc <=
      c.order (evenTargetPreviousIndex i))
    (htarget : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat))
    (hcomparisonNe : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) ≠
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let centralQ : Rat :=
    ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first
  have hmixed := caseEight_gapTwo_odd_mixedDefect_le_of_comparisonPrefix_ne
    b c i hiOdd (centralQ : WithTop Rat) (by
      simpa only [centralQ] using htarget) (by
        simpa only [centralQ] using hcomparisonNe)
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have harith :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) + centralQ <=
        b.alphaValue (caseEightLastAlphaIndex i) := by
    have hcomparisonQ : (b.order first.castSucc : Rat) <=
        (c.order (evenTargetPreviousIndex i) : Rat) := by
      exact_mod_cast hcomparisonOrder
    simp only [centralQ]
    push_cast at hcentral hcomparisonQ ⊢
    linarith
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i <= b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ <=
        ((((b.order (Fin.mk i.val i.lt_large) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) :
              WithTop Rat) + (centralQ : WithTop Rat)) := by
      unfold representationPrimaryDefect
      simpa only [evenTargetPreviousIndex] using
        add_le_add_right hmixed
          ((((b.order (Fin.mk i.val i.lt_large) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) :
              WithTop Rat))
    _ <= (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
      exact_mod_cast harith

end BONG.GoodBONG

end Bong
