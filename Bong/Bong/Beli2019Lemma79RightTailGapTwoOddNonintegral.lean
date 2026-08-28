/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddDomination
import Bong.Bong.Beli2019Lemma79RightTailGapTwoNonintegralHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd nonintegral branch

A nonintegral `gamma_(i-1)` is strictly above `2e`.  The strict domination
coefficient then puts the integral cross-gap at most `beta_i`; the
representation half-gap is half that cross-gap and is therefore strictly
below the positive `beta_i`.  This formalizes lines 5966--5970.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The strict low-witness branch with nonintegral `gamma_(i-1)` satisfies
the desired odd-index beta estimate through the half-gap candidate. -/
theorem caseEight_gapTwo_odd_beta_bound_of_strict_lowWitness_nonintegral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (j : Fin (n + 1))
    (hsource : b.order first.castSucc = c.order j.castSucc + 1)
    (hstrict :
      ((((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
            WithTop Rat) <
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat))
    (hnot : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have halphaLarge : 2 * (ramificationIndex K : Rat) <
      c.alphaValue p := by
    rcases c.beli2009Corollary28_iii p with hsmall | hlarge
    · exact False.elim (hnot (by simpa only [p] using hsmall.2.2))
    · exact hlarge.1
  have hstrictQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue p <
        ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first := by
    exact_mod_cast hstrict
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hsourceQ : (b.order first.castSucc : Rat) =
      (c.order j.castSucc : Rat) + 1 := by
    exact_mod_cast hsource
  have hcrossLt :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) : Int) : Rat) <
        b.alphaValue (caseEightLastAlphaIndex i) + 1 := by
    push_cast at hstrictQ hcentral hsourceQ halphaLarge ⊢
    linarith
  rcases H.alpha_odd (caseEightLastAlphaIndex i) hfirstLast le_rfl with
    ⟨w, hwOdd, hw⟩
  have hcrossLeInt :
      b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) <= w := by
    have hcast :
        ((b.order (Fin.mk i.val i.lt_large) -
            c.order (evenTargetPreviousIndex i) +
            2 * (ramificationIndex K : Int) : Int) : Rat) <
          ((w + 1 : Int) : Rat) := by
      rw [hw] at hcrossLt
      push_cast at hcrossLt ⊢
      linarith
    have hint : b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) < w + 1 := by
      exact_mod_cast hcast
    omega
  have hcrossLe :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) : Int) : Rat) <=
        b.alphaValue (caseEightLastAlphaIndex i) := by
    rw [hw]
    exact_mod_cast hcrossLeInt
  have hbetaPos := H.alpha_pos
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  have hhalf :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) / 2 +
          (ramificationIndex K : Rat) <=
        b.alphaValue (caseEightLastAlphaIndex i) := by
    push_cast at hcrossLe ⊢
    linarith
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i <= b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ <= (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
      unfold representationHalfGap
      exact_mod_cast hhalf

end BONG.GoodBONG

end Bong
