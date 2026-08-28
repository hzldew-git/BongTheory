/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoCentralBounds

/-!
# Beli (2019), Lemma 7.9(ii), case 8: terminal weight comparison

At a gap-two endpoint the source half-gap is exactly one larger than the
target half-gap.  A strict target/source alpha inequality is therefore
separated by at least three halves: either the source alpha is its half-gap,
or both alpha values are odd rational integers.  This supplies the missing
one-half neighboring-coordinate estimate in the terminal form of Lemma
6.9(v).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At a gap-two endpoint, strictness between the two alpha values improves
to a separation by at least `3/2`. -/
theorem CaseEightStrictBetaTailConsequences.targetAlpha_add_threeHalves_le_source
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hcurrent : b.order first.castSucc = a.order first.castSucc + 2)
    (hnext : b.order first.succ = a.order first.succ)
    (hstrict : b.alphaValue first < a.alphaValue first) :
    b.alphaValue first + 3 / 2 ≤ a.alphaValue first := by
  have hhalfShift : a.halfGapValue first = b.halfGapValue first + 1 := by
    unfold halfGapValue orderGap
    rw [hcurrent, hnext]
    push_cast
    ring
  by_cases haHalf : a.alphaValue first = a.halfGapValue first
  · have hbHalf := H.alpha_lt_halfGap first le_rfl hfirstLast
    have haHalfIntegral := a.halfGapValue_isRationalHalfInteger first
    have hbIntegral := H.alpha_odd first le_rfl hfirstLast
    rcases haHalfIntegral with ⟨za, hza⟩
    rcases hbIntegral with ⟨zb, _, hzb⟩
    have hbHalfEq : b.halfGapValue first =
        a.halfGapValue first - 1 := by
      linarith [hhalfShift]
    have hrat : ((2 * zb : Int) : Rat) < (za : Rat) - 2 := by
      rw [hzb, hbHalfEq, hza] at hbHalf
      push_cast at hbHalf ⊢
      linarith
    have hint : 2 * zb < za - 2 := by
      exact_mod_cast hrat
    have hstep : 2 * zb + 3 ≤ za := by omega
    have hstepQ : ((2 * zb + 3 : Int) : Rat) ≤ (za : Rat) := by
      exact_mod_cast hstep
    rw [haHalf, hza, hzb]
    push_cast at hstepQ ⊢
    linarith
  · have haOdd := a.beli2009Lemma27_iv first haHalf
    have hbOdd := H.alpha_odd first le_rfl hfirstLast
    rcases haOdd with ⟨za, hzaOdd, hza⟩
    rcases hbOdd with ⟨zb, hzbOdd, hzb⟩
    have hstrictInt : zb < za := by
      rw [hza, hzb] at hstrict
      exact_mod_cast hstrict
    have hstep : zb + 2 ≤ za := by
      rcases hzaOdd with ⟨ka, hka⟩
      rcases hzbOdd with ⟨kb, hkb⟩
      omega
    have hstepQ : (zb : Rat) + 2 ≤ (za : Rat) := by
      exact_mod_cast hstep
    rw [hza, hzb]
    linarith

/-- The strengthened alpha separation gives the following-coordinate
one-half estimate used to round the terminal right boundary. -/
theorem CaseEightStrictBetaTailConsequences.endpointEvenWeight_le_add_half
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last)
    (hcurrent : b.order first.castSucc = a.order first.castSucc + 2)
    (hnext : b.order first.succ = a.order first.succ)
    (hstrict : b.alphaValue first < a.alphaValue first) :
    b.weightSequence.entryOrZero (2 * first.val) ≤
      a.weightSequence.entryOrZero (2 * first.val) + 1 / 2 := by
  have halpha := H.targetAlpha_add_threeHalves_le_source
    hfirstLast hcurrent hnext hstrict
  have hcoordBound : 2 * first.val < 2 * (n + 1) := by omega
  rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound,
    BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound]
  change b.weightSequence.value ⟨2 * first.val, hcoordBound⟩ ≤
    a.weightSequence.value ⟨2 * first.val, hcoordBound⟩ + 1 / 2
  have hbValue := b.weightSequence_even first
  have haValue := a.weightSequence_even first
  rw [show (⟨2 * first.val, hcoordBound⟩ : Fin (2 * (n + 1))) =
      ⟨2 * first.val, by omega⟩ by apply Fin.ext; rfl,
    hbValue, haValue]
  have hcurrentQ : (b.order first.castSucc : Rat) =
      (a.order first.castSucc : Rat) + 2 := by
    exact_mod_cast hcurrent
  rw [hcurrentQ]
  linarith

/-- Case 8 supplies the terminal neighboring-coordinate estimate directly
from the last-difference suffix and the strict alpha inequality at its end. -/
theorem beli2019Lemma79_typeI_caseEight_terminalRightNeighbor
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast) :
    b.weightSequence.entryOrZero (2 * D.profile.last) ≤
      a.weightSequence.entryOrZero (2 * D.profile.last) + 1 / 2 := by
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  have hcurrent : b.order first.castSucc = a.order first.castSucc + 2 := by
    have hfirstCast : first.castSucc =
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hfirstCast, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hgapTwo
  have horders (j : Fin (n + 1)) (hfirst : first ≤ j)
      (hjTail : j ≤ tailLast) : a.order j.succ = b.order j.succ := by
    have hjLast : D.profile.last ≤ j.val := by
      change first.val ≤ j.val at hfirst
      simpa only [first] using hfirst
    have hentry := D.profile.lastDifference.after
      (j.val + 1) (by omega) (by omega)
    rw [a.orderSequence_entryOrZero_eq_order ⟨j.val + 1, by omega⟩,
      b.orderSequence_entryOrZero_eq_order ⟨j.val + 1, by omega⟩]
      at hentry
    have hidx : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) = j.succ := by
      apply Fin.ext
      rfl
    simpa only [hidx] using hentry
  have hnext : b.order first.succ = a.order first.succ :=
    (horders first le_rfl hfirstTail).symm
  have hstrict : b.alphaValue first < a.alphaValue first :=
    H.targetAlpha_lt_sourceAlpha horders hstrictTail
      first le_rfl hfirstTail
  simpa only [first] using
    H.endpointEvenWeight_le_add_half hfirstTail hcurrent hnext hstrict

end BONG.GoodBONG

end Bong
