/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma73
import Bong.Bong.Beli2019Lemma79RightTailStrict

/-!
# Beli (2019), Lemma 7.9(ii), case 8: beta-tail propagation

In the strict branch the right endpoints of the target alpha sequence agree
at the last changed coordinate and at the current coordinate.  Antitonicity
makes the whole intervening interval constant.  Lemma 7.3(ii) then gives the
order and alpha parity statements, together with the `2e` bounds, used in the
remaining domination argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- All consequences of a constant target right endpoint on the case-8
tail. -/
structure CaseEightBetaTailConsequences
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1)) : Prop where
  rightEndpoint_eq (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.alphaRightEndpoint j = b.alphaRightEndpoint first
  value_eq (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.alphaValue j =
      ((b.order j.succ - b.order first.succ : Int) : Rat) +
        b.alphaValue first
  order_modEq (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    Int.ModEq 2 (b.order j.succ) (b.order first.succ)
  alpha_modEq (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    RationalModEqTwo (b.alphaValue j) (b.alphaValue first)
  alpha_le (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.alphaValue j <= 2 * (ramificationIndex K : Rat)
  gap_le (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.orderGap j <= 2 * (ramificationIndex K : Int)

/-- The shifted beta identity in the paper is exactly equality of target
right endpoints. -/
theorem caseEight_rightEndpoint_eq_of_beta_shift
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1))
    (hshift : b.alphaValue last =
      ((b.order last.succ - b.order first.succ : Int) : Rat) +
        b.alphaValue first) :
    b.alphaRightEndpoint first = b.alphaRightEndpoint last := by
  unfold alphaRightEndpoint
  push_cast at hshift ⊢
  linarith

/-- Equality at the two ends of the target right-endpoint sequence forces
the complete case-8 beta tail. -/
theorem caseEight_betaTailConsequences_of_rightEndpoint_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1))
    (hfirstLast : first < last)
    (hendpoint : b.alphaRightEndpoint first =
      b.alphaRightEndpoint last) :
    CaseEightBetaTailConsequences b first last := by
  have hlemma73 := b.beli2019Lemma73_ii first last hfirstLast hendpoint
  have hright (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
      b.alphaRightEndpoint j = b.alphaRightEndpoint first := by
    apply le_antisymm
    · exact b.alphaRightEndpoint_antitone hfirst
    · rw [hendpoint]
      exact b.alphaRightEndpoint_antitone hlast
  refine
    { rightEndpoint_eq := hright
      value_eq := ?_
      order_modEq := hlemma73.order_modEq
      alpha_modEq := hlemma73.alpha_modEq
      alpha_le := hlemma73.alpha_le
      gap_le := hlemma73.gap_le }
  intro j hfirst hlast
  have heq := hright j hfirst hlast
  unfold alphaRightEndpoint at heq
  push_cast at heq ⊢
  linarith

/-- Direct form starting from the shifted beta identity displayed in case
8 of the paper. -/
theorem caseEight_betaTailConsequences_of_beta_shift
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1))
    (hfirstLast : first < last)
    (hshift : b.alphaValue last =
      ((b.order last.succ - b.order first.succ : Int) : Rat) +
        b.alphaValue first) :
    CaseEightBetaTailConsequences b first last :=
  caseEight_betaTailConsequences_of_rightEndpoint_eq b first last
    hfirstLast (caseEight_rightEndpoint_eq_of_beta_shift
      b first last hshift)

/-- Strict target/source alpha inequality at the end of an unchanged-order
tail propagates to every preceding boundary on that tail. -/
theorem CaseEightBetaTailConsequences.targetAlpha_lt_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {first last : Fin (n + 1)}
    (H : CaseEightBetaTailConsequences b first last)
    (horders : forall j, first <= j -> j <= last ->
      a.order j.succ = b.order j.succ)
    (hstrict : b.alphaValue last < a.alphaValue last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last) :
    b.alphaValue j < a.alphaValue j := by
  have hbEndpoint : b.alphaRightEndpoint j =
      b.alphaRightEndpoint last :=
    (H.rightEndpoint_eq j hfirst hlast).trans
      (H.rightEndpoint_eq last (hfirst.trans hlast) le_rfl).symm
  have haEndpoint := a.alphaRightEndpoint_antitone hlast
  have hjOrder := horders j hfirst hlast
  have hlastOrder := horders last (hfirst.trans hlast) le_rfl
  unfold alphaRightEndpoint at hbEndpoint haEndpoint
  rw [hjOrder, hlastOrder] at haEndpoint
  push_cast at hbEndpoint haEndpoint
  linarith

end BONG.GoodBONG

end Bong
