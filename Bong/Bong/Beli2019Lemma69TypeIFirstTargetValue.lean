/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralPositiveSeeds
import Bong.Bong.Beli2019Lemma69TypeITerminalBoundary
import Bong.Bong.Beli2019Lemma69TypeIRightTargetValue

/-!
# Beli (2019), Lemma 6.9(ii): the first central target value

The odd value immediately after a positive type-I left switch only needs the
preceding left-branch value and Lemma 6.9(v) at the switch.  The complete
terminal/nonterminal form of Lemma 6.9(v) therefore removes the old
nonterminal restriction from this first central value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Conditions 2.1(i),(ii) determine the first odd target-beta value after a
positive type-I left switch, including the terminal type-I interval. -/
theorem beli2019Lemma69_ii_typeI_firstTargetValue_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftPos : 0 < C.leftSwitch)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.leftSwitch + 1) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hiLarge := i.lt_large
        omega⟩ := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hleftNext : C.leftSwitch + 1 < n + 2 := by omega
  have hleftValue := beli2019Lemma69_ii_typeI_leftSwitchValue
    a b D C hfirst hleftPos hleftNext hdefect
  have hiOdd : Odd i.val := by
    rcases C.left_even with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hiTwo : 1 < i.val := by
    rcases C.left_even with ⟨k, hk⟩
    omega
  have hiLeft : C.leftSwitch ≤ i.val - 1 := by omega
  have hiRight : i.val - 1 < C.rightSwitch := by omega
  have hweight := a.beli2019Lemma69_v_typeI_from_conditions
    b D C hfirst horder hdefect (i.val - 1) hiLeft hiRight
  have hprevious : a.representationAlpha b
      (⟨i.val - 1, by omega, by omega, by omega⟩ :
        RepresentationIndex (n + 2) (n + 2)) =
    (a.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ) := by
    simpa only [hi, show C.leftSwitch + 1 - 1 = C.leftSwitch by omega,
      show C.leftSwitch + 1 - 2 = C.leftSwitch - 1 by omega]
      using hleftValue
  have hvalue := lemma69_typeI_beta_eq_of_previous_normal
    a b D C hfirst hdefect i hiOdd hiTwo hiLeft hiRight
      (by simpa only using hweight) hprevious
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact hvalue

/-- Conditions 2.1(i),(ii) determine the first odd target-beta value after
the left switch, including coincident and terminal switches. -/
theorem beli2019Lemma69_ii_typeI_firstTargetValue_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hleftPos : 0 < C.leftSwitch)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.leftSwitch + 1) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hiLarge := i.lt_large
        omega⟩ := by
  by_cases hstrict : C.leftSwitch < C.rightSwitch
  · exact a.beli2019Lemma69_ii_typeI_firstTargetValue_from_conditions
      b D C hfirst hleftPos hstrict horder hdefect i hi
  · have hcoincident : C.leftSwitch = C.rightSwitch := by
      have hle := C.left_le_anchor.trans C.anchor_le_right
      omega
    have hiOdd : Odd i.val := by
      rcases C.left_even with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
    · have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
        a b D C hfirst hrightLast
      have hiRightEq : i.val = C.rightSwitch + 1 := by omega
      have hiRight : C.rightSwitch < i.val := by
        rw [hiRightEq]
        omega
      have hiLast : i.val < D.profile.last := by
        rw [hiRightEq]
        omega
      exact a.beli2019Lemma69_ii_typeI_targetRightValue
        b D C hfirst hrightLast hdefect i hiRight hiLast hiOdd
    · apply a.beli2019Lemma63_sameRank_right_value b hdefect i
      intro k hik hkn
      exact D.profile.lastDifference.after k (by omega) hkn

end BONG.GoodBONG

end Bong
