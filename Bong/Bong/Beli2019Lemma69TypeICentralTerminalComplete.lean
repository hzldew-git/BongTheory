/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralSeedsComplete
import Bong.Bong.Beli2019Lemma69TypeIFirstTargetValue

/-!
# Beli (2019), Lemma 6.9(ii): terminal-complete type-I central values

The complete form of Lemma 6.9(v) identifies the weight endpoints even when
the canonical right switch is the last unequal order.  It therefore supplies
both central seeds and the whole alternating central induction without the
old nonterminal hypothesis `rightSwitch < last`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- The second seed may itself be the final representation coordinate.
/-- Conditions 2.1(i),(ii) determine both central type-I seeds, including a
terminal canonical interval. -/
theorem lemma69_typeI_centralSeedData_from_conditions_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    Lemma69TypeICentralSeedData a b D C := by
  have hoddSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 1 →
        a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    by_cases hleftZero : C.leftSwitch = 0
    · have hjOne : j.val = 1 := by omega
      have hweight := a.beli2019Lemma69_v_typeI_from_conditions
        b D C hfirst horder hdefect 0 (by omega) (by omega)
      have hbeta := lemma69_typeI_beta_eq_one_of_leftSwitch_zero
        a b D C hfirst hleftZero hdefect j hjOne (by omega) (by
          simpa only using hweight)
      simpa only [hjOne] using hbeta
    · have hvalue := a.beli2019Lemma69_ii_typeI_firstTargetValue_complete
        b D C hfirst (Nat.pos_of_ne_zero hleftZero) horder hdefect j hj
      rw [← a.coe_representationAlphaValue b j, hvalue]
  have hevenSeed : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 2 →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hl := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro j hj
    have hjEven : Even j.val := by
      rcases C.left_even with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hjTwo : 1 < j.val := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    have hjLeft : C.leftSwitch ≤ j.val - 2 := by omega
    have hjRight : j.val - 1 < C.rightSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    have hjPos := j.pos
    have hjLarge := j.lt_large
    have hweight := a.beli2019Lemma69_v_typeI_from_conditions
      b D C hfirst horder hdefect (j.val - 2) (by omega) (by omega)
    let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
      ⟨j.val - 1, by omega, by omega, by omega⟩
    have hpreviousRaw := hoddSeed previousIdx (by
      simp only [previousIdx]
      omega)
    have hprevious : a.representationAlpha b
        (⟨j.val - 1, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) := by
      simpa only [previousIdx,
        show j.val - 1 - 1 = j.val - 2 by omega] using hpreviousRaw
    by_cases hinterior : 1 < j.val ∧ j.val + 1 < n + 2
    · apply lemma69_typeI_alpha_eq_of_previous_or_first
        a b D C hfirst hdefect j hjEven hjTwo hjLeft hjRight
          hinterior (by simpa only using hweight) hprevious
      intro hthree
      have hleftPos : 0 < C.leftSwitch := by omega
      have hleftNext : C.leftSwitch + 1 < n + 2 := by
        have hbound := j.lt_large
        omega
      have hleftValue := beli2019Lemma69_ii_typeI_leftSwitchValue
        a b D C hfirst hleftPos hleftNext hdefect
      simpa only [hj,
        show C.leftSwitch + 2 - 2 = C.leftSwitch by omega,
        show C.leftSwitch + 2 - 3 = C.leftSwitch - 1 by omega]
        using hleftValue
    · exact lemma69_typeI_alpha_eq_of_previous_terminal
        a b D C hfirst hdefect j hjEven hjTwo (by omega) hjRight
          hinterior (by simpa only using hweight) hprevious
  exact ⟨hoddSeed, hevenSeed⟩

set_option maxHeartbeats 5000000 in
-- The alternating induction transports dependent representation indices.
/-- Conditions 2.1(i),(ii) determine every central type-I value, including
the terminal right-switch case. -/
theorem lemma69_typeI_central_values_from_conditions_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    (Odd i.val → a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) ∧
    (Even i.val → a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) := by
  have hstrict : C.leftSwitch < C.rightSwitch :=
    hiLeft.trans_lt hiRight
  have S := lemma69_typeI_centralSeedData_from_conditions_complete
    a b D C hfirst hstrict horder hdefect
  have hweight : ∀ p : Fin (n + 1),
      C.leftSwitch ≤ p.val → p.val < C.rightSwitch →
        a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
    intro p hpLeft hpRight
    have h := a.beli2019Lemma69_v_typeI_from_conditions
      b D C hfirst horder hdefect p.val hpLeft hpRight
    simpa only using h
  exact lemma69_typeI_central_values_of_seeds
    a b D C hfirst hdefect hweight S.odd S.even i hiLeft hiRight

/-- Finite target-beta form of the terminal-complete central type-I
calculation. -/
theorem beli2019Lemma69_ii_typeI_targetValue_from_conditions_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ := by
  have hvalue :=
    (lemma69_typeI_central_values_from_conditions_complete
      a b D C hfirst horder hdefect i hiLeft hiRight).1 hodd
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact hvalue

/-- Lemma 6.9(ii) at the first coordinate after the canonical right switch,
dispatching between the proper right tail and the common suffix. -/
theorem beli2019Lemma69_ii_typeI_rightSuccessorTargetValue_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hl := i.lt_large
        omega⟩ := by
  have hiOdd : Odd i.val := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
  · have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
      a b D C hfirst hrightLast
    exact a.beli2019Lemma69_ii_typeI_targetRightValue
      b D C hfirst hrightLast hdefect i (by omega) (by omega) hiOdd
  · apply a.beli2019Lemma63_sameRank_right_value b hdefect i
    intro k hik hkn
    exact D.profile.lastDifference.after k (by omega) hkn

end BONG.GoodBONG

end Bong
