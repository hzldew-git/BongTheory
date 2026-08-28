/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseOne
import Bong.Bong.Beli2019Lemma88Sufficiency

/-!
# Beli (2019), Lemma 9.3: ordinary Case 2

This file formalizes the complementary arithmetic branch to Case 1.  Since
the exposed rank is at least four, the paper's conditional final inequality
is always present: the first capped comparison defect equals `β₁`, lies below
the second-boundary half-gap, and `β₁ < α₃`.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Case 2 in the proof of Lemma 9.3, in zero-based notation. -/
noncomputable def Beli2019Lemma93CaseTwoCondition
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) : Prop :=
  a.truncatedPrefixDefect b (-1) 3 1 =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∧
  a.truncatedPrefixDefect b (-1) 3 1 <
      ((((b.order (1 : Fin (N + 4)) -
          a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ∧
  (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
    (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)

/-- The two numbered cases in the paper are genuinely exhaustive.  The
right prefix cap gives `d ≤ β₁`; negating the first Case 1 alternative turns
this into `d = β₁`, while the other two negations give the remaining strict
Case 2 inequalities. -/
theorem beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) :
    a.Beli2019Lemma93CaseTwoCondition b ↔
      ¬a.Beli2019Lemma93CaseOneCondition b := by
  let d := a.truncatedPrefixDefect b (-1) 3 1
  let betaOne : WithTop ℚ :=
    (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  let alphaThree : WithTop ℚ :=
    (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
  let threshold : WithTop ℚ :=
    ((((b.order (1 : Fin (N + 4)) -
        a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hdBeta : d ≤ betaOne := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hzero : (⟨1 - 1, by omega⟩ : Fin (N + 3)) =
        (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    rw [hzero] at hcap
    exact hcap
  change (d = betaOne ∧ d < threshold ∧ betaOne < alphaThree) ↔
    ¬(d < betaOne ∨ alphaThree ≤ betaOne ∨ threshold ≤ d)
  constructor
  · rintro ⟨hdbeta, hlow, hbetaAlpha⟩ hcase
    rcases hcase with hstrict | halphaBeta | hlarge
    · exact (lt_irrefl betaOne) (hdbeta ▸ hstrict)
    · exact (not_le_of_gt hbetaAlpha) halphaBeta
    · exact (not_le_of_gt hlow) hlarge
  · intro hnot
    have hnotStrict : ¬d < betaOne := fun h => hnot (Or.inl h)
    have hnotAlpha : ¬alphaThree ≤ betaOne :=
      fun h => hnot (Or.inr (Or.inl h))
    have hnotLarge : ¬threshold ≤ d :=
      fun h => hnot (Or.inr (Or.inr h))
    exact ⟨le_antisymm hdBeta (le_of_not_gt hnotStrict),
      lt_of_not_ge hnotLarge, lt_of_not_ge hnotAlpha⟩

/-- Case 2, like Case 1, is unchanged by replacing either good BONG on its
lattice. -/
theorem beli2019Lemma93CaseTwoCondition_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a c : GoodBONG q L (N + 4))
    (b d : GoodBONG r M (N + 4)) :
    a.Beli2019Lemma93CaseTwoCondition b ↔
      c.Beli2019Lemma93CaseTwoCondition d := by
  rw [a.beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition b,
    c.beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition d,
    a.beli2019Lemma93CaseOneCondition_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      c b d]

/-- The first numerical observation in Case 2:
`β₁ < (S₂-S₁)/2+e`.  Goodness gives `R₁ ≤ R₃`, and the selected heads give
`S₁ = R₁`, so the displayed Case 2 threshold is no larger than the source
half-gap. -/
theorem sourceFirstAlpha_lt_halfGap_of_caseTwo
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    b.alphaValue (0 : Fin (N + 3)) <
      b.halfGapValue (0 : Fin (N + 3)) := by
  unfold Beli2019Lemma93CaseTwoCondition at hcase
  have hlow :
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
        ((((b.order (1 : Fin (N + 4)) -
            a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
    hcase.1 ▸ hcase.2.1
  have houter := a.order_zero_le_two
  have hlowQ : b.alphaValue (0 : Fin (N + 3)) <
      ((b.order (1 : Fin (N + 4)) -
        a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) :=
    WithTop.coe_lt_coe.mp hlow
  unfold halfGapValue orderGap
  have houterQ : (a.order (0 : Fin (N + 4)) : ℚ) ≤
      (a.order (2 : Fin (N + 4)) : ℚ) := by
    exact_mod_cast houter
  have hzeroSucc : (0 : Fin (N + 3)).succ =
      (1 : Fin (N + 4)) := by
    apply Fin.ext
    simp
  have hzeroCast : (0 : Fin (N + 3)).castSucc =
      (0 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hzeroSucc, hzeroCast]
  push_cast at hlowQ ⊢
  rw [← hfirst]
  linarith

set_option maxHeartbeats 800000 in
/-- The one-step analogue of
`thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail`.  If deleting the
head strictly raises the second alpha, the lost first left-defect candidate
attains it; right-endpoint monotonicity then gives
`β₂ = S₃ - S₂ + β₁`. -/
theorem secondAlpha_eq_third_sub_second_add_first_of_lt_tail
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hstrict :
      (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) <
        (a.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    a.alphaValue (1 : Fin (N + 3)) =
      ((a.order (2 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
        a.alphaValue (0 : Fin (N + 3)) := by
  have honeSucc : (0 : Fin (N + 2)).succ =
      (1 : Fin (N + 3)) := by
    apply Fin.ext
    change 0 % (N + 2) + 1 = 1 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hshift : a.alpha (0 : Fin (N + 2)).succ <
      a.tail.alpha (0 : Fin (N + 2)) := by
    rw [honeSucc, ← a.coe_alphaValue, ← a.tail.coe_alphaValue]
    exact hstrict
  have hlostLt :=
    a.firstLeftDefect_lt_tailAlpha_of_alpha_shift_lt
      (0 : Fin (N + 2)) hshift
  have hlost :
      (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) =
        a.leftDefectCandidate (1 : Fin (N + 3))
          (0 : Fin (N + 3)) := by
    rw [a.coe_alphaValue]
    simpa only [honeSucc] using
      a.alpha_shift_eq_firstLeftDefect_of_lt_tailAlpha
        (0 : Fin (N + 2)) hlostLt
  have hadjacentFinite : a.adjacentDefect (0 : Fin (N + 3)) ≠ ⊤ := by
    intro htop
    rw [leftDefectCandidate, htop] at hlost
    simp only [add_top] at hlost
    exact WithTop.coe_ne_top hlost
  let delta : ℚ :=
    (a.adjacentDefect (0 : Fin (N + 3))).untop hadjacentFinite
  have hdelta : (delta : WithTop ℚ) =
      a.adjacentDefect (0 : Fin (N + 3)) :=
    WithTop.coe_untop _ _
  have hlostQ : a.alphaValue (1 : Fin (N + 3)) =
      ((a.order (2 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta := by
    rw [leftDefectCandidate, ← hdelta, ← WithTop.coe_add] at hlost
    exact WithTop.coe_eq_coe.mp hlost
  have hfirstUpperTop :=
    a.alpha_le_leftDefectCandidate
      (i := (0 : Fin (N + 3))) (j := (0 : Fin (N + 3))) le_rfl
  have hfirstUpper : a.alphaValue (0 : Fin (N + 3)) ≤
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta := by
    rw [← a.coe_alphaValue, leftDefectCandidate, ← hdelta,
      ← WithTop.coe_add] at hfirstUpperTop
    exact_mod_cast hfirstUpperTop
  have hendpoint01Le :=
    a.alphaRightEndpoint_antitone
      (show (0 : Fin (N + 3)) ≤ (1 : Fin (N + 3)) by
        change 0 % (N + 3) ≤ 1 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
  have hzeroSucc : (0 : Fin (N + 3)).succ =
      (1 : Fin (N + 4)) := by
    apply Fin.ext
    change 0 % (N + 3) + 1 = 1 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have honeOriginalSucc : (1 : Fin (N + 3)).succ =
      (2 : Fin (N + 4)) := by
    apply Fin.ext
    change 1 % (N + 3) + 1 = 2 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold alphaRightEndpoint at hendpoint01Le
  rw [hzeroSucc, honeOriginalSucc] at hendpoint01Le
  have hfirstLower :
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta ≤
        a.alphaValue (0 : Fin (N + 3)) := by
    push_cast at hendpoint01Le hlostQ ⊢
    linarith
  have hfirstQ : a.alphaValue (0 : Fin (N + 3)) =
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta :=
    le_antisymm hfirstUpper hfirstLower
  push_cast at hlostQ hfirstQ ⊢
  linarith

/-- Either of the two low source-alpha failures isolated in Case 2 forces
the same recursion `β₂ = S₃ - S₂ + β₁`.  For a failure at `β₃`, the
three-step formula makes the first and third right endpoints equal; their
monotonicity then squeezes the middle endpoint to the same value. -/
theorem secondAlpha_eq_third_sub_second_add_first_of_second_or_third_lt_tail
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hfailure :
      (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) <
          (a.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) ∨
        (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
          (a.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)) :
    a.alphaValue (1 : Fin (N + 3)) =
      ((a.order (2 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
        a.alphaValue (0 : Fin (N + 3)) := by
  rcases hfailure with hsecond | hthird
  · exact a.secondAlpha_eq_third_sub_second_add_first_of_lt_tail hsecond
  · have hthirdFormula :=
      a.thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail hthird
    have hzeroSucc : (0 : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      change 0 % (N + 3) + 1 = 1 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have honeSucc : (1 : Fin (N + 3)).succ =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 1 % (N + 3) + 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have htwoSucc : (2 : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hendpoint02 :
        a.alphaRightEndpoint (0 : Fin (N + 3)) =
          a.alphaRightEndpoint (2 : Fin (N + 3)) := by
      unfold alphaRightEndpoint
      rw [hzeroSucc, htwoSucc]
      push_cast at hthirdFormula ⊢
      linarith
    have hendpoint01Le :=
      a.alphaRightEndpoint_antitone
        (show (0 : Fin (N + 3)) ≤ (1 : Fin (N + 3)) by
          change 0 % (N + 3) ≤ 1 % (N + 3)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega)
    have hendpoint12Le :=
      a.alphaRightEndpoint_antitone
        (show (1 : Fin (N + 3)) ≤ (2 : Fin (N + 3)) by
          change 1 % (N + 3) ≤ 2 % (N + 3)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega)
    have hendpoint01 :
        a.alphaRightEndpoint (1 : Fin (N + 3)) =
          a.alphaRightEndpoint (0 : Fin (N + 3)) :=
      le_antisymm hendpoint01Le (hendpoint02.trans_le hendpoint12Le)
    unfold alphaRightEndpoint at hendpoint01
    rw [hzeroSucc, honeSucc] at hendpoint01
    push_cast at hendpoint01 ⊢
    linarith

/-- The order reduction at the start of Case 2.  The five alternatives of
Lemma 9.1 collapse to the two branches retained in the paper:
`R₁ < R₃`, or `R₂ = S₂ < R₄`.  The alternating equal-order possibility is
excluded by Corollary 2.3 and `α₁ ≤ β₁ < α₃`; the first-gap alternative is
excluded by the strict source half-gap inequality; and the fifth alternative
is incompatible with the Case 2 identity `d = β₁`. -/
theorem earlyOrderAlternative_of_caseTwo
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)) ∨
      (a.order (1 : Fin (N + 4)) = b.order (1 : Fin (N + 4)) ∧
        a.order (1 : Fin (N + 4)) < a.order (3 : Fin (N + 4))) := by
  have hsecondLe : a.order (1 : Fin (N + 4)) ≤
      b.order (1 : Fin (N + 4)) :=
    a.secondOrder_le_of_firstOrder_eq b conditions.orderCondition hfirst
  have hfirstAlphaLe : a.alphaValue (0 : Fin (N + 3)) ≤
      b.alphaValue (0 : Fin (N + 3)) :=
    by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.firstAlpha_le_sourceFirstAlpha_of_representationConditions
        b (Nat.le_refl (N + 3)) hfirst conditions
  have hnotAlternating : ¬(
      a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)) ∧
      a.order (1 : Fin (N + 4)) = a.order (3 : Fin (N + 4))) := by
    rintro ⟨houter, hinner⟩
    have hsum : a.adjacentOrderSum (0 : Fin (N + 3)) =
        a.adjacentOrderSum (2 : Fin (N + 3)) := by
      unfold adjacentOrderSum
      change a.order (0 : Fin (N + 4)) +
          a.order (1 : Fin (N + 4)) =
        a.order (2 : Fin (N + 4)) +
          a.order (3 : Fin (N + 4))
      rw [← houter, ← hinner]
    have C := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.beli2009Corollary23
        (0 : Fin (N + 3)) (2 : Fin (N + 3)) (by norm_num) hsum
    have halpha : a.alphaValue (0 : Fin (N + 3)) =
        a.alphaValue (2 : Fin (N + 3)) :=
      C.alpha_eq_of_sameParity
        (0 : Fin (N + 3)) (2 : Fin (N + 3))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
          change (0 : Nat) % 2 = (2 % (N + 3)) % 2
          simp only [Nat.mod_eq_of_lt (show 2 < N + 3 by omega),
            Nat.reduceMod])
    have hstrict := hcase.2.2
    rw [halpha] at hfirstAlphaLe
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hfirstAlphaLe)) hstrict
  have hnotGap : ¬a.orderGap (0 : Fin (N + 3)) =
      2 * (ramificationIndex K : Int) := by
    intro hgap
    have hsourceGap : 2 * (ramificationIndex K : Int) ≤
        b.orderGap (0 : Fin (N + 3)) := by
      unfold orderGap at hgap ⊢
      change 2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4))
      rw [← hgap, ← hfirst]
      exact sub_le_sub_right hsecondLe _
    have hhalf := by
      letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
      exact b.alpha_p4 (0 : Fin (N + 3)) hsourceGap
    exact (ne_of_lt
      (a.sourceFirstAlpha_lt_halfGap_of_caseTwo b hfirst hcase)) hhalf
  have hnotFifth : ¬(
      a.truncatedPrefixDefect b (-1) 3 1 =
          (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∧
        a.alphaValue (0 : Fin (N + 3)) <
          b.alphaValue (0 : Fin (N + 3))) := by
    rintro ⟨hdefect, hstrict⟩
    have halphaBeta :
        (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
          (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
      hdefect.symm.trans hcase.1
    exact (ne_of_lt hstrict)
      (WithTop.coe_injective halphaBeta)
  by_cases hfirstThird :
      a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4))
  · exact Or.inl hfirstThird
  · have hfirstThirdEq : a.order (0 : Fin (N + 4)) =
        a.order (2 : Fin (N + 4)) :=
      le_antisymm a.order_zero_le_two (le_of_not_gt hfirstThird)
    have hsecondFourthLe : a.order (1 : Fin (N + 4)) ≤
        a.order (3 : Fin (N + 4)) := by
      have htail := a.tail.order_zero_le_two
      have hzeroSucc : (⟨0, by omega⟩ : Fin (N + 3)).succ =
          (1 : Fin (N + 4)) := by
        apply Fin.ext
        simp
      have htwoSucc : (⟨2, by omega⟩ : Fin (N + 3)).succ =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        change 2 + 1 = 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [a.order_goodTail, a.order_goodTail,
        hzeroSucc, htwoSucc] at htail
      exact htail
    unfold Lemma91Alternative at hlemma91
    rcases hlemma91 with hfirst | hsecond | hgap | hfourth | hfifth
    · exact (hfirstThird hfirst).elim
    · refine Or.inr ⟨hsecond, ?_⟩
      exact lt_of_le_of_ne hsecondFourthLe
        (fun heq => hnotAlternating ⟨hfirstThirdEq, heq⟩)
    · exact (hnotGap hgap).elim
    · rcases hfourth with ⟨hfour, heq⟩
      have hindex : (⟨3, hfour⟩ : Fin (N + 4)) =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        rfl
      rw [hindex] at heq
      exact (hnotAlternating ⟨hfirstThirdEq, heq⟩).elim
    · exact (hnotFifth hfifth).elim

/-- Lemma 8.8 is applicable to the source in Case 2.  The strict half-gap
inequality rules out the exceptional alternative before any construction is
chosen. -/
theorem exists_firstValueTransform_of_caseTwo
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hstrict := a.sourceFirstAlpha_lt_halfGap_of_caseTwo b hfirst hcase
  have hnotExceptional : ¬b.Beli2019Lemma88Exceptional := by
    rintro ⟨hhalf, _⟩
    exact (ne_of_lt hstrict) hhalf
  exact (b.beli2019Lemma88_i).mpr hnotExceptional

/-- A first-value transform multiplies the first prefix product by its
chosen unit. -/
theorem Beli2019FirstValueTransform.prefixProduct_one_eq
    {b : GoodBONG r M (N + 4)} (T : b.Beli2019FirstValueTransform) :
    T.transformed.prefixProduct 1 = T.epsilon * b.prefixProduct 1 := by
  unfold GoodBONG.prefixProduct
  rw [T.transformed.toBONG.prefixProduct_succ 0 (by omega),
    b.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  exact T.firstValue_eq

/-- The source choice made immediately after invoking Lemma 8.8 in Case 2.
Its uncapped first-three comparison defect is exactly the original `β₁`.
The identity choice is used when this is already true; otherwise Lemma 8.8's
multiplier has the strictly smaller defect and sharp multiplicativity gives
the equality. -/
structure Beli2019Lemma93CaseTwoSourceHeadNormalization
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  transformed : GoodBONG r M (N + 4)
  firstThirdRawDefect_eq :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * transformed.prefixProduct 1) =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)

/-- Existence of the source head normalization used in Case 2. -/
theorem exists_caseTwoSourceHeadNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019Lemma93CaseTwoSourceHeadNormalization a b) := by
  let raw := defectOrder (K := K)
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
  have hrawLe :
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤ raw := by
    have hle := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    exact hcase.1 ▸ hle
  by_cases hrawEq : raw =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  · exact ⟨{
      transformed := b
      firstThirdRawDefect_eq := hrawEq
    }⟩
  · rcases a.exists_firstValueTransform_of_caseTwo b hfirst hcase with ⟨T⟩
    have hstrict :
        (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) < raw :=
      lt_of_le_of_ne hrawLe (fun h => hrawEq h.symm)
    have hproduct :
        (-1 : Kˣ) * a.prefixProduct 3 * T.transformed.prefixProduct 1 =
          T.epsilon * ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [T.prefixProduct_one_eq]
      ac_rfl
    refine ⟨{
      transformed := T.transformed
      firstThirdRawDefect_eq := ?_
    }⟩
    rw [hproduct,
      defectOrder_mul_eq_left_of_lt_right (K := K)
        (T.epsilon_defect ▸ hstrict), T.epsilon_defect]

/-- Lemma 9.2 fixes the first value, hence also the first prefix product. -/
theorem Beli2019Lemma92Transform.prefixProduct_one_eq
    {b : GoodBONG r M (N + 4)} (T : b.Beli2019Lemma92Transform) :
    T.transformed.prefixProduct 1 = b.prefixProduct 1 := by
  unfold GoodBONG.prefixProduct
  rw [T.transformed.toBONG.prefixProduct_succ 0 (by omega),
    b.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  exact T.firstValue_eq

/-- The Case 2 source after its first-value choice and the subsequent Lemma
9.2 tail normalization. -/
structure Beli2019Lemma93CaseTwoSourceNormalization
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  beforeLemma92 : GoodBONG r M (N + 4)
  transform : beforeLemma92.Beli2019Lemma92Transform
  firstThirdRawDefect_eq :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * transform.transformed.prefixProduct 1) =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)

/-- Lemma 9.2 preserves the exact raw defect established by the Case 2
first-value normalization. -/
theorem Beli2019Lemma93CaseTwoSourceHeadNormalization.exists_sourceNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (H : Beli2019Lemma93CaseTwoSourceHeadNormalization a b) :
    Nonempty (Beli2019Lemma93CaseTwoSourceNormalization a b) := by
  rcases H.transformed.beli2019Lemma92 with ⟨T⟩
  refine ⟨{
    beforeLemma92 := H.transformed
    transform := T
    firstThirdRawDefect_eq := ?_
  }⟩
  rw [T.prefixProduct_one_eq]
  exact H.firstThirdRawDefect_eq

/-- The first two source choices in Case 2 form one canonical existence
statement: Lemma 8.8 fixes the raw first-three defect, and Lemma 9.2 then
normalizes the remaining source tail without changing that defect. -/
theorem exists_caseTwoSourceNormalization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019Lemma93CaseTwoSourceNormalization a b) := by
  rcases a.exists_caseTwoSourceHeadNormalization b hfirst hcase with ⟨H⟩
  exact H.exists_sourceNormalization

/-- The paper's observation that the exact Case 2 raw defect is independent
of the target BONG.  The defect of the target prefix-change factor is at
least `α₃`; multiplying the two old/new comparison products differs from
that factor only by a square.  Sharp defect multiplicativity then transports
the strictly smaller value `δ`. -/
theorem firstThirdRawDefect_changeTarget_eq_of_lt_alphaThree
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    (a c : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (delta : WithTop ℚ)
    (hraw : defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) = delta)
    (hlt : delta <
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)) :
    defectOrder (K := K)
        ((-1) * c.prefixProduct 3 * b.prefixProduct 1) = delta := by
  let x : Kˣ := (-1) * a.prefixProduct 3 * b.prefixProduct 1
  let y : Kˣ := (-1) * c.prefixProduct 3 * b.prefixProduct 1
  let z : Kˣ := a.prefixProduct 3 * c.prefixProduct 3
  have hchange :=
    Beli2006PrefixChangeLaws.prefixChangeDefectBound a c 3
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hchange
  have htwo : (⟨3 - 1, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [htwo] at hchange
  have hxyProduct : x * y = z * (b.prefixProduct 1) ^ 2 := by
    dsimp only [x, y, z]
    rw [show (-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1 *
        ((-1) * c.prefixProduct 3 * b.prefixProduct 1) =
      ((-1 : Kˣ) * (-1)) *
        (a.prefixProduct 3 * c.prefixProduct 3) *
          (b.prefixProduct 1 * b.prefixProduct 1) by ac_rfl]
    simp only [neg_mul_neg, one_mul, pow_two]
  have hxyDefect : defectOrder (K := K) (x * y) =
      defectOrder (K := K) z := by
    rw [hxyProduct, defectOrder_mul_square]
  have hxltxy : defectOrder (K := K) x <
      defectOrder (K := K) (x * y) := by
    rw [hxyDefect, hraw]
    exact hlt.trans_le hchange
  have hsharp := defectOrder_mul_eq_left_of_lt_right (K := K) hxltxy
  have hxxyProduct : x * (x * y) = y * x ^ 2 := by
    simp only [pow_two]
    ac_rfl
  calc
    defectOrder (K := K)
        ((-1) * c.prefixProduct 3 * b.prefixProduct 1) =
        defectOrder (K := K) y := by rfl
    _ = defectOrder (K := K) (y * x ^ 2) :=
      (defectOrder_mul_square y x).symm
    _ = defectOrder (K := K) (x * (x * y)) := by rw [hxxyProduct]
    _ = defectOrder (K := K) x := hsharp
    _ = delta := hraw

/-- If the target cap is unchanged while a shifted capped defect becomes
strictly larger after deleting the equal heads, the only possible lost
minimum is the source cap.  Thus the original defect equals that cap, and
the cap itself increases strictly.  This is the order-theoretic core of the
`β₂ < β₂*` / `β₃ < β₃*` reduction in Case 2. -/
theorem truncatedPrefixDefect_eq_rightCap_of_lt_tail_of_leftCap_eq
    {n : Nat}
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0) (epsilon : Kˣ)
    (i j : Nat) (hile : i ≤ n + 1) (hjle : j ≤ n + 1)
    (hcapA : a.prefixAlphaCap (i + 1) = a.tail.prefixAlphaCap i)
    (hstrict :
      a.truncatedPrefixDefect b epsilon (i + 1) (j + 1) <
        a.tail.truncatedPrefixDefect b.tail epsilon i j) :
    a.truncatedPrefixDefect b epsilon (i + 1) (j + 1) =
        b.prefixAlphaCap (j + 1) ∧
      b.prefixAlphaCap (j + 1) < b.tail.prefixAlphaCap j := by
  let raw : WithTop ℚ := defectOrder (K := K)
    (epsilon * a.tail.prefixProduct i * b.tail.prefixProduct j)
  let left : WithTop ℚ := a.tail.prefixAlphaCap i
  let right : WithTop ℚ := b.prefixAlphaCap (j + 1)
  let rightTail : WithTop ℚ := b.tail.prefixAlphaCap j
  have hraw : defectOrder (K := K)
      (epsilon * a.prefixProduct (i + 1) * b.prefixProduct (j + 1)) =
        raw :=
    a.defectOrder_shiftedPrefixes_eq_tail b hhead epsilon i j hile hjle
  have hstrictMin : min raw (min left right) <
      min raw (min left rightTail) := by
    simpa only [truncatedPrefixDefect, hraw, hcapA, raw, left, right,
      rightTail] using hstrict
  have hrawNotLe : ¬raw ≤ min left right := by
    intro hle
    have hlhs : min raw (min left right) = raw := min_eq_left hle
    have hrhs : min raw (min left rightTail) ≤ raw := min_le_left _ _
    rw [hlhs] at hstrictMin
    exact (not_lt_of_ge hrhs) hstrictMin
  have hinnerLtRaw : min left right < raw := lt_of_not_ge hrawNotLe
  have hleftNotLe : ¬left ≤ right := by
    intro hle
    have hlhs : min raw (min left right) = left := by
      rw [min_eq_right hinnerLtRaw.le, min_eq_left hle]
    have hrhs : min raw (min left rightTail) ≤ left :=
      (min_le_right raw _).trans (min_le_left left rightTail)
    rw [hlhs] at hstrictMin
    exact (not_lt_of_ge hrhs) hstrictMin
  have hrightLeLeft : right ≤ left := le_of_not_ge hleftNotLe
  have hlhs : min raw (min left right) = right := by
    rw [min_eq_right hinnerLtRaw.le, min_eq_right hrightLeLeft]
  have hrightLtTail : right < rightTail := by
    rw [hlhs] at hstrictMin
    exact hstrictMin.trans_le
      ((min_le_right raw _).trans (min_le_right left rightTail))
  refine ⟨?_, hrightLtTail⟩
  unfold truncatedPrefixDefect
  rw [hraw, hcapA]
  exact hlhs

/-- The selected pair for Case 2, retaining the exact uncapped defect that
drives all later low-candidate comparisons. -/
structure Beli2019Lemma93CaseTwoNormalizedPair
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  normalized : Beli2019Lemma93NormalizedPair a b
  firstThirdRawDefect_eq_sourceFirstAlpha :
    defectOrder (K := K)
        ((-1) * normalized.targetTransform.transformed.prefixProduct 3 *
          normalized.sourceTransform.transformed.prefixProduct 1) =
      (normalized.sourceTransform.transformed.alphaValue
        (0 : Fin (N + 3)) : WithTop ℚ)

/-- After the source has been normalized, Lemmas 9.1 and 9.2 select the
target.  Prefix-change domination and the strict `β₁ < α₃` inequality show
that the exact raw defect survives both target changes. -/
theorem Beli2019Lemma93CaseTwoSourceNormalization.exists_normalizedPair
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (S : Beli2019Lemma93CaseTwoSourceNormalization a b)
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019Lemma93CaseTwoNormalizedPair a b) := by
  have hsourceOrders : b.SameOrders S.beforeLemma92 := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant S.beforeLemma92
  have hfirstSelected : a.order (0 : Fin (N + 4)) =
      S.beforeLemma92.order (0 : Fin (N + 4)) :=
    hfirst.trans (hsourceOrders (0 : Fin (N + 4)))
  have selectedConditions :
      RepresentationConditions a S.beforeLemma92 (Nat.le_refl (N + 3)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      a b S.beforeLemma92 (Nat.le_refl (N + 3))).mp conditions
  have hlemma91Selected : a.Lemma91Alternative S.beforeLemma92 :=
    (a.lemma91Alternative_changeSource_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      b S.beforeLemma92).mp hlemma91
  rcases a.beli2019Lemma91_sameRank
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity)
      (targetLocalization := targetLocalization)
      (targetConstruction := targetConstruction)
      (targetSectionTwo := targetSectionTwo)
      (targetBinaryScaling := targetBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      S.beforeLemma92 hfirstSelected ambient selectedConditions
        hlemma91Selected with ⟨D⟩
  have hTa : Nonempty (Beli2019Lemma92Transform D.transformed) := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    letI : Beli2009AlphaParityLaws.{u, v} K := targetParity
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := targetLocalization
    letI : BeliLemma43ConstructionLaws.{u, v} K := targetConstruction
    letI : Beli2006SectionTwoLaws.{u, v} K := targetSectionTwo
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := targetBinaryScaling
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K :=
      targetQuaternaryScaling
    letI : BeliLemma49Laws.{u, v} K := targetLemma49
    letI : BeliLemma47Laws.{u, v} K := targetLemma47
    exact D.transformed.beli2019Lemma92
  rcases hTa with ⟨Ta⟩
  let normalized : Beli2019Lemma93NormalizedPair a b :=
    Beli2019Lemma93NormalizedPair.ofTransforms
      (classificationV := classificationV) (classificationW := classificationW)
      a b conditions D.transformed S.beforeLemma92
      (D.firstValue_eq.trans S.beforeLemma92.firstUnarySegment_valueUnit_zero)
      Ta S.transform
  have hrawOriginal :
      defectOrder (K := K)
          ((-1) * Ta.transformed.prefixProduct 3 *
            S.transform.transformed.prefixProduct 1) =
        (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
    firstThirdRawDefect_changeTarget_eq_of_lt_alphaThree
      (prefixChangeV := prefixChangeV)
      a Ta.transformed S.transform.transformed
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
      S.firstThirdRawDefect_eq hcase.2.2
  have hsourceAlpha : b.alphaValue (0 : Fin (N + 3)) =
      S.transform.transformed.alphaValue (0 : Fin (N + 3)) := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant S.transform.transformed (0 : Fin (N + 3))
  refine ⟨{
    normalized := normalized
    firstThirdRawDefect_eq_sourceFirstAlpha := ?_
  }⟩
  change defectOrder (K := K)
      ((-1) * Ta.transformed.prefixProduct 3 *
        S.transform.transformed.prefixProduct 1) =
    (S.transform.transformed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  exact hrawOriginal.trans (congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceAlpha)

/-- End-to-end existence of the pair selected in ordinary Case 2.  This
composes the source first-value choice, both Lemma 9.2 normalizations, and
the Lemma 9.1 target-head prescription in the order used in the paper. -/
theorem exists_beli2019Lemma93CaseTwoNormalizedPair
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    Nonempty (Beli2019Lemma93CaseTwoNormalizedPair a b) := by
  rcases a.exists_caseTwoSourceNormalization b hfirst hcase with ⟨S⟩
  exact S.exists_normalizedPair
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    (targetParity := targetParity)
    (targetLocalization := targetLocalization)
    (targetConstruction := targetConstruction)
    (targetSectionTwo := targetSectionTwo)
    (classificationV := classificationV) (classificationW := classificationW)
    (targetBinaryScaling := targetBinaryScaling)
    (targetQuaternaryScaling := targetQuaternaryScaling)
    (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
    (structuralV := structuralV) (structuralW := structuralW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    (sectionFiveW := sectionFiveW)
    (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
    (deepWW := deepWW)
    hfirst ambient conditions hlemma91 hcase

/-- The selected pair remains in Case 2. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.selectedCaseTwoCondition
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
      P.normalized.sourceTransform.transformed :=
  (a.beli2019Lemma93CaseTwoCondition_changeBONG_iff
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    P.normalized.targetTransform.transformed b
      P.normalized.sourceTransform.transformed).mp hcase

/-- The two surviving order branches hold for the fully selected BONGs,
not merely for the original presentation. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.selectedEarlyOrderAlternative
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseTwoCondition b) :
    P.normalized.targetTransform.transformed.order (0 : Fin (N + 4)) <
        P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ∨
      (P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) =
          P.normalized.sourceTransform.transformed.order (1 : Fin (N + 4)) ∧
        P.normalized.targetTransform.transformed.order (1 : Fin (N + 4)) <
          P.normalized.targetTransform.transformed.order
            (3 : Fin (N + 4))) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hfirst : A.order (0 : Fin (N + 4)) =
      B.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  have hlemma91' : A.Lemma91Alternative B :=
    (a.lemma91Alternative_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      A b B).mp hlemma91
  have hcase' : A.Beli2019Lemma93CaseTwoCondition B :=
    P.selectedCaseTwoCondition
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      hcase
  exact A.earlyOrderAlternative_of_caseTwo
    (targetLaws := targetLaws) (sourceLaws := sourceLaws)
    B hfirst P.normalized.selectedConditions hlemma91' hcase'

/-- At the first tail boundary, the exact raw defect squeezes the tail capped
defect to the same `β₁` value. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.firstThirdDefect_eq_tail
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) 3 1 =
      P.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed.tail (-1) 2 0 := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let betaOne : WithTop ℚ :=
    (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  have hdecomp := A.firstThirdDefect_eq_min_tail_alpha_three_beta_one
    B P.normalized.headValue_eq
  have hcaps : min
      (A.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) betaOne = betaOne :=
    min_eq_right hcase.2.2.le
  have htailLower : betaOne ≤
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 := by
    have hmin : min (A.tail.truncatedPrefixDefect B.tail (-1) 2 0)
        betaOne = betaOne := by
      rw [hcaps] at hdecomp
      exact hdecomp.symm.trans hcase.1
    exact min_eq_right_iff.mp hmin
  have htailUpper :
      A.tail.truncatedPrefixDefect B.tail (-1) 2 0 ≤ betaOne := by
    have hrawShift := A.defectOrder_shiftedPrefixes_eq_tail B
      P.normalized.headValue_eq (-1) 2 0 (by omega) (by omega)
    have hle := A.tail.truncatedPrefixDefect_le_defect B.tail (-1) 2 0
    rw [← hrawShift,
      P.firstThirdRawDefect_eq_sourceFirstAlpha] at hle
    exact hle
  change A.truncatedPrefixDefect B (-1) 3 1 =
    A.tail.truncatedPrefixDefect B.tail (-1) 2 0
  rw [hcase.1]
  exact le_antisymm htailLower htailUpper

/-- Consequently the first comparison alpha after head deletion is exactly
the shifted original second comparison alpha. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.firstRepresentationAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed) :
    P.normalized.targetTransform.transformed.tail.representationAlpha
        P.normalized.sourceTransform.transformed.tail
        (firstRepresentationIndex (N + 1) (N + 2)) =
      P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
        (secondRepresentationIndex (N + 1) (N + 2)) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hfirst : A.order (0 : Fin (N + 4)) =
      B.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  exact representationAlpha_tail_first_eq_originalSecond_of_defect_eq
    A B hfirst (P.firstThirdDefect_eq_tail hcase)

/-- Lemma 8.12(ii) selects its primary term at the second boundary in Case
2.  The Case-2 strict threshold is exactly the inequality saying that this
term is smaller than the half-gap term. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.secondRepresentationAlpha_eq_primary
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
        (secondRepresentationIndex (N + 1) (N + 2)) =
      P.normalized.targetTransform.transformed.secondRepresentationPrimaryFormula
        P.normalized.sourceTransform.transformed := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let d := A.truncatedPrefixDefect B (-1) 3 1
  have hd : d = (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    dsimp only [d, A, B]
    exact hcase.1
  have hfirst : A.order (0 : Fin (N + 4)) =
      B.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [A.toBONG.order_eq_ordUnit, B.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact P.normalized.headValue_eq)
  have hlowQ : B.alphaValue (0 : Fin (N + 3)) <
      ((B.order (1 : Fin (N + 4)) -
        A.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    have hlow : d <
        ((((B.order (1 : Fin (N + 4)) -
          A.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
      dsimp only [d, A, B]
      exact hcase.2.1
    rw [hd] at hlow
    exact WithTop.coe_lt_coe.mp hlow
  have hprimaryLtHalf : A.secondRepresentationPrimaryFormula B <
      A.secondRepresentationHalfGapFormula B := by
    unfold secondRepresentationPrimaryFormula
      secondRepresentationHalfGapFormula
    change
      ((((A.order (2 : Fin (N + 4)) -
        B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) + d) < _
    rw [hd, ← WithTop.coe_add]
    apply WithTop.coe_lt_coe.mpr
    push_cast at hlowQ ⊢
    linarith
  have hformula := A.beli2019Lemma812_ii B hfirst
  change A.representationAlpha B
      (secondRepresentationIndex (N + 1) (N + 2)) = _
  rw [hformula, min_eq_right hprimaryLtHalf.le]

/-- Paper formula (9.3, Case 2):
`A₂ = R₃ - S₂ + β₁`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.secondRepresentationAlpha_eq_formula
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
        (secondRepresentationIndex (N + 1) (N + 2)) =
      (((P.normalized.targetTransform.transformed.order
            (2 : Fin (N + 4)) -
          P.normalized.sourceTransform.transformed.order
            (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        (P.normalized.sourceTransform.transformed.alphaValue
          (0 : Fin (N + 3)) : WithTop ℚ) := by
  rw [P.secondRepresentationAlpha_eq_primary hcase]
  unfold secondRepresentationPrimaryFormula
  rw [hcase.1]

/-- Condition 2.1(ii) bounds the second comparison invariant by the second
source alpha, i.e. `A₂ ≤ β₂`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.secondRepresentationAlpha_le_sourceSecondAlpha
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
        (secondRepresentationIndex (N + 1) (N + 2)) ≤
      (P.normalized.sourceTransform.transformed.alphaValue
        (1 : Fin (N + 3)) : WithTop ℚ) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let second : RepresentationIndex (N + 4) (N + 4) :=
    secondRepresentationIndex (N + 1) (N + 2)
  have h := A.representationAlpha_le_rightAlpha B
    P.normalized.selectedConditions.defectCondition second
  have hindex : (⟨second.val - 1, by
      have := second.pos
      have := second.lt_large
      omega⟩ : Fin (N + 3)) = (1 : Fin (N + 3)) := by
    apply Fin.ext
    change second.val - 1 = 1 % (N + 3)
    simp only [second, secondRepresentationIndex]
    rw [Nat.mod_eq_of_lt (by omega)]
  simpa only [A, B, second, hindex] using h

/-- At a later primary candidate, strict growth after head deletion can only
come from the source alpha cap.  In paper notation this says that a strict
failure is precisely `d[-a₁,ᵢ₊₁ b₁,ᵢ₋₁] = βᵢ₋₁ < βᵢ₋₁*`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.primaryStrict_sourceAlphaFailure
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hi : 1 < i.val)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    P.normalized.targetTransform.transformed.truncatedPrefixDefect
        P.normalized.sourceTransform.transformed (-1) (i.val + 2) i.val =
          (P.normalized.sourceTransform.transformed.alphaValue
            ⟨i.val - 1, by have := i.lt_large; omega⟩ : WithTop ℚ) ∧
      (P.normalized.sourceTransform.transformed.alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩ : WithTop ℚ) <
        (P.normalized.sourceTransform.transformed.tail.alphaValue
          ⟨i.val - 2, by have := i.lt_large; omega⟩ : WithTop ℚ) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hdefect :
      A.truncatedPrefixDefect B (-1) ((i.val + 1) + 1)
          ((i.val - 1) + 1) <
        A.tail.truncatedPrefixDefect B.tail (-1) (i.val + 1)
          (i.val - 1) := by
    have h := hstrict
    unfold representationPrimaryDefect at h
    rw [A.order_goodTail, B.order_goodTail] at h
    let coefficient : WithTop ℚ :=
      (((A.order (⟨i.val, by have := i.lt_large; omega⟩ : Fin (N + 3)).succ -
        B.order (⟨i.val - 1, by have := i.lt_large; omega⟩ :
          Fin (N + 3)).succ : Int) : ℚ) : WithTop ℚ)
    have htargetOrder :
        A.order (⟨i.tailShift.val, i.tailShift.lt_large⟩ : Fin (N + 4)) =
          A.order (⟨i.val, by have := i.lt_large; omega⟩ :
            Fin (N + 3)).succ := by
      congr 1
    have hsourceOrder :
        B.order (⟨i.tailShift.val - 1, by
          exact lt_of_le_of_lt (Nat.sub_le _ _) i.tailShift.lt_large⟩ :
            Fin (N + 4)) =
          B.order (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (N + 3)).succ := by
      congr 1
      apply Fin.ext
      simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
      omega
    have hleftDefect :
        A.truncatedPrefixDefect B (-1)
            (i.tailShift.val + 1) (i.tailShift.val - 1) =
          A.truncatedPrefixDefect B (-1) ((i.val + 1) + 1)
            ((i.val - 1) + 1) := by
      congr 2 <;> simp only [RepresentationIndex.tailShift_val] <;> omega
    rw [htargetOrder, hsourceOrder, hleftDefect] at h
    change coefficient +
        A.truncatedPrefixDefect B (-1) ((i.val + 1) + 1)
            ((i.val - 1) + 1) <
      coefficient + A.tail.truncatedPrefixDefect B.tail (-1)
        (i.val + 1) (i.val - 1) at h
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp h
  have htargetCap : A.prefixAlphaCap ((i.val + 1) + 1) =
      A.tail.prefixAlphaCap (i.val + 1) :=
    A.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
      (fun k hk ↦
        P.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
      (i.val + 1) (by omega) (by have := i.lt_large; omega)
  have H := truncatedPrefixDefect_eq_rightCap_of_lt_tail_of_leftCap_eq
    A B P.normalized.headValue_eq (-1) (i.val + 1) (i.val - 1)
      (by have := i.lt_large; omega) (by have := i.lt_large; omega)
      htargetCap hdefect
  have horiginalCap : B.prefixAlphaCap ((i.val - 1) + 1) =
      (B.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ :
        WithTop ℚ) := by
    have hlen : i.val - 1 + 1 = i.val := by omega
    rw [hlen, B.prefixAlphaCap_of_internal (by omega)
      (by have := i.lt_large; omega)]
  have htailCap : B.tail.prefixAlphaCap (i.val - 1) =
      (B.tail.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ :
        WithTop ℚ) := by
    rw [B.tail.prefixAlphaCap_of_internal (by omega)
      (by have := i.lt_large; omega)]
    congr 2 <;> omega
  change A.truncatedPrefixDefect B (-1) (i.val + 2) i.val = _ ∧ _
  constructor
  · calc
      A.truncatedPrefixDefect B (-1) (i.val + 2) i.val =
          A.truncatedPrefixDefect B (-1) ((i.val + 1) + 1)
            ((i.val - 1) + 1) := by congr 2 <;> omega
      _ = B.prefixAlphaCap ((i.val - 1) + 1) := H.1
      _ = _ := horiginalCap
  · rw [← horiginalCap, ← htailCap]
    exact H.2

/-- A strict primary-candidate failure at either of the only two relevant
low boundaries forces the common source recursion used in the rest of Case
2.  This packages the paper's two alternatives `β₂ < β₂*` and
`β₃ < β₃*` into their shared conclusion. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.sourceSecondAlphaFormula_of_primaryStrict
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hlow : i.val = 2 ∨ i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    P.normalized.sourceTransform.transformed.alphaValue
        (1 : Fin (N + 3)) =
      ((P.normalized.sourceTransform.transformed.order
          (2 : Fin (N + 4)) -
        P.normalized.sourceTransform.transformed.order
          (1 : Fin (N + 4)) : Int) : ℚ) +
        P.normalized.sourceTransform.transformed.alphaValue
          (0 : Fin (N + 3)) := by
  let B := P.normalized.sourceTransform.transformed
  have H := P.primaryStrict_sourceAlphaFailure
    (classificationV := classificationV) i (by omega) hstrict
  apply B.secondAlpha_eq_third_sub_second_add_first_of_second_or_third_lt_tail
  rcases hlow with htwo | hthree
  · left
    have h := H.2
    have hleft : (⟨i.val - 1, by have := i.lt_large; omega⟩ :
        Fin (N + 3)) = (1 : Fin (N + 3)) := by
      apply Fin.ext
      change i.val - 1 = 1 % (N + 3)
      rw [htwo, Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨i.val - 2, by have := i.lt_large; omega⟩ :
        Fin (N + 2)) = (0 : Fin (N + 2)) := by
      apply Fin.ext
      change i.val - 2 = 0 % (N + 2)
      rw [htwo]
      simp
    simpa only [B, hleft, hright] using h
  · right
    have h := H.2
    have hleft : (⟨i.val - 1, by have := i.lt_large; omega⟩ :
        Fin (N + 3)) = (2 : Fin (N + 3)) := by
      apply Fin.ext
      change i.val - 1 = 2 % (N + 3)
      rw [hthree, Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨i.val - 2, by have := i.lt_large; omega⟩ :
        Fin (N + 2)) = (1 : Fin (N + 2)) := by
      apply Fin.ext
      change i.val - 2 = 1 % (N + 2)
      rw [hthree, Nat.mod_eq_of_lt (by omega)]
    simpa only [B, hleft, hright] using h

/-- Under either low primary failure, the raw defect of the second source
adjacent pair is strictly larger than `β₁`.  Equality would make the first
or second tail left candidate no larger than the corresponding original
alpha, contradicting the strict source-alpha failure. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.sourceSecondAdjacentDefect_gt_firstAlpha_of_primaryStrict
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hlow : i.val = 2 ∨ i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    (P.normalized.sourceTransform.transformed.alphaValue
        (0 : Fin (N + 3)) : WithTop ℚ) <
      P.normalized.sourceTransform.transformed.adjacentDefect
        (1 : Fin (N + 3)) := by
  let B := P.normalized.sourceTransform.transformed
  have hformulaTwo := P.sourceSecondAlphaFormula_of_primaryStrict
    (sourceLaws := sourceLaws) (classificationV := classificationV)
    i hlow hstrict
  have hfailure := (P.primaryStrict_sourceAlphaFailure
    (classificationV := classificationV) i (by omega) hstrict).2
  have hbetaLe : (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤
      B.adjacentDefect (1 : Fin (N + 3)) := by
    have hbound := B.alpha_le_leftDefectCandidate
      (i := (1 : Fin (N + 3))) (j := (1 : Fin (N + 3))) le_rfl
    rw [← B.coe_alphaValue, leftDefectCandidate] at hbound
    have honeSucc : (1 : Fin (N + 3)).succ =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 1 % (N + 3) + 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have honeCast : (1 : Fin (N + 3)).castSucc =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      change 1 % (N + 3) = 1 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [honeSucc, honeCast] at hbound
    have hformulaTop := congrArg (fun z : ℚ => (z : WithTop ℚ)) hformulaTwo
    rw [hformulaTop] at hbound
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hbound
  by_contra hnot
  have hadjLe : B.adjacentDefect (1 : Fin (N + 3)) ≤
      (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
    le_of_not_gt hnot
  have hadjEq : B.adjacentDefect (1 : Fin (N + 3)) =
      (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
    le_antisymm hadjLe hbetaLe
  rcases hlow with htwo | hthree
  · have hleft : (⟨i.val - 1, by have := i.lt_large; omega⟩ :
        Fin (N + 3)) = (1 : Fin (N + 3)) := by
      apply Fin.ext
      change i.val - 1 = 1 % (N + 3)
      rw [htwo, Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨i.val - 2, by have := i.lt_large; omega⟩ :
        Fin (N + 2)) = (0 : Fin (N + 2)) := by
      apply Fin.ext
      change i.val - 2 = 0 % (N + 2)
      rw [htwo]
      simp
    have hstrictTwo :
        (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) <
          (B.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
      simpa only [B, hleft, hright] using hfailure
    have htailBound := B.tail.alpha_le_leftDefectCandidate
      (i := (0 : Fin (N + 2))) (j := (0 : Fin (N + 2))) le_rfl
    rw [← B.tail.coe_alphaValue, leftDefectCandidate,
      B.order_goodTail, B.order_goodTail, B.adjacentDefect_tail] at htailBound
    have htailCandidate :
        (((B.order (2 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
            B.adjacentDefect (1 : Fin (N + 3)) =
          (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
      rw [hadjEq, ← WithTop.coe_add]
      exact congrArg (fun z : ℚ => (z : WithTop ℚ)) hformulaTwo.symm
    have htailLe :
        (B.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) ≤
          (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
      apply htailBound.trans_eq
      convert htailCandidate using 1 <;> congr 3 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge htailLe) hstrictTwo
  · have hleft : (⟨i.val - 1, by have := i.lt_large; omega⟩ :
        Fin (N + 3)) = (2 : Fin (N + 3)) := by
      apply Fin.ext
      change i.val - 1 = 2 % (N + 3)
      rw [hthree, Nat.mod_eq_of_lt (by omega)]
    have hright : (⟨i.val - 2, by have := i.lt_large; omega⟩ :
        Fin (N + 2)) = (1 : Fin (N + 2)) := by
      apply Fin.ext
      change i.val - 2 = 1 % (N + 2)
      rw [hthree, Nat.mod_eq_of_lt (by omega)]
    have hstrictThree :
        (B.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
          (B.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
      simpa only [B, hleft, hright] using hfailure
    have hformulaThree :=
      B.thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail hstrictThree
    have htailBound := B.tail.alpha_le_leftDefectCandidate
      (i := (1 : Fin (N + 2))) (j := (0 : Fin (N + 2))) (by
        change 0 % (N + 2) ≤ 1 % (N + 2)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
    rw [← B.tail.coe_alphaValue, leftDefectCandidate,
      B.order_goodTail, B.order_goodTail, B.adjacentDefect_tail] at htailBound
    have htailCandidate :
        (((B.order (3 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
            B.adjacentDefect (1 : Fin (N + 3)) =
          (B.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
      rw [hadjEq, ← WithTop.coe_add]
      exact congrArg (fun z : ℚ => (z : WithTop ℚ)) hformulaThree.symm
    have htailLe :
        (B.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
          (B.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
      apply htailBound.trans_eq
      convert htailCandidate using 1 <;> congr 3 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge htailLe) hstrictThree

/-- The strict adjacent-source defect lets the exact first-three/first-source
defect absorb the factor `-b₂b₃`.  Hence the raw comparison defect through
the first three entries on both sides is still `β₁`:
`d(a₁a₂a₃b₁b₂b₃) = β₁`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.firstThreeComparisonRawDefect_eq_firstAlpha_of_primaryStrict
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hlow : i.val = 2 ∨ i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    defectOrder (K := K)
        ((1 : Kˣ) *
          P.normalized.targetTransform.transformed.prefixProduct 3 *
          P.normalized.sourceTransform.transformed.prefixProduct 3) =
      (P.normalized.sourceTransform.transformed.alphaValue
        (0 : Fin (N + 3)) : WithTop ℚ) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let x : Kˣ := (-1) * A.prefixProduct 3 * B.prefixProduct 1
  let y : Kˣ := B.adjacentProduct (1 : Fin (N + 3))
  have hx : defectOrder (K := K) x =
      (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    dsimp only [x, A, B]
    exact P.firstThirdRawDefect_eq_sourceFirstAlpha
  have hy : (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
      defectOrder (K := K) y := by
    simpa only [y, adjacentDefect] using
      P.sourceSecondAdjacentDefect_gt_firstAlpha_of_primaryStrict
        (sourceLaws := sourceLaws) (classificationV := classificationV)
        i hlow hstrict
  have hprefixTwo : B.prefixProduct 2 =
      B.prefixProduct 1 * B.valueUnit (1 : Fin (N + 4)) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    simpa using B.toBONG.prefixProduct_succ 1 (by omega)
  have hprefixThree : B.prefixProduct 3 =
      B.prefixProduct 2 * B.valueUnit
        (⟨2, by omega⟩ : Fin (N + 4)) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    simpa using B.toBONG.prefixProduct_succ 2 (by omega)
  have hxy : x * y = (1 : Kˣ) * A.prefixProduct 3 * B.prefixProduct 3 := by
    dsimp only [x, y]
    unfold adjacentProduct
    have hcast : (1 : Fin (N + 3)).castSucc =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      simp
    have hsucc : (1 : Fin (N + 3)).succ =
        (⟨2, by omega⟩ : Fin (N + 4)) := by
      apply Fin.ext
      simp
    rw [hcast, hsucc, hprefixThree, hprefixTwo]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one]
    ring
  have hxyDefect : defectOrder (K := K) (x * y) =
      defectOrder (K := K) x :=
    defectOrder_mul_eq_left_of_lt_right (K := K) (hx ▸ hy)
  calc
    defectOrder (K := K) ((1 : Kˣ) * A.prefixProduct 3 *
        B.prefixProduct 3) = defectOrder (K := K) (x * y) := by rw [hxy]
    _ = defectOrder (K := K) x := hxyDefect
    _ = (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := hx

/-- The ordinary third comparison boundary used in the low Case-2
calculation. -/
def lemma93ThirdRepresentationIndex (N : Nat) :
    RepresentationIndex (N + 4) (N + 4) where
  val := 3
  pos := by omega
  lt_large := by omega
  le_small := by omega

/-- Paper inequality `A₃ ≤ β₁`.  Condition 2.1(ii) bounds `A₃` by the
capped three-by-three comparison defect; the preceding raw-defect identity
bounds that capped defect by `β₁`. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.thirdRepresentationAlpha_le_firstSourceAlpha_of_primaryStrict
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hlow : i.val = 2 ∨ i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i) :
    P.normalized.targetTransform.transformed.representationAlpha
        P.normalized.sourceTransform.transformed
        (lemma93ThirdRepresentationIndex N) ≤
      (P.normalized.sourceTransform.transformed.alphaValue
        (0 : Fin (N + 3)) : WithTop ℚ) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  let third := lemma93ThirdRepresentationIndex N
  have hcondition :=
    P.normalized.selectedConditions.defectCondition third
  rw [A.coe_representationAlphaValue B third] at hcondition
  have hcapped := A.truncatedPrefixDefect_le_defect B (1 : Kˣ) 3 3
  have hraw :=
    P.firstThreeComparisonRawDefect_eq_firstAlpha_of_primaryStrict
      (sourceLaws := sourceLaws) (classificationV := classificationV)
      i hlow hstrict
  change A.representationAlpha B third ≤
    (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  exact hcondition.trans (hcapped.trans_eq hraw)

/-- The order-theoretic last step in the first three-index claim of Case 2.
The three displayed weak reverse inequalities negate, respectively, the
first, second, and first essentiality clauses at tail indices `2,3,4` in the
paper's one-based notation. -/
theorem tail_lowThree_not_essential_of_order_bounds
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfive : 5 < N + 4)
    (hleft : a.order (⟨3, by omega⟩ : Fin (N + 4)) ≤
      b.order (⟨1, by omega⟩ : Fin (N + 4)))
    (hmiddle : a.order (⟨4, by omega⟩ : Fin (N + 4)) +
        a.order (⟨5, hfive⟩ : Fin (N + 4)) ≤
      b.order (⟨1, by omega⟩ : Fin (N + 4)) +
        b.order (⟨2, by omega⟩ : Fin (N + 4)))
    (hright : a.order (⟨5, hfive⟩ : Fin (N + 4)) ≤
      b.order (⟨3, by omega⟩ : Fin (N + 4))) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨1, by omega⟩ : Fin (N + 3))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 3))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 3))) := by
  constructor
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.1 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨1 - 1, by omega⟩ <
      a.tail.order ⟨1 + 1, by omega⟩ at hcross
    rw [b.order_goodTail, a.order_goodTail] at hcross
    have hcross' : b.order (⟨1, by omega⟩ : Fin (N + 4)) <
        a.order (⟨3, by omega⟩ : Fin (N + 4)) := by
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hleft) hcross'
  constructor
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.2 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨2 - 2, by omega⟩ +
          b.tail.order ⟨2 - 1, by omega⟩ <
        a.tail.order ⟨2 + 1, by omega⟩ +
          a.tail.order ⟨2 + 2, by omega⟩ at hcross
    rw [b.order_goodTail, b.order_goodTail,
      a.order_goodTail, a.order_goodTail] at hcross
    have hcross' :
        b.order (⟨1, by omega⟩ : Fin (N + 4)) +
            b.order (⟨2, by omega⟩ : Fin (N + 4)) <
          a.order (⟨4, by omega⟩ : Fin (N + 4)) +
            a.order (⟨5, hfive⟩ : Fin (N + 4)) := by
      convert hcross using 1 <;> congr 2 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hmiddle) hcross'
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.1 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨3 - 1, by omega⟩ <
      a.tail.order ⟨3 + 1, by omega⟩ at hcross
    rw [b.order_goodTail, a.order_goodTail] at hcross
    have hcross' : b.order (⟨3, by omega⟩ : Fin (N + 4)) <
        a.order (⟨5, hfive⟩ : Fin (N + 4)) := by
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hright) hcross'

/-- The exact order pattern obtained in the secondary-candidate branch of
the paper's first claim.  From `R₅>S₃` and
`R₅+R₆<S₂+S₃`, goodness yields `R₄≤R₆<S₂≤S₄`; the preceding lemma then
discharges nonessentiality of tail indices `2,3,4`. -/
theorem tail_lowThree_not_essential_of_sum_lt
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfive : 5 < N + 4)
    (hcross : b.order (⟨2, by omega⟩ : Fin (N + 4)) <
      a.order (⟨4, by omega⟩ : Fin (N + 4)))
    (hsum : a.order (⟨4, by omega⟩ : Fin (N + 4)) +
        a.order (⟨5, hfive⟩ : Fin (N + 4)) <
      b.order (⟨1, by omega⟩ : Fin (N + 4)) +
        b.order (⟨2, by omega⟩ : Fin (N + 4))) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨1, by omega⟩ : Fin (N + 3))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 3))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 3))) := by
  have hsixLtSecond :
      a.order (⟨5, hfive⟩ : Fin (N + 4)) <
        b.order (⟨1, by omega⟩ : Fin (N + 4)) := by
    omega
  have htargetGoodRaw :=
    a.good (⟨3, by omega⟩ : Fin (N + 4)) (by omega)
  have htargetGood :
      a.order (⟨3, by omega⟩ : Fin (N + 4)) ≤
        a.order (⟨5, hfive⟩ : Fin (N + 4)) := by
    convert htargetGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  have hsourceGoodRaw :=
    b.good (⟨1, by omega⟩ : Fin (N + 4)) (by
      change 1 + 2 < N + 4
      omega)
  have hsourceGood :
      b.order (⟨1, by omega⟩ : Fin (N + 4)) ≤
        b.order (⟨3, by omega⟩ : Fin (N + 4)) := by
    convert hsourceGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  exact tail_lowThree_not_essential_of_order_bounds a b hfive
    (htargetGood.trans hsixLtSecond.le) hsum.le
    (hsixLtSecond.le.trans hsourceGood)

/-- Combining `A₂ = R₃-S₂+β₁`, condition (ii)'s `A₂ ≤ β₂`, and
`β₂ = S₃-S₂+β₁` gives the order comparison `R₃ ≤ S₃` used throughout the
remaining Case-2 analysis. -/
theorem Beli2019Lemma93CaseTwoNormalizedPair.thirdTargetOrder_le_thirdSourceOrder_of_primaryStrict
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (P : Beli2019Lemma93CaseTwoNormalizedPair a b)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hlow : i.val = 2 ∨ i.val = 3)
    (hstrict :
      P.normalized.targetTransform.transformed.representationPrimaryDefect
          P.normalized.sourceTransform.transformed i.tailShift <
        P.normalized.targetTransform.transformed.tail.representationPrimaryDefect
          P.normalized.sourceTransform.transformed.tail i)
    (hcase :
      P.normalized.targetTransform.transformed.Beli2019Lemma93CaseTwoCondition
        P.normalized.sourceTransform.transformed) :
    P.normalized.targetTransform.transformed.order (2 : Fin (N + 4)) ≤
      P.normalized.sourceTransform.transformed.order (2 : Fin (N + 4)) := by
  let A := P.normalized.targetTransform.transformed
  let B := P.normalized.sourceTransform.transformed
  have hbound := P.secondRepresentationAlpha_le_sourceSecondAlpha
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  have htargetFormula := P.secondRepresentationAlpha_eq_formula hcase
  have hsourceFormula := P.sourceSecondAlphaFormula_of_primaryStrict
    (sourceLaws := sourceLaws) (classificationV := classificationV)
    i hlow hstrict
  have hsourceFormulaTop :
      (B.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) =
        (((B.order (2 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
          (B.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun z : ℚ => (z : WithTop ℚ)) hsourceFormula
  rw [htargetFormula, hsourceFormulaTop] at hbound
  have hdiffTop :
      (((A.order (2 : Fin (N + 4)) -
        B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) ≤
        (((B.order (2 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) :=
    (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp hbound
  have hdiffQ :
      ((A.order (2 : Fin (N + 4)) -
        B.order (1 : Fin (N + 4)) : Int) : ℚ) ≤
        ((B.order (2 : Fin (N + 4)) -
          B.order (1 : Fin (N + 4)) : Int) : ℚ) :=
    WithTop.coe_le_coe.mp hdiffTop
  have hordersQ : (A.order (2 : Fin (N + 4)) : ℚ) ≤
      (B.order (2 : Fin (N + 4)) : ℚ) := by
    push_cast at hdiffQ
    linarith
  exact_mod_cast hordersQ

end BONG.GoodBONG

end Bong
