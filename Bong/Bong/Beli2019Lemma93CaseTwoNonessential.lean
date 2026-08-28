/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwo

/-!
# Beli (2019), Lemma 9.3: the first nonessential triple in Case 2

This file formalizes the claim following the inequalities `A₃ ≤ β₁` and
`R₃ ≤ S₃`.  The v2 source contains an index typo in the displayed hypothesis
of the claim: Definition 4 and the subsequent calculation use
`R₅ + R₆ - S₃ - S₄ + d[-a₁,₄ b₁,₂]`, not the printed
`R₅ + R₆ - S₂ - S₃ + d[-a₁,₄ b₁,₂]`.  We use the definition-consistent
`representationSecondaryPreviousDefect` throughout.
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

/-- The fourth ordinary boundary, available uniformly from rank five on. -/
def lemma93FourthRepresentationIndex (N : Nat) :
    RepresentationIndex (N + 5) (N + 5) where
  val := 4
  pos := by omega
  lt_large := by omega
  le_small := by omega

/-- The fifth ordinary boundary, available uniformly from rank six on. -/
def lemma93FifthRepresentationIndex (N : Nat) :
    RepresentationIndex (N + 6) (N + 6) where
  val := 5
  pos := by omega
  lt_large := by omega
  le_small := by omega

/-- The order-theoretic conclusion for the shifted Case-2 claim.  These
three weak reverse inequalities negate the essentiality clauses at tail
indices `3,4,5` in the paper's one-based notation. -/
theorem tail_nextThree_not_essential_of_order_bounds
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hsix : 6 < N + 5)
    (hleft : a.order (⟨4, by omega⟩ : Fin (N + 5)) ≤
      b.order (⟨2, by omega⟩ : Fin (N + 5)))
    (hmiddle : a.order (⟨5, by omega⟩ : Fin (N + 5)) +
        a.order (⟨6, hsix⟩ : Fin (N + 5)) ≤
      b.order (⟨2, by omega⟩ : Fin (N + 5)) +
        b.order (⟨3, by omega⟩ : Fin (N + 5)))
    (hright : a.order (⟨6, hsix⟩ : Fin (N + 5)) ≤
      b.order (⟨4, by omega⟩ : Fin (N + 5))) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 4))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 4))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨4, by omega⟩ : Fin (N + 4))) := by
  constructor
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.1 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨2 - 1, by omega⟩ <
      a.tail.order ⟨2 + 1, by omega⟩ at hcross
    rw [b.order_goodTail, a.order_goodTail] at hcross
    have hcross' : b.order (⟨2, by omega⟩ : Fin (N + 5)) <
        a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hleft) hcross'
  constructor
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.2 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨3 - 2, by omega⟩ +
          b.tail.order ⟨3 - 1, by omega⟩ <
        a.tail.order ⟨3 + 1, by omega⟩ +
          a.tail.order ⟨3 + 2, by omega⟩ at hcross
    rw [b.order_goodTail, b.order_goodTail,
      a.order_goodTail, a.order_goodTail] at hcross
    have hcross' :
        b.order (⟨2, by omega⟩ : Fin (N + 5)) +
            b.order (⟨3, by omega⟩ : Fin (N + 5)) <
          a.order (⟨5, by omega⟩ : Fin (N + 5)) +
            a.order (⟨6, hsix⟩ : Fin (N + 5)) := by
      convert hcross using 1 <;> congr 2 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hmiddle) hcross'
  · intro hessential
    unfold IsEssentialFor BeliOrderSequence.IsEssentialFor at hessential
    have hcross := hessential.1 (by simp) (by
      simp only [Fin.val_mk]
      omega)
    change b.tail.order ⟨4 - 1, by omega⟩ <
      a.tail.order ⟨4 + 1, by omega⟩ at hcross
    rw [b.order_goodTail, a.order_goodTail] at hcross
    have hcross' : b.order (⟨4, by omega⟩ : Fin (N + 5)) <
        a.order (⟨6, hsix⟩ : Fin (N + 5)) := by
      convert hcross using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    exact (not_lt_of_ge hright) hcross'

/-- From `R₆>S₄` and `R₆+R₇<S₃+S₄`, goodness supplies the three order
bounds needed to show that tail indices `3,4,5` are nonessential. -/
theorem tail_nextThree_not_essential_of_sum_lt
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M (N + 5))
    (hsix : 6 < N + 5)
    (hcross : b.order (⟨3, by omega⟩ : Fin (N + 5)) <
      a.order (⟨5, by omega⟩ : Fin (N + 5)))
    (hsum : a.order (⟨5, by omega⟩ : Fin (N + 5)) +
        a.order (⟨6, hsix⟩ : Fin (N + 5)) <
      b.order (⟨2, by omega⟩ : Fin (N + 5)) +
        b.order (⟨3, by omega⟩ : Fin (N + 5))) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 4))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 4))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨4, by omega⟩ : Fin (N + 4))) := by
  have hsevenLtThird :
      a.order (⟨6, hsix⟩ : Fin (N + 5)) <
        b.order (⟨2, by omega⟩ : Fin (N + 5)) := by
    omega
  have htargetGoodRaw :=
    a.good (⟨4, by omega⟩ : Fin (N + 5)) (by omega)
  have htargetGood :
      a.order (⟨4, by omega⟩ : Fin (N + 5)) ≤
        a.order (⟨6, hsix⟩ : Fin (N + 5)) := by
    convert htargetGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  have hsourceGoodRaw :=
    b.good (⟨2, by omega⟩ : Fin (N + 5)) (by
      change 2 + 2 < N + 5
      omega)
  have hsourceGood :
      b.order (⟨2, by omega⟩ : Fin (N + 5)) ≤
        b.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    convert hsourceGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
  exact tail_nextThree_not_essential_of_order_bounds a b hsix
    (htargetGood.trans hsevenLtThird.le) hsum.le
    (hsevenLtThird.le.trans hsourceGood)

set_option maxHeartbeats 800000 in
/-- The first three-index claim in Case 2.  If the third invariant is
strictly below its primary candidate, `R₅>S₃`, and the fourth invariant is
the previous-form secondary candidate, then tail indices `2,3,4` are all
nonessential.

The proof follows the two candidates left for `A₃` after Lemma 2.7(ii).
The half-gap candidate contradicts the standard target half-gap upper bound
for `A₄`; the secondary-current candidate forces
`R₅+R₆<S₂+S₃`, after which goodness gives the three failed essentiality
inequalities. -/
theorem tail_lowThree_not_essential_of_thirdPrimaryStrict_fourthPrevious
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 6)) (b : GoodBONG r M (N + 6))
    (hcross : b.order (⟨2, by omega⟩ : Fin (N + 6)) <
      a.order (⟨4, by omega⟩ : Fin (N + 6)))
    (hthirdStrict :
      a.representationAlpha b (lemma93ThirdRepresentationIndex (N + 2)) <
        a.representationPrimaryDefect b
          (lemma93ThirdRepresentationIndex (N + 2)))
    (hfourthEq :
      a.representationAlpha b (lemma93FourthRepresentationIndex (N + 1)) =
        a.representationSecondaryPreviousDefect b
          (lemma93FourthRepresentationIndex (N + 1)) (by
            simp only [lemma93FourthRepresentationIndex]
            omega)) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨1, by omega⟩ : Fin (N + 5))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 5))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 5))) := by
  let third : RepresentationIndex (N + 6) (N + 6) :=
    lemma93ThirdRepresentationIndex (N + 2)
  let fourth : RepresentationIndex (N + 6) (N + 6) :=
    lemma93FourthRepresentationIndex (N + 1)
  have hiThird : 1 < third.val ∧ third.val + 1 < N + 6 := by
    simp only [third, lemma93ThirdRepresentationIndex]
    omega
  have hiFourth : 1 < fourth.val ∧ fourth.val + 1 < N + 6 := by
    simp only [fourth, lemma93FourthRepresentationIndex]
    omega
  have hthirdStrict' : a.representationAlpha b third <
      a.representationPrimaryDefect b third := by
    simpa only [third] using hthirdStrict
  have hfourthEq' : a.representationAlpha b fourth =
      a.representationSecondaryPreviousDefect b fourth hiFourth := by
    simpa only [fourth] using hfourthEq
  have hcrossThird :
      b.order ⟨third.val - 1, by have := third.le_small; omega⟩ ≤
        a.order ⟨third.val + 1, hiThird.2⟩ := by
    simpa only [third, lemma93ThirdRepresentationIndex] using hcross.le
  have hnormal : a.representationAlpha b third =
      min (a.representationHalfGap b third)
        (min (a.representationPrimaryDefect b third)
          (a.representationSecondaryCurrentDefect b third hiThird)) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    rw [a.representationAlpha_eq_min_halfGap_prime b third,
      a.representationAlphaPrime_eq_min_primary_current b third hiThird
        hcrossThird]
  have hchoice :
      a.representationAlpha b third = a.representationHalfGap b third ∨
        a.representationAlpha b third =
          a.representationSecondaryCurrentDefect b third hiThird := by
    rcases min_choice (a.representationHalfGap b third)
        (min (a.representationPrimaryDefect b third)
          (a.representationSecondaryCurrentDefect b third hiThird)) with
      hhalf | hprime
    · exact Or.inl (hnormal.trans hhalf)
    · rcases min_choice (a.representationPrimaryDefect b third)
          (a.representationSecondaryCurrentDefect b third hiThird) with
        hprimary | hsecondary
      · have heq := hnormal.trans (hprime.trans hprimary)
        exact False.elim ((ne_of_lt hthirdStrict') heq)
      · exact Or.inr (hnormal.trans (hprime.trans hsecondary))
  let D : WithTop ℚ := a.truncatedPrefixDefect b (-1) 4 2
  have hDcap : D ≤ a.prefixAlphaCap 4 := by
    exact a.truncatedPrefixDefect_le_leftCap b (-1) 4 2
  have hDcapNe : a.prefixAlphaCap 4 ≠ ⊤ := by
    rw [a.prefixAlphaCap_of_internal (i := 4) (by omega) (by omega)]
    exact WithTop.coe_ne_top
  have hDne : D ≠ ⊤ := ne_top_of_le_ne_top hDcapNe hDcap
  let d : ℚ := D.untop hDne
  have hd : (d : WithTop ℚ) = D := WithTop.coe_untop D hDne
  rcases hchoice with hhalf | hsecondary
  · have hhalfPrimary : a.representationHalfGap b third <
        a.representationPrimaryDefect b third := by
      rw [← hhalf]
      exact hthirdStrict'
    have hhalfPrimary' := hhalfPrimary
    unfold representationHalfGap representationPrimaryDefect at hhalfPrimary'
    simp only [third, lemma93ThirdRepresentationIndex] at hhalfPrimary'
    change
      (((((a.order (⟨3, by omega⟩ : Fin (N + 6)) -
        b.order (⟨2, by omega⟩ : Fin (N + 6)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
        ((((a.order (⟨3, by omega⟩ : Fin (N + 6)) -
          b.order (⟨2, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + D)) at hhalfPrimary'
    rw [← hd, ← WithTop.coe_add] at hhalfPrimary'
    have hhalfPrimaryQ := WithTop.coe_lt_coe.mp hhalfPrimary'
    have hdefectLower :
        ((b.order (⟨2, by omega⟩ : Fin (N + 6)) -
          a.order (⟨3, by omega⟩ : Fin (N + 6)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ) < d := by
      push_cast at hhalfPrimaryQ ⊢
      linarith
    have hfourthUpper : a.representationAlpha b fourth ≤
        (((a.order ⟨fourth.val, fourth.lt_large⟩ -
          b.order ⟨fourth.val - 1, by have := fourth.le_small; omega⟩ :
            Int) : ℚ) : WithTop ℚ) +
          (a.halfGapValue ⟨fourth.val, by omega⟩ : WithTop ℚ) := by
      apply (a.representationAlpha_le_prime b fourth).trans
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.representationAlphaPrime_le_primaryLeftHalfGap b fourth
        hiFourth.2
    rw [hfourthEq'] at hfourthUpper
    unfold representationSecondaryPreviousDefect halfGapValue orderGap at hfourthUpper
    simp only [fourth, lemma93FourthRepresentationIndex] at hfourthUpper
    change
      (((((a.order (⟨4, by omega⟩ : Fin (N + 6)) +
          a.order (⟨5, by omega⟩ : Fin (N + 6)) -
          b.order (⟨2, by omega⟩ : Fin (N + 6)) -
          b.order (⟨3, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + D) ≤
        ((((a.order (⟨4, by omega⟩ : Fin (N + 6)) -
          b.order (⟨3, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) +
          (((((a.order (⟨5, by omega⟩ : Fin (N + 6)) -
            a.order (⟨4, by omega⟩ : Fin (N + 6)) : Int) : ℚ) / 2 +
              (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ))) at hfourthUpper
    rw [← hd, ← WithTop.coe_add, ← WithTop.coe_add] at hfourthUpper
    have hfourthUpperQ := WithTop.coe_le_coe.mp hfourthUpper
    have htargetGoodRaw :=
      a.good (⟨3, by omega⟩ : Fin (N + 6)) (by
        change 3 + 2 < N + 6
        omega)
    have htargetGood :
        a.order (⟨3, by omega⟩ : Fin (N + 6)) ≤
          a.order (⟨5, by omega⟩ : Fin (N + 6)) := by
      convert htargetGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    have hcrossQ :
        (b.order (⟨2, by omega⟩ : Fin (N + 6)) : ℚ) <
          (a.order (⟨4, by omega⟩ : Fin (N + 6)) : ℚ) := by
      exact_mod_cast hcross
    have htargetGoodQ :
        (a.order (⟨3, by omega⟩ : Fin (N + 6)) : ℚ) ≤
          (a.order (⟨5, by omega⟩ : Fin (N + 6)) : ℚ) := by
      exact_mod_cast htargetGood
    push_cast at hfourthUpperQ hdefectLower
    exfalso
    linarith
  · let E : WithTop ℚ := a.truncatedPrefixDefect b (-1) 5 3
    have hEcap : E ≤ a.prefixAlphaCap 5 := by
      exact a.truncatedPrefixDefect_le_leftCap b (-1) 5 3
    have hEcapNe : a.prefixAlphaCap 5 ≠ ⊤ := by
      rw [a.prefixAlphaCap_of_internal (i := 5) (by omega) (by omega)]
      exact WithTop.coe_ne_top
    have hEne : E ≠ ⊤ := ne_top_of_le_ne_top hEcapNe hEcap
    let eDefect : ℚ := E.untop hEne
    have he : (eDefect : WithTop ℚ) = E := WithTop.coe_untop E hEne
    have hsecondaryPrimary :
        a.representationSecondaryCurrentDefect b third hiThird <
          a.representationPrimaryDefect b third := by
      rw [← hsecondary]
      exact hthirdStrict'
    unfold representationSecondaryCurrentDefect representationPrimaryDefect at hsecondaryPrimary
    simp only [third, lemma93ThirdRepresentationIndex] at hsecondaryPrimary
    change
      (((((a.order (⟨3, by omega⟩ : Fin (N + 6)) +
          a.order (⟨4, by omega⟩ : Fin (N + 6)) -
          b.order (⟨1, by omega⟩ : Fin (N + 6)) -
          b.order (⟨2, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + E) <
        ((((a.order (⟨3, by omega⟩ : Fin (N + 6)) -
          b.order (⟨2, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + D)) at hsecondaryPrimary
    rw [← he, ← hd, ← WithTop.coe_add, ← WithTop.coe_add] at hsecondaryPrimary
    have hsecondaryPrimaryQ := WithTop.coe_lt_coe.mp hsecondaryPrimary
    have hfirstDefect :
        ((a.order (⟨4, by omega⟩ : Fin (N + 6)) -
          b.order (⟨1, by omega⟩ : Fin (N + 6)) : Int) : ℚ) + eDefect < d := by
      push_cast at hsecondaryPrimaryQ ⊢
      linarith
    have hfourthPrimary := a.representationAlpha_le_primary b fourth
    rw [hfourthEq'] at hfourthPrimary
    unfold representationSecondaryPreviousDefect representationPrimaryDefect at hfourthPrimary
    simp only [fourth, lemma93FourthRepresentationIndex] at hfourthPrimary
    change
      (((((a.order (⟨4, by omega⟩ : Fin (N + 6)) +
          a.order (⟨5, by omega⟩ : Fin (N + 6)) -
          b.order (⟨2, by omega⟩ : Fin (N + 6)) -
          b.order (⟨3, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + D) ≤
        ((((a.order (⟨4, by omega⟩ : Fin (N + 6)) -
          b.order (⟨3, by omega⟩ : Fin (N + 6)) : Int) : ℚ) :
            WithTop ℚ) + E)) at hfourthPrimary
    rw [← hd, ← he, ← WithTop.coe_add, ← WithTop.coe_add] at hfourthPrimary
    have hfourthPrimaryQ := WithTop.coe_le_coe.mp hfourthPrimary
    have hsumQ :
        (a.order (⟨4, by omega⟩ : Fin (N + 6)) : ℚ) +
            (a.order (⟨5, by omega⟩ : Fin (N + 6)) : ℚ) <
          (b.order (⟨1, by omega⟩ : Fin (N + 6)) : ℚ) +
            (b.order (⟨2, by omega⟩ : Fin (N + 6)) : ℚ) := by
      push_cast at hfirstDefect hfourthPrimaryQ
      linarith
    have hsum :
        a.order (⟨4, by omega⟩ : Fin (N + 6)) +
            a.order (⟨5, by omega⟩ : Fin (N + 6)) <
          b.order (⟨1, by omega⟩ : Fin (N + 6)) +
            b.order (⟨2, by omega⟩ : Fin (N + 6)) := by
      exact_mod_cast hsumQ
    exact tail_lowThree_not_essential_of_sum_lt
      (N := N + 2) a b (by omega) hcross hsum

set_option maxHeartbeats 800000 in
/-- The shifted three-index claim in Case 2.  If the fourth invariant is
strictly below its primary candidate, `R₆>S₄`, and the fifth invariant is
the previous-form secondary candidate, then tail indices `3,4,5` are all
nonessential.

This is the fully expanded proof of the paper's word “Similarly”.  As in
the preceding claim, the v2 displayed formula has a shifted-source typo:
Definition 4 gives `R₆+R₇-S₄-S₅+d[-a₁,₅b₁,₃]`; the proof below uses that
definition-consistent candidate. -/
theorem tail_nextThree_not_essential_of_fourthPrimaryStrict_fifthPrevious
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 7)) (b : GoodBONG r M (N + 7))
    (hcross : b.order (⟨3, by omega⟩ : Fin (N + 7)) <
      a.order (⟨5, by omega⟩ : Fin (N + 7)))
    (hfourthStrict :
      a.representationAlpha b (lemma93FourthRepresentationIndex (N + 2)) <
        a.representationPrimaryDefect b
          (lemma93FourthRepresentationIndex (N + 2)))
    (hfifthEq :
      a.representationAlpha b (lemma93FifthRepresentationIndex (N + 1)) =
        a.representationSecondaryPreviousDefect b
          (lemma93FifthRepresentationIndex (N + 1)) (by
            simp only [lemma93FifthRepresentationIndex]
            omega)) :
    (¬a.tail.IsEssentialFor b.tail
        (⟨2, by omega⟩ : Fin (N + 6))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨3, by omega⟩ : Fin (N + 6))) ∧
      (¬a.tail.IsEssentialFor b.tail
        (⟨4, by omega⟩ : Fin (N + 6))) := by
  let fourth : RepresentationIndex (N + 7) (N + 7) :=
    lemma93FourthRepresentationIndex (N + 2)
  let fifth : RepresentationIndex (N + 7) (N + 7) :=
    lemma93FifthRepresentationIndex (N + 1)
  have hiFourth : 1 < fourth.val ∧ fourth.val + 1 < N + 7 := by
    simp only [fourth, lemma93FourthRepresentationIndex]
    omega
  have hiFifth : 1 < fifth.val ∧ fifth.val + 1 < N + 7 := by
    simp only [fifth, lemma93FifthRepresentationIndex]
    omega
  have hfourthStrict' : a.representationAlpha b fourth <
      a.representationPrimaryDefect b fourth := by
    simpa only [fourth] using hfourthStrict
  have hfifthEq' : a.representationAlpha b fifth =
      a.representationSecondaryPreviousDefect b fifth hiFifth := by
    simpa only [fifth] using hfifthEq
  have hcrossFourth :
      b.order ⟨fourth.val - 1, by have := fourth.le_small; omega⟩ ≤
        a.order ⟨fourth.val + 1, hiFourth.2⟩ := by
    simpa only [fourth, lemma93FourthRepresentationIndex] using hcross.le
  have hnormal : a.representationAlpha b fourth =
      min (a.representationHalfGap b fourth)
        (min (a.representationPrimaryDefect b fourth)
          (a.representationSecondaryCurrentDefect b fourth hiFourth)) := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    rw [a.representationAlpha_eq_min_halfGap_prime b fourth,
      a.representationAlphaPrime_eq_min_primary_current b fourth hiFourth
        hcrossFourth]
  have hchoice :
      a.representationAlpha b fourth = a.representationHalfGap b fourth ∨
        a.representationAlpha b fourth =
          a.representationSecondaryCurrentDefect b fourth hiFourth := by
    rcases min_choice (a.representationHalfGap b fourth)
        (min (a.representationPrimaryDefect b fourth)
          (a.representationSecondaryCurrentDefect b fourth hiFourth)) with
      hhalf | hprime
    · exact Or.inl (hnormal.trans hhalf)
    · rcases min_choice (a.representationPrimaryDefect b fourth)
          (a.representationSecondaryCurrentDefect b fourth hiFourth) with
        hprimary | hsecondary
      · have heq := hnormal.trans (hprime.trans hprimary)
        exact False.elim ((ne_of_lt hfourthStrict') heq)
      · exact Or.inr (hnormal.trans (hprime.trans hsecondary))
  let D : WithTop ℚ := a.truncatedPrefixDefect b (-1) 5 3
  have hDcap : D ≤ a.prefixAlphaCap 5 := by
    exact a.truncatedPrefixDefect_le_leftCap b (-1) 5 3
  have hDcapNe : a.prefixAlphaCap 5 ≠ ⊤ := by
    rw [a.prefixAlphaCap_of_internal (i := 5) (by omega) (by omega)]
    exact WithTop.coe_ne_top
  have hDne : D ≠ ⊤ := ne_top_of_le_ne_top hDcapNe hDcap
  let d : ℚ := D.untop hDne
  have hd : (d : WithTop ℚ) = D := WithTop.coe_untop D hDne
  rcases hchoice with hhalf | hsecondary
  · have hhalfPrimary : a.representationHalfGap b fourth <
        a.representationPrimaryDefect b fourth := by
      rw [← hhalf]
      exact hfourthStrict'
    have hhalfPrimary' := hhalfPrimary
    unfold representationHalfGap representationPrimaryDefect at hhalfPrimary'
    simp only [fourth, lemma93FourthRepresentationIndex] at hhalfPrimary'
    change
      (((((a.order (⟨4, by omega⟩ : Fin (N + 7)) -
        b.order (⟨3, by omega⟩ : Fin (N + 7)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
        ((((a.order (⟨4, by omega⟩ : Fin (N + 7)) -
          b.order (⟨3, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + D)) at hhalfPrimary'
    rw [← hd, ← WithTop.coe_add] at hhalfPrimary'
    have hhalfPrimaryQ := WithTop.coe_lt_coe.mp hhalfPrimary'
    have hdefectLower :
        ((b.order (⟨3, by omega⟩ : Fin (N + 7)) -
          a.order (⟨4, by omega⟩ : Fin (N + 7)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ) < d := by
      push_cast at hhalfPrimaryQ ⊢
      linarith
    have hfifthUpper : a.representationAlpha b fifth ≤
        (((a.order ⟨fifth.val, fifth.lt_large⟩ -
          b.order ⟨fifth.val - 1, by have := fifth.le_small; omega⟩ :
            Int) : ℚ) : WithTop ℚ) +
          (a.halfGapValue ⟨fifth.val, by omega⟩ : WithTop ℚ) := by
      apply (a.representationAlpha_le_prime b fifth).trans
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.representationAlphaPrime_le_primaryLeftHalfGap b fifth
        hiFifth.2
    rw [hfifthEq'] at hfifthUpper
    unfold representationSecondaryPreviousDefect halfGapValue orderGap at hfifthUpper
    simp only [fifth, lemma93FifthRepresentationIndex] at hfifthUpper
    change
      (((((a.order (⟨5, by omega⟩ : Fin (N + 7)) +
          a.order (⟨6, by omega⟩ : Fin (N + 7)) -
          b.order (⟨3, by omega⟩ : Fin (N + 7)) -
          b.order (⟨4, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + D) ≤
        ((((a.order (⟨5, by omega⟩ : Fin (N + 7)) -
          b.order (⟨4, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) +
          (((((a.order (⟨6, by omega⟩ : Fin (N + 7)) -
            a.order (⟨5, by omega⟩ : Fin (N + 7)) : Int) : ℚ) / 2 +
              (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ))) at hfifthUpper
    rw [← hd, ← WithTop.coe_add, ← WithTop.coe_add] at hfifthUpper
    have hfifthUpperQ := WithTop.coe_le_coe.mp hfifthUpper
    have htargetGoodRaw :=
      a.good (⟨4, by omega⟩ : Fin (N + 7)) (by
        change 4 + 2 < N + 7
        omega)
    have htargetGood :
        a.order (⟨4, by omega⟩ : Fin (N + 7)) ≤
          a.order (⟨6, by omega⟩ : Fin (N + 7)) := by
      convert htargetGoodRaw using 1 <;> congr 1 <;> apply Fin.ext <;> simp
    have hcrossQ :
        (b.order (⟨3, by omega⟩ : Fin (N + 7)) : ℚ) <
          (a.order (⟨5, by omega⟩ : Fin (N + 7)) : ℚ) := by
      exact_mod_cast hcross
    have htargetGoodQ :
        (a.order (⟨4, by omega⟩ : Fin (N + 7)) : ℚ) ≤
          (a.order (⟨6, by omega⟩ : Fin (N + 7)) : ℚ) := by
      exact_mod_cast htargetGood
    push_cast at hfifthUpperQ hdefectLower
    exfalso
    linarith
  · let E : WithTop ℚ := a.truncatedPrefixDefect b (-1) 6 4
    have hEcap : E ≤ a.prefixAlphaCap 6 := by
      exact a.truncatedPrefixDefect_le_leftCap b (-1) 6 4
    have hEcapNe : a.prefixAlphaCap 6 ≠ ⊤ := by
      rw [a.prefixAlphaCap_of_internal (i := 6) (by omega) (by omega)]
      exact WithTop.coe_ne_top
    have hEne : E ≠ ⊤ := ne_top_of_le_ne_top hEcapNe hEcap
    let eDefect : ℚ := E.untop hEne
    have he : (eDefect : WithTop ℚ) = E := WithTop.coe_untop E hEne
    have hsecondaryPrimary :
        a.representationSecondaryCurrentDefect b fourth hiFourth <
          a.representationPrimaryDefect b fourth := by
      rw [← hsecondary]
      exact hfourthStrict'
    unfold representationSecondaryCurrentDefect representationPrimaryDefect at hsecondaryPrimary
    simp only [fourth, lemma93FourthRepresentationIndex] at hsecondaryPrimary
    change
      (((((a.order (⟨4, by omega⟩ : Fin (N + 7)) +
          a.order (⟨5, by omega⟩ : Fin (N + 7)) -
          b.order (⟨2, by omega⟩ : Fin (N + 7)) -
          b.order (⟨3, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + E) <
        ((((a.order (⟨4, by omega⟩ : Fin (N + 7)) -
          b.order (⟨3, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + D)) at hsecondaryPrimary
    rw [← he, ← hd, ← WithTop.coe_add, ← WithTop.coe_add] at hsecondaryPrimary
    have hsecondaryPrimaryQ := WithTop.coe_lt_coe.mp hsecondaryPrimary
    have hfirstDefect :
        ((a.order (⟨5, by omega⟩ : Fin (N + 7)) -
          b.order (⟨2, by omega⟩ : Fin (N + 7)) : Int) : ℚ) + eDefect < d := by
      push_cast at hsecondaryPrimaryQ ⊢
      linarith
    have hfifthPrimary := a.representationAlpha_le_primary b fifth
    rw [hfifthEq'] at hfifthPrimary
    unfold representationSecondaryPreviousDefect representationPrimaryDefect at hfifthPrimary
    simp only [fifth, lemma93FifthRepresentationIndex] at hfifthPrimary
    change
      (((((a.order (⟨5, by omega⟩ : Fin (N + 7)) +
          a.order (⟨6, by omega⟩ : Fin (N + 7)) -
          b.order (⟨3, by omega⟩ : Fin (N + 7)) -
          b.order (⟨4, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + D) ≤
        ((((a.order (⟨5, by omega⟩ : Fin (N + 7)) -
          b.order (⟨4, by omega⟩ : Fin (N + 7)) : Int) : ℚ) :
            WithTop ℚ) + E)) at hfifthPrimary
    rw [← hd, ← he, ← WithTop.coe_add, ← WithTop.coe_add] at hfifthPrimary
    have hfifthPrimaryQ := WithTop.coe_le_coe.mp hfifthPrimary
    have hsumQ :
        (a.order (⟨5, by omega⟩ : Fin (N + 7)) : ℚ) +
            (a.order (⟨6, by omega⟩ : Fin (N + 7)) : ℚ) <
          (b.order (⟨2, by omega⟩ : Fin (N + 7)) : ℚ) +
            (b.order (⟨3, by omega⟩ : Fin (N + 7)) : ℚ) := by
      push_cast at hfirstDefect hfifthPrimaryQ
      linarith
    have hsum :
        a.order (⟨5, by omega⟩ : Fin (N + 7)) +
            a.order (⟨6, by omega⟩ : Fin (N + 7)) <
          b.order (⟨2, by omega⟩ : Fin (N + 7)) +
            b.order (⟨3, by omega⟩ : Fin (N + 7)) := by
      exact_mod_cast hsumQ
    exact tail_nextThree_not_essential_of_sum_lt
      (N := N + 2) a b (by omega) hcross hsum

end BONG.GoodBONG

end Bong
