/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralProfiles

/-!
# Beli (2019), Section 4: the asymmetric central cases

This file closes cases (b) and (c) in the proof of Theorem 2.1(iii), where
exactly one of the two adjacent representation alphas attains its primed
value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- If `B_(i-1) < B'_(i-1)`, Lemma 2.14 gives the left boundary used in
Lemma 4.2(i); at `i=2` this boundary is vacuous. -/
theorem sectionFourLeftBoundary_of_previous_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    (∃ hiPrev : 2 < i.val,
      c.order ⟨i.val - 3, by have := i.lt_large; omega⟩ <
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩) ∨
      i.val = 2 := by
  by_cases hi : i.val = 2
  · exact Or.inr hi
  · apply Or.inl
    have hiPrev : 2 < i.val := by
      have := i.one_lt
      omega
    refine ⟨hiPrev, ?_⟩
    have hhalf :=
      (b.representationAlpha_eq_halfGap_and_lt_prime_of_ne
        c i.previous hneBC).2
    have hcross := b.sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
      c i.previous (by
        change 1 < i.val - 1
        omega) hhalf
    simpa only [CentralRepresentationIndex.previous, Nat.sub_sub,
      one_add_one_eq_two] using hcross

/-- Case (b): `A_i=A'_i` and `B_(i-1)<B'_(i-1)`.  The two possible
Lemma 1.5 Hilbert sums cannot both be at most `2e`. -/
theorem sectionFourCentralCertificate_of_current_eq_previous_ne
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (heqAB : a.representationAlpha b (i.current i.lt_large.le) =
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have hleftBoundary := b.sectionFourLeftBoundary_of_previous_alpha_ne_prime
    c i hneBC
  have hleft := a.sectionFourLeftDirectTrigger_of_boundary
    b c i htrigger hleftBoundary
  have hcomparison := a.sectionFourForwardComparison_of_current_eq_prime
    b c hab hbc i htrigger heqAB
  have hforwardPrime :=
    a.sectionFourForwardFirst_of_current_eq_previous_ne
      b c hbc i htrigger.1 heqAB hneBC hcomparison
  have hforward :
      (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha c (i.current i.lt_large.le) ≤
        (((b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le) := by
    simpa only [heqAB] using hforwardPrime
  have htriggerAB := a.sectionFour_middleCentralTrigger_of_leftDirect
    b c hlocal i htrigger hleft hforward
  have hmiddle := hab.centralRepresentations i htriggerAB
  have hsourceCurrent :=
    b.sourceCurrent_represents_of_previous_alpha_ne_prime c hbc i hneBC
  have hsourcePrevious :=
    b.sourcePrevious_represents_of_previous_alpha_ne_prime c hbc i hneBC
  let defectAB := a.truncatedPrefixDefect b 1 i.val i.val
  let defectBC := b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)
  by_cases hcaseI :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectAB + defectBC
  · exact CentralRepresentationCertificate.of_caseI_truncatedDefects
      hmiddle hsourceCurrent (by
        simpa only [defectAB, defectBC] using hcaseI)
  · apply CentralRepresentationCertificate.of_caseIII_truncatedDefects
      hmiddle hsourcePrevious
    by_contra hnotCaseIII
    have hleI : defectAB + defectBC ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
      le_of_not_gt hcaseI
    have hleIII : defectBC + a.centralPreviousDefect c i ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
      le_of_not_gt hnotCaseIII
    have habBound := hab.defectCondition (i.current i.lt_large.le)
    have hbcBound := hbc.defectCondition i.previous
    rw [a.coe_representationAlphaValue b
      (i.current i.lt_large.le)] at habBound
    rw [b.coe_representationAlphaValue c i.previous] at hbcBound
    have halphaI :
        a.representationAlpha b (i.current i.lt_large.le) +
            b.representationAlpha c i.previous ≤
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      apply (add_le_add habBound hbcBound).trans
      simpa only [defectAB, defectBC, CentralRepresentationIndex.current,
        CentralRepresentationIndex.previous, one_mul] using hleI
    have hpreviousDefect :=
      a.sectionFourLemma45_shiftedPreviousAlpha_le_previousDefect c i
    have halphaIII :
        b.representationAlpha c i.previous +
            ((((c.order ⟨i.val - 2, by have := i.lt_large; omega⟩ -
                a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
                  WithTop ℚ) + a.representationAlpha c i.previous) ≤
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      apply (add_le_add hbcBound hpreviousDefect).trans
      simpa only [defectBC, CentralRepresentationIndex.previous, one_mul]
        using hleIII
    have hhalf :=
      (b.representationAlpha_eq_halfGap_and_lt_prime_of_ne
        c i.previous hneBC).1
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous] at halphaI
    rw [← b.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue c i.previous] at halphaIII
    rw [← a.coe_representationAlphaValue c
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue b
        (i.current i.lt_large.le)] at hforward
    rw [← b.coe_representationAlphaValue c i.previous] at hhalf
    unfold representationHalfGap at hhalf
    simp only [CentralRepresentationIndex.previous, Nat.sub_sub,
      one_add_one_eq_two] at hhalf
    norm_cast at halphaI halphaIII hforward hhalf hsum
    simp only [Rat.divInt_eq_div] at hhalf
    push_cast at halphaI halphaIII hforward hhalf hsum
    norm_num [div_eq_mul_inv] at hhalf
    simp only [CentralRepresentationIndex.previous] at halphaI halphaIII hsum
    linarith

/-- If `A_i < A'_i`, Lemma 2.14 gives the right boundary used in Lemma
4.2(ii); at the final boundary the alternative is vacuous. -/
theorem sectionFourRightBoundary_of_current_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le)) :
    (∃ hiNext : i.val + 1 < n + 1,
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
        a.order ⟨i.val + 1, hiNext⟩) ∨
      i.val + 1 = n + 1 := by
  by_cases hi : i.val + 1 = n + 1
  · exact Or.inr hi
  · have hiNext : i.val + 1 < n + 1 := by
      have := i.lt_large
      omega
    apply Or.inl
    refine ⟨hiNext, ?_⟩
    have hhalf :=
      (a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
        b (i.current i.lt_large.le) hneAB).2
    exact a.sourceNext_gt_targetCurrent_of_halfGap_lt_alphaPrime
      b (i.current i.lt_large.le) hiNext hhalf

/-- Lemma 2.14 also activates condition (iii) one boundary to the right.
At the final boundary this is the full BONG coordinate change. -/
theorem middleCurrent_represents_of_current_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le)) :
    DiagonalRepresents
      (b.prefixValues i.val i.current_le_sameRank)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  by_cases hiNext : i.val + 1 < n + 1
  · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
      { val := i.val + 1
        one_lt := by have := i.one_lt; omega
        lt_large := hiNext
        le_small_succ := by omega }
    have hne' : a.representationAlpha b j.previous ≠
        a.representationAlphaPrime b j.previous := by
      simpa only [j, CentralRepresentationIndex.previous,
        CentralRepresentationIndex.current, Nat.add_sub_cancel] using hneAB
    have htrigger := a.centralAlphaTrigger_of_previous_alpha_ne_prime
      b le_rfl hab.orderCondition hab.defectCondition j j.lt_large.le hne'
    have hrep := hab.centralRepresentations j htrigger
    exact prefixRepresents_cast b a (by
      dsimp only [j]
      omega) rfl hrep
  · have hend : i.val + 1 = n + 1 := by
      have := i.lt_large
      omega
    have hprefix := b.prefixValues_represents_of_le
      i.val (n + 1) (by omega) le_rfl
    have hfull := b.fullPrefix_represents a
    exact prefixRepresents_cast b a rfl hend.symm (hprefix.trans hfull)

/-- Case (c): `A_i<A'_i` and `B_(i-1)=B'_(i-1)`.  This is the direct
counterpart of the paper's duality argument. -/
theorem sectionFourCentralCertificate_of_current_ne_previous_eq
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (heqBC : b.representationAlpha c i.previous =
      b.representationAlphaPrime c i.previous) :
    CentralRepresentationCertificate a b c i := by
  let hlocal := SectionFourLocalConditions.ofRepresentationConditions
    a b c hab hbc
  have hrightBoundary := a.sectionFourRightBoundary_of_current_alpha_ne_prime
    b i hneAB
  have hright := a.sectionFourRightDirectTrigger_of_boundary
    b c i htrigger hrightBoundary
  have hcrossBC := a.sectionFour_middleNext_gt_sourcePrevious_of_rightDirect
    b c hab.orderCondition i htrigger hright
  have hcomparison := a.sectionFourBackwardComparison_of_previous_eq_prime
    b c hab hbc i htrigger heqBC
  have hbackwardPrime :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlphaPrime c i.previous := by
    rcases hcomparison with hfirst | hsecond | hthird
    · exact hfirst
    · exact (a.sectionFourBackwardSecond_impossible b c i htrigger.1
        hneAB heqBC hsecond).elim
    · exact (not_lt_of_ge hcrossBC.le hthird).elim
  have hbackward :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
            ℚ) : WithTop ℚ) + b.representationAlpha c i.previous := by
    simpa only [heqBC] using hbackwardPrime
  have htriggerBC := a.sectionFour_sourceCentralTrigger_of_rightDirect
    b c hlocal i htrigger hright hbackward
  have hmiddlePrevious :=
    a.middlePrevious_represents_of_current_alpha_ne_prime b hab i hneAB
  have hmiddleCurrent :=
    a.middleCurrent_represents_of_current_alpha_ne_prime b hab i hneAB
  have hsource := hbc.centralRepresentations i htriggerBC
  let defectAB := a.truncatedPrefixDefect b 1 i.val i.val
  let defectBC := b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)
  by_cases hcaseI :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectAB + defectBC
  · exact CentralRepresentationCertificate.of_caseI_truncatedDefects
      hmiddlePrevious hsource (by
        simpa only [defectAB, defectBC] using hcaseI)
  · apply CentralRepresentationCertificate.of_caseII_truncatedDefects
      hmiddleCurrent hsource
    by_contra hnotCaseII
    have hleI : defectAB + defectBC ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
      le_of_not_gt hcaseI
    have hleII : defectAB + a.centralCurrentDefect c i ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
      le_of_not_gt hnotCaseII
    have habBound := hab.defectCondition (i.current i.lt_large.le)
    have hbcBound := hbc.defectCondition i.previous
    rw [a.coe_representationAlphaValue b
      (i.current i.lt_large.le)] at habBound
    rw [b.coe_representationAlphaValue c i.previous] at hbcBound
    have halphaI :
        a.representationAlpha b (i.current i.lt_large.le) +
            b.representationAlpha c i.previous ≤
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      apply (add_le_add habBound hbcBound).trans
      simpa only [defectAB, defectBC, CentralRepresentationIndex.current,
        CentralRepresentationIndex.previous, one_mul] using hleI
    have hcurrentDefect :=
      a.sectionFourLemma45_shiftedCurrentAlpha_le_currentDefect c i
    have halphaII :
        a.representationAlpha b (i.current i.lt_large.le) +
            ((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
                a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
              a.representationAlpha c (i.current i.lt_large.le)) ≤
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      apply (add_le_add habBound hcurrentDefect).trans
      simpa only [defectAB, CentralRepresentationIndex.current, one_mul]
        using hleII
    have hhalf :=
      (a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
        b (i.current i.lt_large.le) hneAB).1
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos i.lt_large.le] at hsum
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← b.coe_representationAlphaValue c i.previous] at halphaI
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue c
        (i.current i.lt_large.le)] at halphaII
    rw [← a.coe_representationAlphaValue c i.previous,
      ← b.coe_representationAlphaValue c i.previous] at hbackward
    rw [← a.coe_representationAlphaValue b
      (i.current i.lt_large.le)] at hhalf
    unfold representationHalfGap at hhalf
    simp only [CentralRepresentationIndex.current] at hhalf
    norm_cast at halphaI halphaII hbackward hhalf hsum
    simp only [Rat.divInt_eq_div] at hhalf
    push_cast at halphaI halphaII hbackward hhalf hsum
    norm_num [div_eq_mul_inv] at hhalf
    simp only [CentralRepresentationIndex.current,
      CentralRepresentationIndex.previous] at halphaI halphaII hbackward hsum
    linarith

end BONG.GoodBONG

end Bong
