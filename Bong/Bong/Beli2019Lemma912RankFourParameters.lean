/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912LowBranches
import Bong.Bong.Beli2019Lemma912Lemma99Conditions
import Bong.Bong.Beli2019Lemma814HigherRankUnequal

/-!
# Beli (2019), Lemma 9.12: quaternary parameter arithmetic

This file supplies the one positive-tail endpoint omitted by the original
rank-at-least-five implementation.  All statements are literal rank-four
versions of the five-way parameter split and of the numerical input needed
by Lemma 9.10; no fifth coefficient is introduced.
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
  {L : Lattice K V} {M : Lattice K W}

/-- The five alternatives of Lemma 9.12 at literal quaternary rank. -/
inductive Beli2019Lemma912ParameterBranchRankFour
    (a : GoodBONG q L 4) (c : GoodBONG r M 4) : Prop
  | equalSecondLarge
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin 3) =
        c.alphaValue (0 : Fin 3))
      (secondAlpha_large : 1 < a.alphaValue (1 : Fin 3))
  | equalSecondOne
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin 3) =
        c.alphaValue (0 : Fin 3))
      (secondAlpha_eq_one : a.alphaValue (1 : Fin 3) = 1)
  | strictBelowHalfGap
      (fullDefect_strict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_below_halfGap : a.alphaValue (0 : Fin 3) <
        a.halfGapValue (0 : Fin 3))
  | strictAtHalfGapIsotropic
      (fullDefect_strict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap : a.alphaValue (0 : Fin 3) =
        a.halfGapValue (0 : Fin 3))
      (firstThree_isotropic : a.Lemma814FirstThreeIsotropic)
  | strictAtHalfGapAnisotropic
      (fullDefect_strict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap : a.alphaValue (0 : Fin 3) =
        a.halfGapValue (0 : Fin 3))
      (firstThree_anisotropic : a.Lemma814FirstThreeAnisotropic)

/-- The second alpha is at least one in the quaternary residual profile. -/
theorem beli2019Lemma912_secondAlpha_one_le_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c) :
    1 ≤ a.alphaValue (1 : Fin 3) := by
  have hgapReverse : a.orderGap (1 : Fin 3) =
      -a.orderGap (0 : Fin 3) := by
    change a.order (2 : Fin 4) - a.order (1 : Fin 4) =
      -(a.order (1 : Fin 4) - a.order (0 : Fin 4))
    rw [← profile.firstThird_eq]
    ring
  have hne : a.alphaValue (1 : Fin 3) ≠ 0 := by
    intro hzero
    have hgapZero := (a.alpha_p2 (1 : Fin 3)).2.mp hzero
    have := profile.firstGap_le_twoE_sub_two
    omega
  exact a.one_le_alphaValue_of_ne_zero (1 : Fin 3) hne

/-- The five quaternary alternatives exhaust the residual profile. -/
theorem beli2019Lemma912_parameterBranches_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c) :
    Beli2019Lemma912ParameterBranchRankFour a c := by
  rcases profile.fullDefectAlternative with hstrict | hequal
  · have hhalf := a.alphaValue_le_halfGapValue (0 : Fin 3)
    rcases eq_or_lt_of_le hhalf with hhalfEq | hhalfLt
    · by_cases hisotropic : a.Lemma814FirstThreeIsotropic
      · exact .strictAtHalfGapIsotropic hstrict hhalfEq hisotropic
      · have hanisotropic : a.Lemma814FirstThreeAnisotropic := by
          intro x hx
          by_contra hxne
          exact hisotropic ⟨x, hxne, hx⟩
        exact .strictAtHalfGapAnisotropic hstrict hhalfEq hanisotropic
    · exact .strictBelowHalfGap hstrict hhalfLt
  · rcases hequal with ⟨hfull, hfirstAlpha⟩
    have hone := a.beli2019Lemma912_secondAlpha_one_le_rankFour c profile
    rcases eq_or_lt_of_le hone with honeEq | honeLt
    · exact .equalSecondOne hfull hfirstAlpha honeEq.symm
    · exact .equalSecondLarge hfull hfirstAlpha honeLt

/-- The first alpha is integral in the quaternary residual profile. -/
theorem beli2019Lemma912_firstAlpha_integral_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c) :
    IsRationalInteger (a.alphaValue (0 : Fin 3)) := by
  apply a.beli2009Corollary28_i (0 : Fin 3)
  rintro ⟨_, hlarge⟩
  have := profile.firstGap_le_twoE_sub_two
  omega

/-- Below the first half-gap, the integral first alpha is odd. -/
theorem beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (hbelow : a.alphaValue (0 : Fin 3) <
      a.halfGapValue (0 : Fin 3)) :
    IsOddRationalInteger (a.alphaValue (0 : Fin 3)) :=
  a.beli2009Lemma27_iv (0 : Fin 3) (ne_of_lt hbelow)

/-- In the below-half-gap branch, parity sharpens the first gap by two. -/
theorem beli2019Lemma912_firstGap_le_twoE_sub_four_of_below_halfGap_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hbelow : a.alphaValue (0 : Fin 3) <
      a.halfGapValue (0 : Fin 3)) :
    a.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) - 4 := by
  by_contra hnot
  have hgap : a.orderGap (0 : Fin 3) =
      2 * (ramificationIndex K : Int) - 2 := by
    rcases profile.firstGap_even with ⟨z, hz⟩
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hhalf := a.beli2009Corollary29_i (0 : Fin 3)
    (Or.inr (Or.inr (Or.inr hgap)))
  exact (ne_of_lt hbelow) hhalf

/-- Equal outer orders imply monotonicity from the first to the third alpha. -/
theorem beli2019Lemma912_firstAlpha_le_thirdAlpha_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c) :
    a.alphaValue (0 : Fin 3) ≤ a.alphaValue (2 : Fin 3) := by
  have hmono := a.alphaLeftEndpoint_monotone
    (show (0 : Fin 3) ≤ (2 : Fin 3) by omega)
  unfold alphaLeftEndpoint at hmono
  have hzeroCast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
  have htwoCast : (2 : Fin 3).castSucc = (2 : Fin 4) := by rfl
  rw [hzeroCast, htwoCast, ← profile.firstThird_eq] at hmono
  linarith

/-- A strict full-prefix defect is strictly below the third alpha cap. -/
theorem beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict_rankFour
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    a.alphaValue (0 : Fin 3) < a.alphaValue (2 : Fin 3) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap c (-1) 3 1
  rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
  simpa using WithTop.coe_lt_coe.mp (hstrict.trans_le hcap)

/-- In the equal-alpha branch, a second alpha larger than one forces a
two-step rise to the fourth order. -/
theorem beli2019Lemma912_fourthOrder_ge_add_two_of_secondAlpha_large_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hlarge : 1 < a.alphaValue (1 : Fin 3)) :
    a.order (1 : Fin 4) + 2 ≤ a.order (3 : Fin 4) := by
  by_contra hnot
  have hfourth : a.order (3 : Fin 4) = a.order (1 : Fin 4) + 1 := by
    have hindex : (⟨3, by omega⟩ : Fin 4) = (3 : Fin 4) := by
      apply Fin.ext
      rfl
    have hlt := profile.second_lt_fourth (by omega)
    rw [hindex] at hlt
    omega
  rcases profile.firstGap_even with ⟨z, hz⟩
  have hsumOdd : Odd (a.order (2 : Fin 4) + a.order (3 : Fin 4)) := by
    refine ⟨a.order (0 : Fin 4) + z, ?_⟩
    unfold orderGap at hz
    change a.order (1 : Fin 4) - a.order (0 : Fin 4) = z + z at hz
    rw [← profile.firstThird_eq, hfourth]
    omega
  have hadjacent : a.adjacentDefect (2 : Fin 3) = 0 :=
    a.adjacentDefect_eq_zero_of_order_sum_odd (2 : Fin 3) hsumOdd
  have hupper := a.alpha_le_rightDefectCandidate
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by omega)
  rw [← a.coe_alphaValue] at hupper
  unfold rightDefectCandidate at hupper
  rw [hadjacent, add_zero] at hupper
  have hdiff : a.order (3 : Fin 4) - a.order (1 : Fin 4) = 1 := by omega
  have hsucc : (2 : Fin 3).succ = (3 : Fin 4) := by rfl
  have hcast : (1 : Fin 3).castSucc = (1 : Fin 4) := by rfl
  rw [hsucc, hcast, hdiff] at hupper
  have hupperQ : a.alphaValue (1 : Fin 3) ≤ 1 :=
    WithTop.coe_le_coe.mp (by simpa using hupper)
  exact (not_lt_of_ge hupperQ) hlarge

/-- In the equal-alpha branch, the comparison second order rises by at
least two. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large_rankFour
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hfirstAlpha : a.alphaValue (0 : Fin 3) = c.alphaValue (0 : Fin 3))
    (hlarge : 1 < a.alphaValue (1 : Fin 3)) :
    a.order (1 : Fin 4) + 2 ≤ c.order (1 : Fin 4) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin 4) = a.order (1 : Fin 4) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin 2) profile.firstThird_eq
  have hsourceFormula : a.alphaValue (0 : Fin 3) =
      ((a.order (1 : Fin 4) - a.order (2 : Fin 4) : Int) : ℚ) +
        a.alphaValue (1 : Fin 3) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha,
      remark87MiddleValue, remark87NextValue] using hremark.previousAlpha_eq
  rw [← profile.firstThird_eq] at hsourceFormula
  have htargetGap : c.orderGap (0 : Fin 3) =
      a.orderGap (0 : Fin 3) + 1 := by
    unfold orderGap
    change c.order (1 : Fin 4) - c.order (0 : Fin 4) =
      (a.order (1 : Fin 4) - a.order (0 : Fin 4)) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetGapOdd : Odd (c.orderGap (0 : Fin 3)) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetGapLe : c.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin 3) =
      (c.orderGap (0 : Fin 3) : ℚ) :=
    (c.alpha_p3 (0 : Fin 3) htargetGapLe).2.mpr (Or.inr htargetGapOdd)
  rw [hfirstAlpha, htargetAlpha, htargetGap] at hsourceFormula
  unfold orderGap at hsourceFormula
  push_cast at hsourceFormula
  linarith

/-- In a strict full-defect branch, the fourth order rises by at least two. -/
theorem beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    a.order (1 : Fin 4) + 2 ≤ a.order (3 : Fin 4) := by
  by_contra hnot
  have hfourth : a.order (3 : Fin 4) = a.order (1 : Fin 4) + 1 := by
    have hindex : (⟨3, by omega⟩ : Fin 4) = (3 : Fin 4) := by
      apply Fin.ext
      rfl
    have hlt := profile.second_lt_fourth (by omega)
    rw [hindex] at hlt
    omega
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict_rankFour
      c hstrict
  have hthirdGap : a.orderGap (2 : Fin 3) =
      a.orderGap (0 : Fin 3) + 1 := by
    unfold orderGap
    change a.order (3 : Fin 4) - a.order (2 : Fin 4) =
      (a.order (1 : Fin 4) - a.order (0 : Fin 4)) + 1
    rw [hfourth, ← profile.firstThird_eq]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have hthirdOdd : Odd (a.orderGap (2 : Fin 3)) := by
    refine ⟨z, ?_⟩
    rw [hthirdGap, hz]
    omega
  have hthirdLe : a.orderGap (2 : Fin 3) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hthirdAlpha : a.alphaValue (2 : Fin 3) =
      (a.orderGap (2 : Fin 3) : ℚ) :=
    (a.alpha_p3 (2 : Fin 3) hthirdLe).2.mpr (Or.inr hthirdOdd)
  have hfirstLe : a.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hfirstLower := (a.alpha_p3 (0 : Fin 3) hfirstLe).1
  have hfirstNe : a.alphaValue (0 : Fin 3) ≠
      (a.orderGap (0 : Fin 3) : ℚ) := by
    intro heq
    rcases (a.alpha_p3 (0 : Fin 3) hfirstLe).2.mp heq with heqGap | hodd
    · have := profile.firstGap_le_twoE_sub_two
      omega
    · exact (Int.not_odd_iff_even.mpr profile.firstGap_even) hodd
  have hfirstStrict : (a.orderGap (0 : Fin 3) : ℚ) <
      a.alphaValue (0 : Fin 3) :=
    lt_of_le_of_ne hfirstLower hfirstNe.symm
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A, hA⟩
  have hLowerZ : a.orderGap (0 : Fin 3) < A := by
    exact_mod_cast (show (a.orderGap (0 : Fin 3) : ℚ) < (A : ℚ) by
      simpa only [← hA] using hfirstStrict)
  have hUpperZ : A < a.orderGap (0 : Fin 3) + 1 := by
    exact_mod_cast (show (A : ℚ) <
      ((a.orderGap (0 : Fin 3) + 1 : Int) : ℚ) by
        rw [← hA, ← hthirdGap, ← hthirdAlpha]
        exact hthirdStrict)
  omega

/-- In a strict full-defect branch, the comparison second order rises by at
least two. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankFour
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    a.order (1 : Fin 4) + 2 ≤ c.order (1 : Fin 4) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin 4) = a.order (1 : Fin 4) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  have hcap := a.truncatedPrefixDefect_le_rightCap c (-1) 3 1
  rw [c.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)] at hcap
  have htargetStrict : a.alphaValue (0 : Fin 3) <
      c.alphaValue (0 : Fin 3) :=
    WithTop.coe_lt_coe.mp (by simpa using hstrict.trans_le hcap)
  have htargetGap : c.orderGap (0 : Fin 3) =
      a.orderGap (0 : Fin 3) + 1 := by
    unfold orderGap
    change c.order (1 : Fin 4) - c.order (0 : Fin 4) =
      (a.order (1 : Fin 4) - a.order (0 : Fin 4)) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetOdd : Odd (c.orderGap (0 : Fin 3)) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetLe : c.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  have hfirstLe : a.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hfirstLower := (a.alpha_p3 (0 : Fin 3) hfirstLe).1
  have hfirstNe : a.alphaValue (0 : Fin 3) ≠
      (a.orderGap (0 : Fin 3) : ℚ) := by
    intro heq
    rcases (a.alpha_p3 (0 : Fin 3) hfirstLe).2.mp heq with heqGap | hodd
    · have := profile.firstGap_le_twoE_sub_two
      omega
    · exact (Int.not_odd_iff_even.mpr profile.firstGap_even) hodd
  have hfirstStrict : (a.orderGap (0 : Fin 3) : ℚ) <
      a.alphaValue (0 : Fin 3) :=
    lt_of_le_of_ne hfirstLower hfirstNe.symm
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A, hA⟩
  have hLowerZ : a.orderGap (0 : Fin 3) < A := by
    exact_mod_cast (show (a.orderGap (0 : Fin 3) : ℚ) < (A : ℚ) by
      simpa only [← hA] using hfirstStrict)
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin 3) =
      (c.orderGap (0 : Fin 3) : ℚ) :=
    (c.alpha_p3 (0 : Fin 3) htargetLe).2.mpr (Or.inr htargetOdd)
  have hUpperZ : A < a.orderGap (0 : Fin 3) + 1 := by
    exact_mod_cast (show (A : ℚ) <
      ((a.orderGap (0 : Fin 3) + 1 : Int) : ℚ) by
        rw [← hA, ← htargetGap, ← htargetAlpha]
        exact htargetStrict)
  omega

/-- The numerical data required by Lemma 9.10 at quaternary rank. -/
structure Beli2019Lemma912TypeIBetaDataRankFour
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (A₁ β₁ : Int) : Prop where
  firstAlpha : a.alphaValue (0 : Fin 3) = (A₁ : ℚ)
  betaLower : A₁ ≤ β₁
  betaUpper : β₁ ≤ A₁ + 2
  betaThird : (β₁ : ℚ) ≤ a.alphaValue (2 : Fin 3)
  fourthOrder : a.order (1 : Fin 4) + 2 ≤ a.order (3 : Fin 4)
  sourceSecondOrder : a.order (1 : Fin 4) + 2 ≤ c.order (1 : Fin 4)

private theorem intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (i : Fin 3) (z : Int)
    (hzOdd : Odd z) (hlt : (z : ℚ) < a.alphaValue i)
    (hhalf : ((z + 2 : Int) : ℚ) ≤ a.halfGapValue i) :
    ((z + 2 : Int) : ℚ) ≤ a.alphaValue i := by
  by_cases heq : a.alphaValue i = a.halfGapValue i
  · rw [heq]
    exact hhalf
  · rcases a.beli2009Lemma27_iv i heq with ⟨w, hwOdd, hw⟩
    have hzw : z < w := by
      exact_mod_cast (show (z : ℚ) < (w : ℚ) by simpa only [← hw] using hlt)
    rcases hzOdd with ⟨s, hs⟩
    rcases hwOdd with ⟨t, ht⟩
    have hstep : z + 2 ≤ w := by omega
    rw [hw]
    exact_mod_cast hstep

/-- In the equal-alpha large-second-alpha branch, choose `β₁ = A₁`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankFour_of_equalSecondLarge
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hfirstAlpha : a.alphaValue (0 : Fin 3) = c.alphaValue (0 : Fin 3))
    (hlarge : 1 < a.alphaValue (1 : Fin 3)) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaDataRankFour a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_, ?_, ?_⟩
  · simpa only [← hA₁] using
      a.beli2019Lemma912_firstAlpha_le_thirdAlpha_rankFour c profile
  · exact a.beli2019Lemma912_fourthOrder_ge_add_two_of_secondAlpha_large_rankFour
      c profile hlarge
  · exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large_rankFour
      (alphaV := alphaV) (alphaW := alphaW)
        a c profile hfirst hfirstAlpha hlarge

/-- In the below-half-gap branch, choose `β₁ = A₁ + 2`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankFour_of_belowHalfGap
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin 3) < a.halfGapValue (0 : Fin 3)) :
    ∃ A₁ : Int,
      Beli2019Lemma912TypeIBetaDataRankFour a c A₁ (A₁ + 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A₁, hA₁⟩
  have hA₁OddRational :=
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankFour hbelow
  have hA₁Odd : Odd A₁ := by
    rcases hA₁OddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by exact_mod_cast hA₁.symm.trans hz
    simpa only [hAz] using hzOdd
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin 3) profile.firstGap_even with ⟨H, hH⟩
  have hA₁H : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← hA₁, ← hH] using hbelow)
  have hA₁Step : A₁ + 1 ≤ H := by omega
  have horders :=
    a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict_rankFour
      c profile hstrict
  have hordersQ : (a.order (1 : Fin 4) : ℚ) + 2 ≤
      (a.order (3 : Fin 4) : ℚ) := by exact_mod_cast horders
  have hhalfShift : a.halfGapValue (0 : Fin 3) + 1 ≤
      a.halfGapValue (2 : Fin 3) := by
    unfold halfGapValue orderGap
    have hzeroSucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
    have hzeroCast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
    have htwoSucc : (2 : Fin 3).succ = (3 : Fin 4) := by rfl
    have htwoCast : (2 : Fin 3).castSucc = (2 : Fin 4) := by rfl
    rw [hzeroSucc, hzeroCast, htwoSucc, htwoCast,
      ← profile.firstThird_eq]
    push_cast
    linarith [hordersQ]
  have hhalfBeta : ((A₁ + 2 : Int) : ℚ) ≤
      a.halfGapValue (2 : Fin 3) := by
    have hstepQ : ((A₁ + 1 : Int) : ℚ) ≤ (H : ℚ) := by
      exact_mod_cast hA₁Step
    calc
      ((A₁ + 2 : Int) : ℚ) = ((A₁ + 1 : Int) : ℚ) + 1 := by
        push_cast
        ring
      _ ≤ (H : ℚ) + 1 := by linarith
      _ = a.halfGapValue (0 : Fin 3) + 1 := by rw [hH]
      _ ≤ a.halfGapValue (2 : Fin 3) := hhalfShift
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict_rankFour
      c hstrict
  have hthird : ((A₁ + 2 : Int) : ℚ) ≤ a.alphaValue (2 : Fin 3) := by
    apply intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le_rankFour
      a (2 : Fin 3) A₁ hA₁Odd
    · simpa only [← hA₁] using hthirdStrict
    · exact hhalfBeta
  refine ⟨A₁, hA₁, by omega, by omega, hthird, horders, ?_⟩
  exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankFour
    (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict

/-- At an isotropic half-gap, choose `β₁ = A₁ + 1`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankFour_of_halfGapIsotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin 3) = a.halfGapValue (0 : Fin 3)) :
    ∃ A₁ : Int,
      Beli2019Lemma912TypeIBetaDataRankFour a c A₁ (A₁ + 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A₁, hA₁⟩
  have hA₁TwoE : A₁ + 1 ≤ 2 * (ramificationIndex K : Int) := by
    have hboundQ : (a.orderGap (0 : Fin 3) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by
      exact_mod_cast profile.firstGap_le_twoE_sub_two
    have hhalfFormula := hhalf
    rw [hA₁] at hhalfFormula
    unfold halfGapValue at hhalfFormula
    have hcast : ((A₁ + 1 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      push_cast at hhalfFormula ⊢
      linarith [hboundQ]
    exact_mod_cast hcast
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict_rankFour
      c hstrict
  have hthird : ((A₁ + 1 : Int) : ℚ) ≤ a.alphaValue (2 : Fin 3) := by
    apply a.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      (2 : Fin 3) A₁ hA₁TwoE
    simpa only [← hA₁] using hthirdStrict
  refine ⟨A₁, hA₁, by omega, by omega, hthird, ?_, ?_⟩
  · exact a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict_rankFour
      c profile hstrict
  · exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankFour
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict

/-- At an anisotropic half-gap, choose `β₁ = A₁`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankFour_of_halfGapAnisotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hstrict : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaDataRankFour a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankFour c profile with ⟨A₁, hA₁⟩
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict_rankFour
      c hstrict
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_, ?_, ?_⟩
  · simpa only [← hA₁] using hthirdStrict.le
  · exact a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict_rankFour
      c profile hstrict
  · exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankFour
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict

end BONG.GoodBONG

end Bong
