/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912LowBranches
import Bong.Bong.Beli2019Lemma912Lemma99Conditions

/-!
# Beli (2019), Lemma 9.12: ternary parameter arithmetic

The printed argument starts in rank three, whereas the first implementation
of its type-I parameter split used two later coordinates.  This file proves
the part of the split that only concerns the initial ternary block directly
at rank three.  In particular, no nonexistent fourth coordinate is introduced.
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

/-- The five parameter alternatives of Lemma 9.12 at literal ternary rank. -/
inductive Beli2019Lemma912ParameterBranchRankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M 3) : Prop
  | equalSecondLarge
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin 2) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin 2) =
        c.alphaValue (0 : Fin 2))
      (secondAlpha_large : 1 < a.alphaValue (1 : Fin 2))
  | equalSecondOne
      (fullDefect_eq : a.truncatedPrefixDefect c (-1) 3 1 =
        (a.alphaValue (0 : Fin 2) : WithTop ℚ))
      (firstAlpha_eq : a.alphaValue (0 : Fin 2) =
        c.alphaValue (0 : Fin 2))
      (secondAlpha_eq_one : a.alphaValue (1 : Fin 2) = 1)
  | strictBelowHalfGap
      (fullDefect_strict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_below_halfGap : a.alphaValue (0 : Fin 2) <
        a.halfGapValue (0 : Fin 2))
  | strictAtHalfGapIsotropic
      (fullDefect_strict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap : a.alphaValue (0 : Fin 2) =
        a.halfGapValue (0 : Fin 2))
      (firstThree_isotropic : a.Lemma814FirstThreeIsotropic)
  | strictAtHalfGapAnisotropic
      (fullDefect_strict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
      (firstAlpha_eq_halfGap : a.alphaValue (0 : Fin 2) =
        a.halfGapValue (0 : Fin 2))
      (firstThree_anisotropic : a.Lemma814FirstThreeAnisotropic)

/-- The second alpha is at least one in the ternary residual profile. -/
theorem beli2019Lemma912_secondAlpha_one_le_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c) :
    1 ≤ a.alphaValue (1 : Fin 2) := by
  have hgapReverse : a.orderGap (1 : Fin 2) =
      -a.orderGap (0 : Fin 2) := by
    change a.order (2 : Fin 3) - a.order (1 : Fin 3) =
      -(a.order (1 : Fin 3) - a.order (0 : Fin 3))
    rw [← profile.firstThird_eq]
    ring
  have hne : a.alphaValue (1 : Fin 2) ≠ 0 := by
    intro hzero
    have hgapZero := (a.alpha_p2 (1 : Fin 2)).2.mp hzero
    have := profile.firstGap_le_twoE_sub_two
    omega
  exact a.one_le_alphaValue_of_ne_zero (1 : Fin 2) hne

/-- The five ternary alternatives exhaust the residual profile. -/
theorem beli2019Lemma912_parameterBranches_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c) :
    Beli2019Lemma912ParameterBranchRankThree a c := by
  rcases profile.fullDefectAlternative with hstrict | hequal
  · have hhalf := a.alphaValue_le_halfGapValue (0 : Fin 2)
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
    have hone := a.beli2019Lemma912_secondAlpha_one_le_rankThree c profile
    rcases eq_or_lt_of_le hone with honeEq | honeLt
    · exact .equalSecondOne hfull hfirstAlpha honeEq.symm
    · exact .equalSecondLarge hfull hfirstAlpha honeLt

/-- The first alpha is integral already at rank three. -/
theorem beli2019Lemma912_firstAlpha_integral_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c) :
    IsRationalInteger (a.alphaValue (0 : Fin 2)) := by
  apply a.beli2009Corollary28_i (0 : Fin 2)
  rintro ⟨_, hlarge⟩
  have := profile.firstGap_le_twoE_sub_two
  omega

/-- Below the first half-gap, the integral first alpha is odd. -/
theorem beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (hbelow : a.alphaValue (0 : Fin 2) <
      a.halfGapValue (0 : Fin 2)) :
    IsOddRationalInteger (a.alphaValue (0 : Fin 2)) :=
  a.beli2009Lemma27_iv (0 : Fin 2) (ne_of_lt hbelow)

/-- In the below-half-gap branch, parity improves the gap bound by two. -/
theorem beli2019Lemma912_firstGap_le_twoE_sub_four_of_below_halfGap_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hbelow : a.alphaValue (0 : Fin 2) <
      a.halfGapValue (0 : Fin 2)) :
    a.orderGap (0 : Fin 2) ≤ 2 * (ramificationIndex K : Int) - 4 := by
  by_contra hnot
  have hgap : a.orderGap (0 : Fin 2) =
      2 * (ramificationIndex K : Int) - 2 := by
    rcases profile.firstGap_even with ⟨z, hz⟩
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hhalf := a.beli2009Corollary29_i (0 : Fin 2)
    (Or.inr (Or.inr (Or.inr hgap)))
  exact (ne_of_lt hbelow) hhalf

/-- In the equal-alpha, second-alpha-large branch, the comparison second
order is at least two above the source second order. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large_rankThree
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hfirstAlpha : a.alphaValue (0 : Fin 2) =
      c.alphaValue (0 : Fin 2))
    (hlarge : 1 < a.alphaValue (1 : Fin 2)) :
    a.order (1 : Fin 3) + 2 ≤ c.order (1 : Fin 3) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin 3) =
      a.order (1 : Fin 3) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin 1) profile.firstThird_eq
  have hsourceFormula : a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha,
      remark87MiddleValue, remark87NextValue] using hremark.previousAlpha_eq
  rw [← profile.firstThird_eq] at hsourceFormula
  have htargetGap : c.orderGap (0 : Fin 2) =
      a.orderGap (0 : Fin 2) + 1 := by
    unfold orderGap
    change c.order (1 : Fin 3) - c.order (0 : Fin 3) =
      (a.order (1 : Fin 3) - a.order (0 : Fin 3)) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetGapOdd : Odd (c.orderGap (0 : Fin 2)) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetGapLe : c.orderGap (0 : Fin 2) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin 2) =
      (c.orderGap (0 : Fin 2) : ℚ) :=
    (c.alpha_p3 (0 : Fin 2) htargetGapLe).2.mpr (Or.inr htargetGapOdd)
  rw [hfirstAlpha, htargetAlpha, htargetGap] at hsourceFormula
  unfold orderGap at hsourceFormula
  push_cast at hsourceFormula
  linarith

/-- In every strict full-defect ternary branch, the comparison second order
is at least two above the source second order. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankThree
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    a.order (1 : Fin 3) + 2 ≤ c.order (1 : Fin 3) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin 3) =
      a.order (1 : Fin 3) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  have hcap := a.truncatedPrefixDefect_le_rightCap c (-1) 3 1
  rw [c.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)] at hcap
  have htargetStrictTop : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      (c.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    simpa using hstrict.trans_le hcap
  have htargetStrict : a.alphaValue (0 : Fin 2) <
      c.alphaValue (0 : Fin 2) := WithTop.coe_lt_coe.mp htargetStrictTop
  have htargetGap : c.orderGap (0 : Fin 2) =
      a.orderGap (0 : Fin 2) + 1 := by
    unfold orderGap
    change c.order (1 : Fin 3) - c.order (0 : Fin 3) =
      (a.order (1 : Fin 3) - a.order (0 : Fin 3)) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetOdd : Odd (c.orderGap (0 : Fin 2)) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetLe : c.orderGap (0 : Fin 2) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  have hfirstLe : a.orderGap (0 : Fin 2) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hfirstLower := (a.alpha_p3 (0 : Fin 2) hfirstLe).1
  have hfirstNe : a.alphaValue (0 : Fin 2) ≠
      (a.orderGap (0 : Fin 2) : ℚ) := by
    intro heq
    rcases (a.alpha_p3 (0 : Fin 2) hfirstLe).2.mp heq with heqGap | hodd
    · have := profile.firstGap_le_twoE_sub_two
      omega
    · exact (Int.not_odd_iff_even.mpr profile.firstGap_even) hodd
  have hfirstStrict : (a.orderGap (0 : Fin 2) : ℚ) <
      a.alphaValue (0 : Fin 2) :=
    lt_of_le_of_ne hfirstLower hfirstNe.symm
  rcases a.beli2019Lemma912_firstAlpha_integral_rankThree c profile with ⟨A, hA⟩
  have hLowerZ : a.orderGap (0 : Fin 2) < A := by
    exact_mod_cast (show (a.orderGap (0 : Fin 2) : ℚ) < (A : ℚ) by
      simpa only [← hA] using hfirstStrict)
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin 2) =
      (c.orderGap (0 : Fin 2) : ℚ) :=
    (c.alpha_p3 (0 : Fin 2) htargetLe).2.mpr (Or.inr htargetOdd)
  have hUpperZ : A < a.orderGap (0 : Fin 2) + 1 := by
    exact_mod_cast (show (A : ℚ) <
      ((a.orderGap (0 : Fin 2) + 1 : Int) : ℚ) by
        rw [← hA, ← htargetGap, ← htargetAlpha]
        exact htargetStrict)
  omega

end BONG.GoodBONG

end Bong
