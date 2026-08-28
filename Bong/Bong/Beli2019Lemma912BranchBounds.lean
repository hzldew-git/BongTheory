/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint
import Bong.Bong.Beli2019Lemma912Branches
import Bong.Bong.Beli2019CappedIntegrality
/-!
# Beli (2019), Lemma 9.12: arithmetic bounds in the residual branches

This file proves the numerical consequences used to start the constructions
after the five-way split in Lemma 9.12. The first alpha is integral; in the
below-half-gap case it is odd; and the relevant branches force the two order
bounds required by the type-I claim. The sole remaining alternative is
isolated as the paper's type-III parameter branch.
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

private theorem intCast_add_one_le_defectOrder_of_lt'
    (x : Kˣ) (A : Int)
    (hstrict : (((A : ℚ) : WithTop ℚ) < defectOrder (K := K) x)) :
    ((((A + 1 : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) := by
  rcases defectOrder_eq_top_or_isWithTopRationalInteger
      (K := K) x with htop | ⟨z, hz⟩
  · rw [htop]
    exact le_top
  · rw [hz] at hstrict ⊢
    apply WithTop.coe_le_coe.mpr
    have hAz : A < z := by
      exact_mod_cast WithTop.coe_lt_coe.mp hstrict
    exact_mod_cast (show A + 1 ≤ z by omega)

private theorem intCast_add_one_le_alphaValue_of_lt_of_le_twoE'
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n) (z : Int)
    (hz : z + 1 ≤ 2 * (ramificationIndex K : Int))
    (hlt : (z : ℚ) < a.alphaValue i) :
    ((z + 1 : Int) : ℚ) ≤ a.alphaValue i := by
  rcases a.beli2009Corollary28_iii i with
    ⟨_, _, hintegral⟩ | ⟨hlarge, _⟩
  · rcases hintegral with ⟨w, hw⟩
    have hzw : z < w := by
      exact_mod_cast (show (z : ℚ) < (w : ℚ) by simpa only [← hw] using hlt)
    have hstep : z + 1 ≤ w := by omega
    rw [hw]
    exact_mod_cast hstep
  · have htwoE : ((z + 1 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hz
    exact htwoE.trans hlarge.le

/-- In the first branch, `α₂ > 1` rules out `R₄ = R₂ + 1`. -/
theorem beli2019Lemma912_fourthOrder_ge_add_two_of_secondAlpha_large
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hlarge : 1 < a.alphaValue (1 : Fin (N + 4))) :
    a.order (1 : Fin (N + 5)) + 2 ≤
      a.order (3 : Fin (N + 5)) := by
  by_contra hnot
  have hfourth : a.order (3 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) + 1 := by
    have := profile.second_lt_fourth
    omega
  rcases profile.firstGap_even with ⟨z, hz⟩
  have hsumOdd : Odd
      (a.order (2 : Fin (N + 5)) + a.order (3 : Fin (N + 5))) := by
    refine ⟨a.order (0 : Fin (N + 5)) + z, ?_⟩
    unfold orderGap at hz
    change a.order (1 : Fin (N + 5)) -
      a.order (0 : Fin (N + 5)) = z + z at hz
    rw [← profile.firstThird_eq, hfourth]
    omega
  have hadjacent : a.adjacentDefect (2 : Fin (N + 4)) = 0 :=
    a.adjacentDefect_eq_zero_of_order_sum_odd
      (2 : Fin (N + 4)) (by
        change Odd
          (a.order (2 : Fin (N + 5)) + a.order (3 : Fin (N + 5)))
        exact hsumOdd)
  have hupper := a.alpha_le_rightDefectCandidate
    (i := (1 : Fin (N + 4))) (j := (2 : Fin (N + 4))) (by
      change (1 : Nat) ≤ 2
      omega)
  rw [← a.coe_alphaValue] at hupper
  unfold rightDefectCandidate at hupper
  rw [hadjacent, add_zero] at hupper
  have hsucc : (2 : Fin (N + 4)).succ =
      (3 : Fin (N + 5)) := by rfl
  have hcast : (1 : Fin (N + 4)).castSucc =
      (1 : Fin (N + 5)) := by rfl
  have hdiff : a.order (3 : Fin (N + 5)) -
      a.order (1 : Fin (N + 5)) = 1 := by omega
  rw [hsucc, hcast, hdiff] at hupper
  have hupperQ : a.alphaValue (1 : Fin (N + 4)) ≤ 1 := by
    exact WithTop.coe_le_coe.mp (by simpa using hupper)
  exact (not_lt_of_ge hupperQ) hlarge

/-- In the first branch, `α₁ = γ₁` and `α₂ > 1` rule out
`T₂ = R₂ + 1`. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hfirstAlpha : a.alphaValue (0 : Fin (N + 4)) =
      c.alphaValue (0 : Fin (N + 4)))
    (hlarge : 1 < a.alphaValue (1 : Fin (N + 4))) :
    a.order (1 : Fin (N + 5)) + 2 ≤
      c.order (1 : Fin (N + 5)) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  let p : Fin (N + 3) := ⟨0, by omega⟩
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hpPreviousValue : remark87PreviousValue p =
      (0 : Fin (N + 5)) := by
    apply Fin.ext
    rfl
  have hpNextValue : remark87NextValue p =
      (2 : Fin (N + 5)) := by
    apply Fin.ext
    rfl
  have houter : a.order (remark87PreviousValue p) =
      a.order (remark87NextValue p) := by
    rw [hpPreviousValue, hpNextValue]
    exact profile.firstThird_eq
  have hremark := a.beli2019Remark87 p houter
  have hpPreviousAlpha : remark87PreviousAlpha p =
      (0 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have hpCurrentAlpha : remark87CurrentAlpha p =
      (1 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have hpMiddleValue : remark87MiddleValue p =
      (1 : Fin (N + 5)) := by
    apply Fin.ext
    rfl
  have hsourceFormula : a.alphaValue (0 : Fin (N + 4)) =
      ((a.order (1 : Fin (N + 5)) -
        a.order (2 : Fin (N + 5)) : Int) : ℚ) +
        a.alphaValue (1 : Fin (N + 4)) := by
    have h := hremark.previousAlpha_eq
    rw [hpPreviousAlpha, hpCurrentAlpha, hpMiddleValue, hpNextValue] at h
    exact h
  rw [← profile.firstThird_eq] at hsourceFormula
  have htargetGap : c.orderGap (0 : Fin (N + 4)) =
      a.orderGap (0 : Fin (N + 4)) + 1 := by
    unfold orderGap
    change c.order (1 : Fin (N + 5)) -
        c.order (0 : Fin (N + 5)) =
      (a.order (1 : Fin (N + 5)) -
        a.order (0 : Fin (N + 5))) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetGapOdd : Odd (c.orderGap (0 : Fin (N + 4))) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetGapLe : c.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin (N + 4)) =
      (c.orderGap (0 : Fin (N + 4)) : ℚ) :=
    (c.alpha_p3 (0 : Fin (N + 4)) htargetGapLe).2.mpr
      (Or.inr htargetGapOdd)
  rw [hfirstAlpha, htargetAlpha] at hsourceFormula
  rw [htargetGap] at hsourceFormula
  unfold orderGap at hsourceFormula
  have hsucc : (0 : Fin (N + 4)).succ =
      (1 : Fin (N + 5)) := by rfl
  have hcast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  rw [hsucc, hcast] at hsourceFormula
  push_cast at hsourceFormula
  linarith

/-- The first alpha in the residual profile is integral. -/
theorem beli2019Lemma912_firstAlpha_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c) :
    IsRationalInteger (a.alphaValue (0 : Fin (N + 4))) := by
  apply a.beli2009Corollary28_i (0 : Fin (N + 4))
  rintro ⟨_, hlarge⟩
  have := profile.firstGap_le_twoE_sub_two
  omega

/-- Below the half-gap branch, the first alpha is an odd integer. -/
theorem beli2019Lemma912_firstAlpha_odd_of_below_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4))) :
    IsOddRationalInteger (a.alphaValue (0 : Fin (N + 4))) :=
  a.beli2009Lemma27_iv (0 : Fin (N + 4)) (ne_of_lt hbelow)

/-- In the below-half-gap branch, evenness excludes the endpoint
`R₂ - R₁ = 2e - 2`, leaving the sharper bound `2e - 4`. -/
theorem beli2019Lemma912_firstGap_le_twoE_sub_four_of_below_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4))) :
    a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 4 := by
  by_contra hnot
  have hgap : a.orderGap (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2 := by
    rcases profile.firstGap_even with ⟨z, hz⟩
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hhalf := a.beli2009Corollary29_i (0 : Fin (N + 4))
    (Or.inr (Or.inr (Or.inr hgap)))
  exact (ne_of_lt hbelow) hhalf

/-- In the strict anisotropic half-gap branch, the Lemma 9.6 exclusion removes
the endpoint `R₂ - R₁ = 2e - 2`.  At that endpoint the first alpha is
`2e - 1`; strictness and the discrete defect/alpha spectra therefore imply
the `2e` defect bound required by Lemma 9.6. -/
theorem beli2019Lemma912_firstGap_le_twoE_sub_four_of_strict_anisotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hstrict : (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4)))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 4 := by
  have hne : a.orderGap (0 : Fin (N + 4)) ≠
      2 * (ramificationIndex K : Int) - 2 := by
    intro hgap
    let z : Int := 2 * (ramificationIndex K : Int) - 1
    have hzOne : z + 1 = 2 * (ramificationIndex K : Int) := by
      dsimp only [z]
      ring
    have halpha : a.alphaValue (0 : Fin (N + 4)) = (z : ℚ) := by
      rw [hhalf]
      unfold halfGapValue
      rw [hgap]
      dsimp only [z]
      push_cast
      ring
    have hstrict' : (((z : ℚ) : WithTop ℚ)) <
        a.truncatedPrefixDefect c (-1) 3 1 := by
      simpa only [halpha] using hstrict
    have hrawStrict : (((z : ℚ) : WithTop ℚ)) <
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * c.prefixProduct 1) := by
      exact hstrict'.trans_le (a.truncatedPrefixDefect_le_defect c (-1) 3 1)
    have hleftStrict : (((z : ℚ) : WithTop ℚ)) <
        a.prefixAlphaCap 3 := by
      exact hstrict'.trans_le (a.truncatedPrefixDefect_le_leftCap c (-1) 3 1)
    have hrightStrict : (((z : ℚ) : WithTop ℚ)) <
        c.prefixAlphaCap 1 := by
      exact hstrict'.trans_le (a.truncatedPrefixDefect_le_rightCap c (-1) 3 1)
    have hrawLower := intCast_add_one_le_defectOrder_of_lt'
      (K := K) ((-1) * a.prefixProduct 3 * c.prefixProduct 1) z hrawStrict
    rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hleftStrict
    rw [c.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)] at hrightStrict
    have hleftLower : ((z + 1 : Int) : ℚ) ≤
        a.alphaValue (2 : Fin (N + 4)) := by
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      letI : Beli2009AlphaParityLaws.{u, v} K := parityV
      exact intCast_add_one_le_alphaValue_of_lt_of_le_twoE'.{u, v}
        (K := K) a (2 : Fin (N + 4)) z (by omega)
          (WithTop.coe_lt_coe.mp hleftStrict)
    have hrightLower : ((z + 1 : Int) : ℚ) ≤
        c.alphaValue (0 : Fin (N + 4)) := by
      letI : Beli2006AlphaLaws.{u, w} K := alphaW
      letI : Beli2009AlphaParityLaws.{u, w} K := parityW
      exact intCast_add_one_le_alphaValue_of_lt_of_le_twoE'.{u, w}
        (K := K) c (0 : Fin (N + 4)) z (by omega)
          (WithTop.coe_lt_coe.mp hrightStrict)
    have hdefect : a.Beli2019Lemma96DefectBound c := by
      unfold Beli2019Lemma96DefectBound truncatedPrefixDefect
      have hcast :
          ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) =
            ((((z + 1 : Int) : ℚ) : WithTop ℚ)) := by
        rw [hzOne]
        norm_num
      rw [hcast]
      apply le_min hrawLower
      apply le_min
      · rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)]
        exact WithTop.coe_le_coe.mpr hleftLower
      · rw [c.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)]
        exact WithTop.coe_le_coe.mpr hrightLower
    rcases profile.lemma96_exclusion_at_boundary hgap with hnot | hnot
    · exact hnot hdefect
    · exact hnot hanisotropic
  rcases profile.firstGap_even with ⟨z, hz⟩
  have := profile.firstGap_le_twoE_sub_two
  omega

/-- In every strict full-defect branch, the left alpha cap rules out
`R₄ = R₂ + 1`. -/
theorem beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hstrict :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1) :
    a.order (1 : Fin (N + 5)) + 2 ≤
      a.order (3 : Fin (N + 5)) := by
  by_contra hnot
  have hfourth : a.order (3 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) + 1 := by
    have := profile.second_lt_fourth
    omega
  have hcap := a.truncatedPrefixDefect_le_leftCap c (-1) 3 1
  rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
  have hcapIndex : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
      (2 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hcapIndex] at hcap
  have hthirdStrictTop :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        (a.alphaValue (2 : Fin (N + 4)) : WithTop ℚ) := by
    simpa using hstrict.trans_le hcap
  have hthirdStrict : a.alphaValue (0 : Fin (N + 4)) <
      a.alphaValue (2 : Fin (N + 4)) :=
    WithTop.coe_lt_coe.mp hthirdStrictTop
  have hthirdGap : a.orderGap (2 : Fin (N + 4)) =
      a.orderGap (0 : Fin (N + 4)) + 1 := by
    unfold orderGap
    change a.order (3 : Fin (N + 5)) -
        a.order (2 : Fin (N + 5)) =
      (a.order (1 : Fin (N + 5)) -
        a.order (0 : Fin (N + 5))) + 1
    rw [hfourth, ← profile.firstThird_eq]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have hthirdOdd : Odd (a.orderGap (2 : Fin (N + 4))) := by
    refine ⟨z, ?_⟩
    rw [hthirdGap, hz]
    omega
  have hthirdLe : a.orderGap (2 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hthirdAlpha : a.alphaValue (2 : Fin (N + 4)) =
      (a.orderGap (2 : Fin (N + 4)) : ℚ) :=
    (a.alpha_p3 (2 : Fin (N + 4)) hthirdLe).2.mpr
      (Or.inr hthirdOdd)
  have hfirstLe : a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hfirstLower :=
    (a.alpha_p3 (0 : Fin (N + 4)) hfirstLe).1
  have hfirstNe : a.alphaValue (0 : Fin (N + 4)) ≠
      (a.orderGap (0 : Fin (N + 4)) : ℚ) := by
    intro heq
    rcases (a.alpha_p3 (0 : Fin (N + 4)) hfirstLe).2.mp heq with
      heqGap | hodd
    · have := profile.firstGap_le_twoE_sub_two
      omega
    · exact (Int.not_odd_iff_even.mpr profile.firstGap_even) hodd
  have hfirstStrict : (a.orderGap (0 : Fin (N + 4)) : ℚ) <
      a.alphaValue (0 : Fin (N + 4)) :=
    lt_of_le_of_ne hfirstLower hfirstNe.symm
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A, hA⟩
  have hLowerZ : a.orderGap (0 : Fin (N + 4)) < A := by
    exact_mod_cast (show (a.orderGap (0 : Fin (N + 4)) : ℚ) <
      (A : ℚ) by simpa only [← hA] using hfirstStrict)
  have hUpperZ : A < a.orderGap (0 : Fin (N + 4)) + 1 := by
    exact_mod_cast (show (A : ℚ) <
      ((a.orderGap (0 : Fin (N + 4)) + 1 : Int) : ℚ) by
        rw [← hA, ← hthirdGap, ← hthirdAlpha]
        exact hthirdStrict)
  omega

/-- In every strict full-defect branch, the right alpha cap rules out
`T₂ = R₂ + 1`. -/
theorem beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1) :
    a.order (1 : Fin (N + 5)) + 2 ≤
      c.order (1 : Fin (N + 5)) := by
  by_contra hnot
  have htargetSecond : c.order (1 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) + 1 := by
    have := profile.second_lt_sourceSecond
    omega
  have hcap := a.truncatedPrefixDefect_le_rightCap c (-1) 3 1
  rw [c.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)] at hcap
  have hcapIndex : (⟨1 - 1, by omega⟩ : Fin (N + 4)) =
      (0 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hcapIndex] at hcap
  have htargetStrictTop :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        (c.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) :=
    hstrict.trans_le hcap
  have htargetStrict : a.alphaValue (0 : Fin (N + 4)) <
      c.alphaValue (0 : Fin (N + 4)) :=
    WithTop.coe_lt_coe.mp htargetStrictTop
  have htargetGap : c.orderGap (0 : Fin (N + 4)) =
      a.orderGap (0 : Fin (N + 4)) + 1 := by
    unfold orderGap
    change c.order (1 : Fin (N + 5)) -
        c.order (0 : Fin (N + 5)) =
      (a.order (1 : Fin (N + 5)) -
        a.order (0 : Fin (N + 5))) + 1
    rw [htargetSecond, ← hfirst]
    ring
  rcases profile.firstGap_even with ⟨z, hz⟩
  have htargetOdd : Odd (c.orderGap (0 : Fin (N + 4))) := by
    refine ⟨z, ?_⟩
    rw [htargetGap, hz]
    omega
  have htargetLe : c.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  have hfirstLe : a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) := by
    have := profile.firstGap_le_twoE_sub_two
    omega
  have hfirstLower :=
    (a.alpha_p3 (0 : Fin (N + 4)) hfirstLe).1
  have hfirstNe : a.alphaValue (0 : Fin (N + 4)) ≠
      (a.orderGap (0 : Fin (N + 4)) : ℚ) := by
    intro heq
    rcases (a.alpha_p3 (0 : Fin (N + 4)) hfirstLe).2.mp heq with
      heqGap | hodd
    · have := profile.firstGap_le_twoE_sub_two
      omega
    · exact (Int.not_odd_iff_even.mpr profile.firstGap_even) hodd
  have hfirstStrict : (a.orderGap (0 : Fin (N + 4)) : ℚ) <
      a.alphaValue (0 : Fin (N + 4)) :=
    lt_of_le_of_ne hfirstLower hfirstNe.symm
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A, hA⟩
  have hLowerZ : a.orderGap (0 : Fin (N + 4)) < A := by
    exact_mod_cast (show (a.orderGap (0 : Fin (N + 4)) : ℚ) <
      (A : ℚ) by simpa only [← hA] using hfirstStrict)
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  have htargetAlpha : c.alphaValue (0 : Fin (N + 4)) =
      (c.orderGap (0 : Fin (N + 4)) : ℚ) :=
    (c.alpha_p3 (0 : Fin (N + 4)) htargetLe).2.mpr
      (Or.inr htargetOdd)
  have hUpperZ : A < a.orderGap (0 : Fin (N + 4)) + 1 := by
    exact_mod_cast (show (A : ℚ) <
      ((a.orderGap (0 : Fin (N + 4)) + 1 : Int) : ℚ) by
        rw [← hA, ← htargetGap, ← htargetAlpha]
        exact htargetStrict)
  omega

/-- The two order inequalities required by the type-I claim. -/
structure Beli2019Lemma912TypeIOrderBounds
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop where
  fourthOrder : a.order (1 : Fin (N + 5)) + 2 ≤
    a.order (3 : Fin (N + 5))
  sourceSecondOrder : a.order (1 : Fin (N + 5)) + 2 ≤
    c.order (1 : Fin (N + 5))

/-- The unique residual branch requiring the separate type-III
construction. -/
def Beli2019Lemma912TypeIIIParameters
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5)) : Prop :=
  a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) ∧
    a.alphaValue (0 : Fin (N + 4)) =
      c.alphaValue (0 : Fin (N + 4)) ∧
    a.alphaValue (1 : Fin (N + 4)) = 1

/-- The paper's five-way split reduces to the exceptional type-III branch
or to the two order bounds needed by the type-I claim. -/
theorem beli2019Lemma912_typeIIIParameters_or_typeIOrderBounds
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5))) :
    Beli2019Lemma912TypeIIIParameters a c ∨
      Beli2019Lemma912TypeIOrderBounds a c := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_parameterBranches c profile with
    ⟨hfull, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, _, _⟩ |
    ⟨hstrict, _, _⟩
  · right
    refine ⟨?_, ?_⟩
    · exact a.beli2019Lemma912_fourthOrder_ge_add_two_of_secondAlpha_large
        c profile hlarge
    · exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large
        (alphaV := alphaV) (alphaW := alphaW) a c profile hfirst
          hfirstAlpha hlarge
  · left
    exact ⟨hfull, hfirstAlpha, hone⟩
  · right
    exact ⟨
      a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
        c profile hstrict,
      beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
          a c profile hfirst hstrict⟩
  · right
    exact ⟨
      a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
        c profile hstrict,
      beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
          a c profile hfirst hstrict⟩
  · right
    exact ⟨
      a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
        c profile hstrict,
      beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
          a c profile hfirst hstrict⟩

end BONG.GoodBONG

end Bong
