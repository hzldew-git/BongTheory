/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912BranchBounds
/-!
# Beli (2019), Lemma 9.12: the four type-I beta choices

For each residual type-I branch this file constructs the integer beta used in
Lemma 9.10 and verifies its interval, third-alpha, and order bounds. The choices
are respectively alpha, alpha plus two, alpha plus one, and alpha. The only
remaining branch is isolated as the paper's type-III construction.
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

/-- Equal first and third orders imply `α₁ ≤ α₃` by P1. -/
theorem beli2019Lemma912_firstAlpha_le_thirdAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c) :
    a.alphaValue (0 : Fin (N + 4)) ≤
      a.alphaValue (2 : Fin (N + 4)) := by
  have hmono := a.alphaLeftEndpoint_monotone
    (show (0 : Fin (N + 4)) ≤ (2 : Fin (N + 4)) by
      change (0 : Nat) ≤ 2
      omega)
  unfold alphaLeftEndpoint at hmono
  have hzeroCast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  have htwoCast : (2 : Fin (N + 4)).castSucc =
      (2 : Fin (N + 5)) := by rfl
  rw [hzeroCast, htwoCast, ← profile.firstThird_eq] at hmono
  linarith

/-- A strict full-prefix defect is strictly below the third alpha cap. -/
theorem beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (hstrict :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1) :
    a.alphaValue (0 : Fin (N + 4)) <
      a.alphaValue (2 : Fin (N + 4)) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap c (-1) 3 1
  rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
  have hindex : (⟨3 - 1, by omega⟩ : Fin (N + 4)) =
      (2 : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hindex] at hcap
  exact WithTop.coe_lt_coe.mp (hstrict.trans_le hcap)

/-- An alpha lying strictly above an integer `z` is at least `z + 1`,
provided that next integer is at most `2e`. -/
theorem intCast_add_one_le_alphaValue_of_lt_of_le_twoE
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

/-- Above an odd integer, an alpha either attains its half-gap or jumps by
at least two. -/
theorem intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (i : Fin (N + 4)) (z : Int)
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

/-- The arithmetic data required by Lemma 9.10 after choosing `β₁`. -/
structure Beli2019Lemma912TypeIBetaData
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (A₁ β₁ : Int) : Prop where
  firstAlpha : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ)
  betaLower : A₁ ≤ β₁
  betaUpper : β₁ ≤ A₁ + 2
  betaThird : (β₁ : ℚ) ≤ a.alphaValue (2 : Fin (N + 4))
  orderBounds : Beli2019Lemma912TypeIOrderBounds a c

/-- In branch 1, choose `β₁ = α₁`. -/
theorem exists_beli2019Lemma912TypeIBetaData_of_equalSecondLarge
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hfirstAlpha : a.alphaValue (0 : Fin (N + 4)) =
      c.alphaValue (0 : Fin (N + 4)))
    (hlarge : 1 < a.alphaValue (1 : Fin (N + 4))) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaData a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_, ?_⟩
  · simpa only [← hA₁] using a.beli2019Lemma912_firstAlpha_le_thirdAlpha
      c profile
  · exact ⟨
      a.beli2019Lemma912_fourthOrder_ge_add_two_of_secondAlpha_large
        c profile hlarge,
      beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large
        (alphaV := alphaV) (alphaW := alphaW) a c profile hfirst
          hfirstAlpha hlarge⟩

/-- In branch 3, choose `β₁ = α₁ + 2`. -/
theorem exists_beli2019Lemma912TypeIBetaData_of_belowHalfGap
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4))) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A₁, hA₁⟩
  have hA₁OddRational :=
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap hbelow
  have hA₁Odd : Odd A₁ := by
    rcases hA₁OddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by
      exact_mod_cast hA₁.symm.trans hz
    simpa only [hAz] using hzOdd
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin (N + 4)) profile.firstGap_even with ⟨H, hH⟩
  have hA₁H : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← hA₁, ← hH] using hbelow)
  have hA₁Step : A₁ + 1 ≤ H := by omega
  have horders :=
    a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
      c profile hstrict
  have hordersQ : (a.order (1 : Fin (N + 5)) : ℚ) + 2 ≤
      (a.order (3 : Fin (N + 5)) : ℚ) := by
    exact_mod_cast horders
  have hhalfShift : a.halfGapValue (0 : Fin (N + 4)) + 1 ≤
      a.halfGapValue (2 : Fin (N + 4)) := by
    unfold halfGapValue orderGap
    have hzeroSucc : (0 : Fin (N + 4)).succ =
        (1 : Fin (N + 5)) := by rfl
    have hzeroCast : (0 : Fin (N + 4)).castSucc =
        (0 : Fin (N + 5)) := by rfl
    have htwoSucc : (2 : Fin (N + 4)).succ =
        (3 : Fin (N + 5)) := by rfl
    have htwoCast : (2 : Fin (N + 4)).castSucc =
        (2 : Fin (N + 5)) := by rfl
    rw [hzeroSucc, hzeroCast, htwoSucc, htwoCast,
      ← profile.firstThird_eq]
    push_cast
    linarith [hordersQ]
  have hhalfBeta : ((A₁ + 2 : Int) : ℚ) ≤
      a.halfGapValue (2 : Fin (N + 4)) := by
    have hstepQ : ((A₁ + 1 : Int) : ℚ) ≤ (H : ℚ) := by
      exact_mod_cast hA₁Step
    calc
      ((A₁ + 2 : Int) : ℚ) = ((A₁ + 1 : Int) : ℚ) + 1 := by
        push_cast
        ring
      _ ≤ (H : ℚ) + 1 := by linarith
      _ = a.halfGapValue (0 : Fin (N + 4)) + 1 := by rw [hH]
      _ ≤ a.halfGapValue (2 : Fin (N + 4)) := hhalfShift
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict
      c hstrict
  have hthird : ((A₁ + 2 : Int) : ℚ) ≤
      a.alphaValue (2 : Fin (N + 4)) := by
    apply a.intCast_add_two_le_alphaValue_of_odd_of_lt_of_halfGap_le
      (2 : Fin (N + 4)) A₁ hA₁Odd
    · simpa only [← hA₁] using hthirdStrict
    · exact hhalfBeta
  refine ⟨A₁, hA₁, by omega, by omega, hthird, ?_⟩
  exact ⟨horders,
    beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict⟩

/-- In branch 4, choose `β₁ = α₁ + 1`. -/
theorem exists_beli2019Lemma912TypeIBetaData_of_halfGapIsotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hstrict :
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) <
        a.truncatedPrefixDefect c (-1) 3 1)
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4))) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaData a c A₁ (A₁ + 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A₁, hA₁⟩
  have hA₁TwoE : A₁ + 1 ≤ 2 * (ramificationIndex K : Int) := by
    have hbound := profile.firstGap_le_twoE_sub_two
    have hboundQ : (a.orderGap (0 : Fin (N + 4)) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by
      exact_mod_cast hbound
    have hhalfFormula := hhalf
    rw [hA₁] at hhalfFormula
    unfold halfGapValue at hhalfFormula
    have hcast : ((A₁ + 1 : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) := by
      push_cast at hhalfFormula ⊢
      linarith [hboundQ]
    exact_mod_cast hcast
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict
      c hstrict
  have hthird : ((A₁ + 1 : Int) : ℚ) ≤
      a.alphaValue (2 : Fin (N + 4)) := by
    apply a.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      (2 : Fin (N + 4)) A₁ hA₁TwoE
    simpa only [← hA₁] using hthirdStrict
  refine ⟨A₁, hA₁, by omega, by omega, hthird, ?_⟩
  exact ⟨
    a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
      c profile hstrict,
    beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict⟩

/-- In branch 5, choose `β₁ = α₁`. -/
theorem exists_beli2019Lemma912TypeIBetaData_of_halfGapAnisotropic
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
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaData a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A₁, hA₁⟩
  have hthirdStrict :=
    a.beli2019Lemma912_firstAlpha_lt_thirdAlpha_of_fullDefect_strict
      c hstrict
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_, ?_⟩
  · exact (show (A₁ : ℚ) ≤ a.alphaValue (2 : Fin (N + 4)) by
      rw [← hA₁]
      exact hthirdStrict.le)
  · exact ⟨
      a.beli2019Lemma912_fourthOrder_ge_add_two_of_fullDefect_strict
        c profile hstrict,
      beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
          a c profile hfirst hstrict⟩

/-- All four type-I branches supply a valid integer `β₁`; the remaining
branch is exactly the separate type-III parameter case. -/
theorem beli2019Lemma912_typeIIIParameters_or_exists_typeIBetaData
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5))) :
    Beli2019Lemma912TypeIIIParameters a c ∨
      ∃ A₁ β₁ : Int, Beli2019Lemma912TypeIBetaData a c A₁ β₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_parameterBranches c profile with
    ⟨_, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, hhalf, _⟩ |
    ⟨hstrict, _, _⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_equalSecondLarge
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hfirstAlpha hlarge with ⟨A₁, hdata⟩
    exact ⟨A₁, A₁, hdata⟩
  · left
    exact ⟨hfull, hfirstAlpha, hone⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_belowHalfGap
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict hbelow with ⟨A₁, hdata⟩
    exact ⟨A₁, A₁ + 2, hdata⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapIsotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict hhalf with ⟨A₁, hdata⟩
    exact ⟨A₁, A₁ + 1, hdata⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapAnisotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict with ⟨A₁, hdata⟩
    exact ⟨A₁, A₁, hdata⟩

end BONG.GoodBONG

end Bong
