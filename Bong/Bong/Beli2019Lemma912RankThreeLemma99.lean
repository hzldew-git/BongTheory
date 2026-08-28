/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankThreeParameters

/-!
# Beli (2019), Lemma 9.12: ternary Lemma 9.9 inputs

This file chooses the integer beta in each ternary type-I branch and checks
the shifted existence conditions of Lemma 9.9.  Only the initial ternary
invariants occur, so the statements have no artificial tail hypotheses.
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

/-- The numerical part of a ternary type-I choice. -/
structure Beli2019Lemma912TypeIBetaDataRankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (A₁ β₁ : Int) : Prop where
  firstAlpha : a.alphaValue (0 : Fin 2) = (A₁ : ℚ)
  betaLower : A₁ ≤ β₁
  betaUpper : β₁ ≤ A₁ + 2
  sourceSecondOrder : a.order (1 : Fin 3) + 2 ≤ c.order (1 : Fin 3)

/-- The equal-alpha large-second-alpha branch uses `β₁ = A₁`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankThree_of_equalSecondLarge
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hfirstAlpha : a.alphaValue (0 : Fin 2) = c.alphaValue (0 : Fin 2))
    (hlarge : 1 < a.alphaValue (1 : Fin 2)) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaDataRankThree a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankThree c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_⟩
  exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_secondAlpha_large_rankThree
    (alphaV := alphaV) (alphaW := alphaW) a c profile hfirst hfirstAlpha hlarge

/-- The below-half-gap branch uses `β₁ = A₁ + 2`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankThree_of_belowHalfGap
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    ∃ A₁ : Int,
      Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankThree c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, by omega, by omega, ?_⟩
  exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankThree
    (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict

/-- The isotropic half-gap branch uses `β₁ = A₁ + 1`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankThree_of_halfGapIsotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    ∃ A₁ : Int,
      Beli2019Lemma912TypeIBetaDataRankThree a c A₁ (A₁ + 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankThree c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, by omega, by omega, ?_⟩
  exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankThree
    (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict

/-- The anisotropic half-gap branch uses `β₁ = A₁`. -/
theorem exists_beli2019Lemma912TypeIBetaDataRankThree_of_halfGapAnisotropic
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hstrict : (a.alphaValue (0 : Fin 2) : WithTop ℚ) <
      a.truncatedPrefixDefect c (-1) 3 1) :
    ∃ A₁ : Int, Beli2019Lemma912TypeIBetaDataRankThree a c A₁ A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral_rankThree c profile with ⟨A₁, hA₁⟩
  refine ⟨A₁, hA₁, le_rfl, by omega, ?_⟩
  exact beli2019Lemma912_sourceSecondOrder_ge_add_two_of_fullDefect_strict_rankThree
    (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict

namespace Beli2019Lemma99Conditions

/-- Shifted Lemma 9.9 conditions in the equal-alpha large-second-alpha
ternary branch. -/
theorem ofEqualSecondLarge_rankThree
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions a R₁ R₂ A₁)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (hR₁ : a.order (0 : Fin 3) = R₁)
    (hR₂ : a.order (1 : Fin 3) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hfirstAlpha : a.alphaValue (0 : Fin 2) = c.alphaValue (0 : Fin 2))
    (hlarge : 1 < a.alphaValue (1 : Fin 2)) :
    Beli2019Lemma99Conditions a R₁ (R₂ + 2) A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin 1) profile.firstThird_eq
  have hsourceFormula : a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) := by
    have h := hremark.previousAlpha_eq
    change a.alphaValue (0 : Fin 2) =
      ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
        a.alphaValue (1 : Fin 2) at h
    rwa [← profile.firstThird_eq] at h
  rw [hA₁, hR₁, hR₂] at hsourceFormula
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ := by
    have hltQ : ((R₂ - R₁ + 1 : Int) : ℚ) < (A₁ : ℚ) := by
      push_cast at hsourceFormula ⊢
      linarith
    have hlt : R₂ - R₁ + 1 < A₁ := by exact_mod_cast hltQ
    omega
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ := by
    exact max_le C.alpha_nonnegative hnewGap
  have hupper : (A₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    have holdUpper := C.upper
    push_cast at holdUpper ⊢
    linarith
  have hhalfLt : a.halfGapValue (0 : Fin 2) <
      c.halfGapValue (0 : Fin 2) := by
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
    rw [hsucc, hcast, ← hfirst]
    push_cast
    have hsecondQ : (a.order (1 : Fin 3) : ℚ) <
        (c.order (1 : Fin 3) : ℚ) := by
      exact_mod_cast profile.second_lt_sourceSecond
    linarith
  have htargetBelow : c.alphaValue (0 : Fin 2) <
      c.halfGapValue (0 : Fin 2) := by
    calc
      c.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 2) := hfirstAlpha.symm
      _ ≤ a.halfGapValue (0 : Fin 2) :=
        a.alphaValue_le_halfGapValue (0 : Fin 2)
      _ < c.halfGapValue (0 : Fin 2) := hhalfLt
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  rcases c.beli2009Lemma27_iv (0 : Fin 2) (ne_of_lt htargetBelow) with
    ⟨z, hzOdd, hz⟩
  have hA₁Odd : Odd A₁ := by
    have hAz : A₁ = z := by
      exact_mod_cast hA₁.symm.trans (hfirstAlpha.trans hz)
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨s, hs⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- Shifted Lemma 9.9 conditions in the strict below-half-gap ternary
branch. -/
theorem ofBelowHalfGap_rankThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions a R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 3) = R₁)
    (hR₂ : a.order (1 : Fin 3) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hbelow : a.alphaValue (0 : Fin 2) < a.halfGapValue (0 : Fin 2)) :
    Beli2019Lemma99Conditions a R₁ (R₂ + 2) (A₁ + 2) := by
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ + 2 := by
    apply max_le
    · have hnonnegative := C.alpha_nonnegative
      omega
    · have := C.gap_le_alpha
      omega
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin 2) profile.firstGap_even with ⟨H, hH⟩
  have hA₁H : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← hA₁, ← hH] using hbelow)
  have hstep : A₁ + 2 ≤ H + 1 := by omega
  have hhalfFormula : (H : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    rw [← hH]
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
    rw [hsucc, hcast, hR₁, hR₂]
  have hupper : ((A₁ + 2 : Int) : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    have hstepQ : ((A₁ + 2 : Int) : ℚ) ≤ ((H + 1 : Int) : ℚ) := by
      exact_mod_cast hstep
    push_cast at hstepQ
    rw [hhalfFormula] at hstepQ
    push_cast at hstepQ ⊢
    ring_nf at hstepQ ⊢
    exact hstepQ
  have hA₁OddRational :=
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankThree hbelow
  have hA₁Odd : Odd A₁ := by
    rcases hA₁OddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by exact_mod_cast hA₁.symm.trans hz
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨s, hs⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- Shifted Lemma 9.9 conditions at the isotropic half-gap. -/
theorem ofHalfGapIsotropic_rankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions a R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 3) = R₁)
    (hR₂ : a.order (1 : Fin 3) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin 2) = a.halfGapValue (0 : Fin 2))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    Beli2019Lemma99Conditions a R₁ (R₂ + 2) (A₁ + 1) := by
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 2) := hA₁.symm
      _ = a.halfGapValue (0 : Fin 2) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
        have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
        rw [hsucc, hcast, hR₁, hR₂]
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ + 1 := by
    have hnewGapQ : ((R₂ + 2 - R₁ : Int) : ℚ) ≤
        ((A₁ + 1 : Int) : ℚ) := by
      have hgap : (R₂ - R₁ : Int) ≤
          2 * (ramificationIndex K : Int) - 2 := by
        have hbound := profile.firstGap_le_twoE_sub_two
        unfold orderGap at hbound
        have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
        have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
        rw [hsucc, hcast, hR₁, hR₂] at hbound
        exact hbound
      have hgapQ : ((R₂ - R₁ : Int) : ℚ) ≤
          2 * (ramificationIndex K : ℚ) - 2 := by
        exact_mod_cast hgap
      push_cast at hgapQ hhalfFormula ⊢
      linarith [hgapQ]
    exact_mod_cast hnewGapQ
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ + 1 := by
    apply max_le
    · have := C.alpha_nonnegative
      omega
    · exact hnewGap
  have heq : ((A₁ + 1 : Int) : ℚ) =
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    push_cast at hhalfFormula ⊢
    ring_nf at hhalfFormula ⊢
    linarith
  apply C.shiftMiddleByTwo hlower heq.le
  intro _
  exact ⟨heq, hisotropic⟩

/-- Shifted Lemma 9.9 conditions at an anisotropic half-gap, provided the
gap is below the exceptional `2e-2` endpoint. -/
theorem ofHalfGapAnisotropic_rankThree
    (a : GoodBONG q L 3) (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions a R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 3) = R₁)
    (hR₂ : a.order (1 : Fin 3) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin 2) = a.halfGapValue (0 : Fin 2))
    (hgapSharp : a.orderGap (0 : Fin 2) ≤
      2 * (ramificationIndex K : Int) - 4)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    Beli2019Lemma99Conditions a R₁ (R₂ + 2) A₁ := by
  have hgap : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4 := by
    unfold orderGap at hgapSharp
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
    rw [hsucc, hcast, hR₁, hR₂] at hgapSharp
    exact hgapSharp
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 2) := hA₁.symm
      _ = a.halfGapValue (0 : Fin 2) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := by rfl
        have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := by rfl
        rw [hsucc, hcast, hR₁, hR₂]
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ := by
    have hgapQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 4 := by exact_mod_cast hgap
    have hnewGapQ : ((R₂ + 2 - R₁ : Int) : ℚ) ≤ (A₁ : ℚ) := by
      push_cast at hgapQ hhalfFormula ⊢
      linarith
    exact_mod_cast hnewGapQ
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ :=
    max_le C.alpha_nonnegative hnewGap
  have hupper : (A₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    push_cast at hhalfFormula ⊢
    linarith
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  have hrefIsotropic := (C.evenBoundary hEven).2
  exact False.elim (a.not_firstThreeIsotropic_of_anisotropic
    hanisotropic hrefIsotropic)

end Beli2019Lemma99Conditions

end BONG.GoodBONG

end Bong
