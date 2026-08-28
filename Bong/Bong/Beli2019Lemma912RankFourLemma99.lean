/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankFourParameters

/-!
# Beli (2019), Lemma 9.12: quaternary Lemma 9.9 inputs

The four type-I choices only change the middle order of the initial ternary
reference.  This file verifies the shifted Lemma 9.9 conditions from the
literal quaternary residual profile.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {r : QuadraticSpace K W}
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W}

namespace Beli2019Lemma99Conditions

/-- Shifted conditions in the equal-alpha, large-second-alpha branch. -/
theorem ofEqualSecondLarge_rankFour
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (hR₁ : a.order (0 : Fin 4) = R₁)
    (hR₂ : a.order (1 : Fin 4) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 3) = (A₁ : ℚ))
    (hfirstAlpha : a.alphaValue (0 : Fin 3) = c.alphaValue (0 : Fin 3))
    (hlarge : 1 < a.alphaValue (1 : Fin 3)) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin 2) profile.firstThird_eq
  have hsourceFormula : a.alphaValue (0 : Fin 3) =
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) +
        a.alphaValue (1 : Fin 3) := by
    have h := hremark.previousAlpha_eq
    change a.alphaValue (0 : Fin 3) =
      ((a.order (1 : Fin 4) - a.order (2 : Fin 4) : Int) : ℚ) +
        a.alphaValue (1 : Fin 3) at h
    rwa [← profile.firstThird_eq] at h
  rw [hA₁, hR₁, hR₂] at hsourceFormula
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ := by
    have hltQ : ((R₂ - R₁ + 1 : Int) : ℚ) < (A₁ : ℚ) := by
      push_cast at hsourceFormula ⊢
      linarith
    have hlt : R₂ - R₁ + 1 < A₁ := by exact_mod_cast hltQ
    omega
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ :=
    max_le C.alpha_nonnegative hnewGap
  have hupper : (A₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    have holdUpper := C.upper
    push_cast at holdUpper ⊢
    linarith
  have hhalfLt : a.halfGapValue (0 : Fin 3) <
      c.halfGapValue (0 : Fin 3) := by
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
    rw [hsucc, hcast]
    rw [← hfirst]
    push_cast
    have hsecondQ : (a.order (1 : Fin 4) : ℚ) <
        (c.order (1 : Fin 4) : ℚ) := by
      exact_mod_cast profile.second_lt_sourceSecond
    linarith
  have htargetBelow : c.alphaValue (0 : Fin 3) <
      c.halfGapValue (0 : Fin 3) := by
    calc
      c.alphaValue (0 : Fin 3) = a.alphaValue (0 : Fin 3) := hfirstAlpha.symm
      _ ≤ a.halfGapValue (0 : Fin 3) :=
        a.alphaValue_le_halfGapValue (0 : Fin 3)
      _ < c.halfGapValue (0 : Fin 3) := hhalfLt
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  rcases c.beli2009Lemma27_iv (0 : Fin 3) (ne_of_lt htargetBelow) with
    ⟨z, hzOdd, hz⟩
  have hA₁Odd : Odd A₁ := by
    have hAz : A₁ = z := by
      exact_mod_cast hA₁.symm.trans (hfirstAlpha.trans hz)
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨p, hp⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- Shifted conditions in the below-half-gap branch. -/
theorem ofBelowHalfGap_rankFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 4) = R₁)
    (hR₂ : a.order (1 : Fin 4) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 3) = (A₁ : ℚ))
    (hbelow : a.alphaValue (0 : Fin 3) < a.halfGapValue (0 : Fin 3)) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) (A₁ + 2) := by
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ + 2 := by
    apply max_le
    · have := C.alpha_nonnegative
      omega
    · have := C.gap_le_alpha
      omega
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin 3) profile.firstGap_even with ⟨H, hH⟩
  have hA₁H : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← hA₁, ← hH] using hbelow)
  have hstep : A₁ + 2 ≤ H + 1 := by omega
  have hhalfFormula : (H : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    rw [← hH]
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
    rw [hsucc, hcast]
    rw [hR₁, hR₂]
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
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap_rankFour hbelow
  have hA₁Odd : Odd A₁ := by
    rcases hA₁OddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by exact_mod_cast hA₁.symm.trans hz
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨p, hp⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- Shifted conditions at an isotropic half-gap. -/
theorem ofHalfGapIsotropic_rankFour
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 4) = R₁)
    (hR₂ : a.order (1 : Fin 4) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 3) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin 3) = a.halfGapValue (0 : Fin 3))
    (hrefIsotropic : reference.Lemma814FirstThreeIsotropic) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) (A₁ + 1) := by
  have hgap : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 2 := by
    have hbound := profile.firstGap_le_twoE_sub_two
    unfold orderGap at hbound
    have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
    rw [hsucc, hcast, hR₁, hR₂] at hbound
    exact hbound
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 3) := hA₁.symm
      _ = a.halfGapValue (0 : Fin 3) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
        have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
        rw [hsucc, hcast, hR₁, hR₂]
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ + 1 := by
    have hgapQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by exact_mod_cast hgap
    have hnewGapQ : ((R₂ + 2 - R₁ : Int) : ℚ) ≤
        ((A₁ + 1 : Int) : ℚ) := by
      push_cast at hgapQ hhalfFormula ⊢
      linarith
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
  exact ⟨heq, hrefIsotropic⟩

/-- Shifted conditions at an anisotropic half-gap below the exceptional
boundary. -/
theorem ofHalfGapAnisotropic_rankFour
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin 4) = R₁)
    (hR₂ : a.order (1 : Fin 4) = R₂)
    (hA₁ : a.alphaValue (0 : Fin 3) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin 3) = a.halfGapValue (0 : Fin 3))
    (hgapSharp : a.orderGap (0 : Fin 3) ≤
      2 * (ramificationIndex K : Int) - 4)
    (hrefAnisotropic : reference.Lemma814FirstThreeAnisotropic) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) A₁ := by
  have hgap : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4 := by
    unfold orderGap at hgapSharp
    have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
    rw [hsucc, hcast, hR₁, hR₂] at hgapSharp
    exact hgapSharp
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin 3) := hA₁.symm
      _ = a.halfGapValue (0 : Fin 3) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        have hsucc : (0 : Fin 3).succ = (1 : Fin 4) := by rfl
        have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by rfl
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
  exact False.elim (reference.not_firstThreeIsotropic_of_anisotropic
    hrefAnisotropic hrefIsotropic)

end Beli2019Lemma99Conditions

end BONG.GoodBONG

end Bong
