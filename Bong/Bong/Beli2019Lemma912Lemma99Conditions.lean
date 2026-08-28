/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912BetaChoices
import Bong.Bong.Beli2019Lemma99Necessity

/-!
# Beli (2019), Lemma 9.12: the modified Lemma 9.9 conditions

This file verifies the numerical existence conditions for the four type-I
choices of the first alpha parameter used in the proof of Lemma 9.12.
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
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W} {N : Nat}

namespace Beli2019Lemma99Realization

/-- Regard a reference ternary good BONG with specified invariants as a
literal Lemma 9.9 realization. -/
noncomputable def ofReference
    (reference : GoodBONG q L 3) (R₁ R₂ A₁ : Int)
    (horders : ∀ i : Fin 3, reference.order i = ![R₁, R₂, R₁] i)
    (hfirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ)) :
    Beli2019Lemma99Realization (q := q) R₁ R₂ R₁ A₁ where
  lattice := L
  bong := reference
  orders := horders
  firstAlpha := hfirstAlpha

end Beli2019Lemma99Realization

namespace Beli2019Lemma99Conditions

/-- Adding two to the middle order preserves the parity and determinant
conditions; the three changed interval conditions are supplied explicitly. -/
theorem shiftMiddleByTwo
    {reference : GoodBONG q L 3} {R₁ R₂ A₁ β₁ : Int}
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hlower : max 0 (R₂ + 2 - R₁) ≤ β₁)
    (hupper : (β₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (heven : Even β₁ →
      (β₁ : ℚ) =
          ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K ∧
        reference.Lemma814FirstThreeIsotropic) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁ := by
  refine {
    orderParity := ?_
    determinantOrder := C.determinantOrder
    lower := by simpa only [add_sub_assoc] using hlower
    upper := by simpa only [add_sub_assoc] using hupper
    evenBoundary := ?_ }
  · have hparity := C.orderParity
    rw [Int.modEq_iff_dvd] at hparity ⊢
    rcases hparity with ⟨z, hz⟩
    exact ⟨z + 1, by omega⟩
  · intro hβ
    simpa only [add_sub_assoc] using heven hβ

/-- The shifted Lemma 9.9 conditions for branch 1, where
`β₁ = α₁` and the second source alpha is strictly larger than one. -/
theorem ofEqualSecondLarge
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hR₁ : a.order (0 : Fin (N + 5)) = R₁)
    (hR₂ : a.order (1 : Fin (N + 5)) = R₂)
    (hA₁ : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hfirstAlpha : a.alphaValue (0 : Fin (N + 4)) =
      c.alphaValue (0 : Fin (N + 4)))
    (hlarge : 1 < a.alphaValue (1 : Fin (N + 4))) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) A₁ := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  let p : Fin (N + 3) := ⟨0, by omega⟩
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
        a.order (0 : Fin (N + 5)) : Int) : ℚ) +
        a.alphaValue (1 : Fin (N + 4)) := by
    have h := hremark.previousAlpha_eq
    rw [hpPreviousAlpha, hpCurrentAlpha, hpMiddleValue, hpNextValue] at h
    rw [← profile.firstThird_eq] at h
    exact h
  rw [hA₁, hR₁, hR₂] at hsourceFormula
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ := by
    have hltQ : ((R₂ - R₁ + 1 : Int) : ℚ) < (A₁ : ℚ) := by
      push_cast at hsourceFormula ⊢
      linarith
    have hlt : R₂ - R₁ + 1 < A₁ := by
      exact_mod_cast hltQ
    omega
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ := by
    apply max_le
    · exact C.alpha_nonnegative
    · exact hnewGap
  have hupper : (A₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    have holdUpper := C.upper
    push_cast at holdUpper ⊢
    linarith
  have hsucc : (0 : Fin (N + 4)).succ =
      (1 : Fin (N + 5)) := by rfl
  have hcast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  have hhalfLt : a.halfGapValue (0 : Fin (N + 4)) <
      c.halfGapValue (0 : Fin (N + 4)) := by
    unfold halfGapValue orderGap
    rw [hsucc, hcast]
    rw [← hfirst]
    push_cast
    have hsecond := profile.second_lt_sourceSecond
    have hsecondQ : (a.order (1 : Fin (N + 5)) : ℚ) <
        (c.order (1 : Fin (N + 5)) : ℚ) := by
      exact_mod_cast hsecond
    linarith
  have htargetBelow : c.alphaValue (0 : Fin (N + 4)) <
      c.halfGapValue (0 : Fin (N + 4)) := by
    calc
      c.alphaValue (0 : Fin (N + 4)) =
          a.alphaValue (0 : Fin (N + 4)) := hfirstAlpha.symm
      _ ≤ a.halfGapValue (0 : Fin (N + 4)) :=
        a.alphaValue_le_halfGapValue (0 : Fin (N + 4))
      _ < c.halfGapValue (0 : Fin (N + 4)) := hhalfLt
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  rcases c.beli2009Lemma27_iv (0 : Fin (N + 4))
      (ne_of_lt htargetBelow) with ⟨z, hzOdd, hz⟩
  have hA₁Odd : Odd A₁ := by
    have hAz : A₁ = z := by
      exact_mod_cast hA₁.symm.trans (hfirstAlpha.trans hz)
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨s, hs⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- The shifted Lemma 9.9 conditions for branch 3, where
`β₁ = α₁ + 2` and `α₁` lies below its half-gap. -/
theorem ofBelowHalfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin (N + 5)) = R₁)
    (hR₂ : a.order (1 : Fin (N + 5)) = R₂)
    (hA₁ : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hbelow : a.alphaValue (0 : Fin (N + 4)) <
      a.halfGapValue (0 : Fin (N + 4))) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) (A₁ + 2) := by
  have hA₁Nonnegative := C.alpha_nonnegative
  have hgapA₁ := C.gap_le_alpha
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ + 2 := by
    apply max_le
    · omega
    · omega
  rcases a.halfGapValue_isRationalInteger_of_even
      (0 : Fin (N + 4)) profile.firstGap_even with ⟨H, hH⟩
  have hA₁H : A₁ < H := by
    exact_mod_cast (show (A₁ : ℚ) < (H : ℚ) by
      simpa only [← hA₁, ← hH] using hbelow)
  have hstep : A₁ + 2 ≤ H + 1 := by omega
  have hhalfFormula : (H : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    rw [← hH]
    unfold halfGapValue orderGap
    have hsucc : (0 : Fin (N + 4)).succ =
        (1 : Fin (N + 5)) := by rfl
    have hcast : (0 : Fin (N + 4)).castSucc =
        (0 : Fin (N + 5)) := by rfl
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
    a.beli2019Lemma912_firstAlpha_odd_of_below_halfGap hbelow
  have hA₁Odd : Odd A₁ := by
    rcases hA₁OddRational with ⟨z, hzOdd, hz⟩
    have hAz : A₁ = z := by
      exact_mod_cast hA₁.symm.trans hz
    simpa only [hAz] using hzOdd
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  rcases hA₁Odd with ⟨s, hs⟩
  rcases hEven with ⟨t, ht⟩
  omega

/-- The shifted Lemma 9.9 conditions for branch 4, where
`β₁ = α₁ + 1`, the first alpha is at its half-gap, and the reference
ternary space is isotropic. -/
theorem ofHalfGapIsotropic
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin (N + 5)) = R₁)
    (hR₂ : a.order (1 : Fin (N + 5)) = R₂)
    (hA₁ : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4)))
    (hrefIsotropic : reference.Lemma814FirstThreeIsotropic) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) (A₁ + 1) := by
  have hsucc : (0 : Fin (N + 4)).succ =
      (1 : Fin (N + 5)) := by rfl
  have hcast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  have hgap : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 2 := by
    have hbound := profile.firstGap_le_twoE_sub_two
    unfold orderGap at hbound
    rw [hsucc, hcast, hR₁, hR₂] at hbound
    exact hbound
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin (N + 4)) := hA₁.symm
      _ = a.halfGapValue (0 : Fin (N + 4)) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        rw [hsucc, hcast, hR₁, hR₂]
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ + 1 := by
    have hgapQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 2 := by
      exact_mod_cast hgap
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

/-- The shifted Lemma 9.9 conditions for branch 5, where
`β₁ = α₁`, the first alpha is at its half-gap, and the reference ternary
space is anisotropic. -/
theorem ofHalfGapAnisotropic
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5))
    (R₁ R₂ A₁ : Int)
    (C : Beli2019Lemma99Conditions reference R₁ R₂ A₁)
    (hR₁ : a.order (0 : Fin (N + 5)) = R₁)
    (hR₂ : a.order (1 : Fin (N + 5)) = R₂)
    (hA₁ : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hhalf : a.alphaValue (0 : Fin (N + 4)) =
      a.halfGapValue (0 : Fin (N + 4)))
    (hgapSharp : a.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) - 4)
    (hrefAnisotropic : reference.Lemma814FirstThreeAnisotropic) :
    Beli2019Lemma99Conditions reference R₁ (R₂ + 2) A₁ := by
  have hsucc : (0 : Fin (N + 4)).succ =
      (1 : Fin (N + 5)) := by rfl
  have hcast : (0 : Fin (N + 4)).castSucc =
      (0 : Fin (N + 5)) := by rfl
  have hgap : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4 := by
    unfold orderGap at hgapSharp
    rw [hsucc, hcast, hR₁, hR₂] at hgapSharp
    exact hgapSharp
  have hhalfFormula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    calc
      (A₁ : ℚ) = a.alphaValue (0 : Fin (N + 4)) := hA₁.symm
      _ = a.halfGapValue (0 : Fin (N + 4)) := hhalf
      _ = ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
        unfold halfGapValue orderGap
        rw [hsucc, hcast, hR₁, hR₂]
  have hnewGap : R₂ + 2 - R₁ ≤ A₁ := by
    have hgapQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 4 := by
      exact_mod_cast hgap
    have hnewGapQ : ((R₂ + 2 - R₁ : Int) : ℚ) ≤ (A₁ : ℚ) := by
      push_cast at hgapQ hhalfFormula ⊢
      linarith
    exact_mod_cast hnewGapQ
  have hlower : max 0 (R₂ + 2 - R₁) ≤ A₁ := by
    apply max_le
    · exact C.alpha_nonnegative
    · exact hnewGap
  have hupper : (A₁ : ℚ) ≤
      ((R₂ + 2 - R₁ : Int) : ℚ) / 2 + ramificationIndex K := by
    push_cast at hhalfFormula ⊢
    linarith
  apply C.shiftMiddleByTwo hlower hupper
  intro hEven
  have hrefIsotropic := (C.evenBoundary hEven).2
  exact False.elim (reference.not_firstThreeIsotropic_of_anisotropic
    hrefAnisotropic hrefIsotropic)

/-- A reference ternary good BONG with the required orders and first alpha
supplies the unshifted Lemma 9.9 conditions without a paper-specific law. -/
theorem ofReferenceInvariants
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (reference : GoodBONG q L 3) (R₁ R₂ A₁ : Int)
    (horders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hfirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ)) :
    Beli2019Lemma99Conditions reference R₁ R₂ A₁ := by
  let D := Beli2019Lemma99Realization.ofReference
    reference R₁ R₂ A₁ horders hfirstAlpha
  exact beli2019Lemma99_necessity reference R₁ R₂ R₁ A₁ rfl D

end Beli2019Lemma99Conditions

end BONG.GoodBONG

end Bong
