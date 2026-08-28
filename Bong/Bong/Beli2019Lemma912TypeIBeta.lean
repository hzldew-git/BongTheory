/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIAlpha
import Bong.Bong.Beli2019Lemma69RightTailMinimum
import Bong.Bong.Beli2019Remark87

/-!
# Beli (2019), Lemma 9.12: condition (ii) in the type-I claim

This file derives the exact formula for the target alpha values in the type-I
construction and proves that the ordinary representation-defect condition is
equivalent to the two scalar requirements appearing in the claim of Lemma 9.12.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

namespace Beli2019Lemma910Data

/-- The first three target orders are exactly the entries prescribed by the construction. -/
@[simp]
theorem order_castLength_prefix
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) (i : Fin 3) :
    (E.bong.castLength hlength).order (⟨i.val, by omega⟩ : Fin (N + 3)) =
      D.bong.order i := by
  rw [GoodBONG.order_castLength]
  have hi : (⟨i.val, by omega⟩ : Fin (3 + N)) = Fin.castAdd N i := by
    apply Fin.ext
    rfl
  rw [hi]
  exact E.order_castAdd a D i

/-- In the type-I construction the first and third target orders coincide. -/
theorem firstThirdOrder_eq
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) :
    (E.bong.castLength hlength).order (⟨0, by omega⟩ : Fin (N + 3)) =
      (E.bong.castLength hlength).order
        (⟨2, by omega⟩ : Fin (N + 3)) := by
  rw [show (⟨0, by omega⟩ : Fin (N + 3)) =
        ⟨(0 : Fin 3).val, by omega⟩ by
      apply Fin.ext
      simp,
    show (⟨2, by omega⟩ : Fin (N + 3)) =
        ⟨(2 : Fin 3).val, by omega⟩ by
      apply Fin.ext
      simp,
    E.order_castLength_prefix a D hlength,
    E.order_castLength_prefix a D hlength, D.order_zero, D.order_two]

/-- The exact formula `βᵢ = min {αᵢ, Sᵢ₊₁ - S₂ + β₁}` for every `i ≥ 2`. -/
theorem alphaValue_eq_min_sourceAlpha_shift
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    (E.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have := i.lt_large; omega⟩ =
      min ((a.castLength hlength).alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩)
        (((((E.bong.castLength hlength).order
            ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) :
            ℚ)) + (β₁ : ℚ)) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let first : Fin (N + 2) := ⟨1, by omega⟩
  let j : Fin (N + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have horder := E.representationOrderCondition a D horders hlength
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < N + 3 →
      source.orderSequence.entryOrZero k =
        target.orderSequence.entryOrZero k := by
    intro k hk hkr
    rw [BeliOrderSequence.entryOrZero_of_lt source.orderSequence hkr,
      BeliOrderSequence.entryOrZero_of_lt target.orderSequence hkr]
    exact (E.order_castLength_eq_source_of_two_le a D horders hlength
      ⟨k, hkr⟩ (by simpa [first] using hk)).symm
  have hformula := beli2019Lemma69_iv_beta_eq_min source target
    horder hdefect first j (by
      change 1 ≤ i.val - 1
      omega) hsuffix
  have houter := E.firstThirdOrder_eq a D hlength
  let p : Fin (N + 1) := ⟨0, by omega⟩
  have hremark := target.beli2019Remark87 p (by
    simpa only [target, p, remark87PreviousValue, remark87NextValue]
      using houter)
  have hjSucc : j.succ = (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp [j]
    omega
  have hfirstSucc : first.succ = (⟨2, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hformula, hjSucc, hfirstSucc]
  congr 1
  have hfirstEq : first = remark87CurrentAlpha p := by
    apply Fin.ext
    rfl
  rw [hfirstEq, hremark.currentAlpha_eq]
  have hfirstAlpha :
      target.alphaValue (remark87PreviousAlpha p) =
        (β₁ : ℚ) := by
    have hindex : remark87PreviousAlpha p = (0 : Fin (N + 2)) := by
      apply Fin.ext
      simp [p, remark87PreviousAlpha]
    rw [hindex]
    exact E.firstAlpha
  rw [hfirstAlpha]
  simp only [p, remark87PreviousValue, remark87MiddleValue]
  rw [← houter]
  push_cast
  ring

/-- The first target alpha value is bounded above by the third target alpha value. -/
theorem firstAlpha_le_thirdAlpha
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3) (hN : 0 < N) :
    (E.bong.castLength hlength).alphaValue
        (⟨0, by omega⟩ : Fin (N + 2)) ≤
      (E.bong.castLength hlength).alphaValue
        (⟨2, by omega⟩ : Fin (N + 2)) := by
  let target := E.bong.castLength hlength
  let first : Fin (N + 2) := ⟨0, by omega⟩
  let third : Fin (N + 2) := ⟨2, by omega⟩
  have hmono := target.alphaLeftEndpoint_monotone
    (show first ≤ third by simp [first, third])
  have houter := E.firstThirdOrder_eq a D hlength
  unfold alphaLeftEndpoint at hmono
  have hfirstCast : first.castSucc = (⟨0, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hthirdCast : third.castSucc = (⟨2, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hfirstCast, hthirdCast, houter] at hmono
  dsimp only [target, first, third] at hmono ⊢
  linarith

/-- The first mixed target defect inequality is equivalent to the full source-prefix inequality. -/
theorem firstMixedDefect_iff_sourceFull
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hN : 0 < N) :
    ((β₁ : ℚ) : WithTop ℚ) ≤
        (E.bong.castLength hlength).truncatedPrefixDefect c 1 1 1 ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
        (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let p : Fin (N + 1) := ⟨0, by omega⟩
  have houter := E.firstThirdOrder_eq a D hlength
  have hremark := target.beli2019Remark87 p (by
    simpa only [target, p, remark87PreviousValue, remark87NextValue]
      using houter)
  have hprevious : remark87PreviousAlpha p = (0 : Fin (N + 2)) := by
    apply Fin.ext
    simp [p, remark87PreviousAlpha]
  have hself : target.truncatedPrefixDefect target (-1) 1 3 =
      ((β₁ : ℚ) : WithTop ℚ) := by
    have h := hremark.currentCappedDefect_eq
    rw [hprevious, E.firstAlpha] at h
    simpa only [p] using h
  have hselfReverse : target.truncatedPrefixDefect target (-1) 3 1 =
      ((β₁ : ℚ) : WithTop ℚ) := by
    rw [target.truncatedPrefixDefect_comm target (-1) 3 1]
    exact hself
  have hforward : ((β₁ : ℚ) : WithTop ℚ) ≤
      target.truncatedPrefixDefect c 1 1 1 →
      ((β₁ : ℚ) : WithTop ℚ) ≤
        target.truncatedPrefixDefect c (-1) 3 1 := by
    intro hshort
    have hdom := target.truncatedPrefixDefect_domination
      target c (-1) 1 3 1 1
    have hdom' : min (target.truncatedPrefixDefect target (-1) 3 1)
        (target.truncatedPrefixDefect c 1 1 1) ≤
          target.truncatedPrefixDefect c (-1) 3 1 := by
      simpa using hdom
    exact (le_min (le_of_eq hselfReverse.symm) hshort).trans hdom'
  have hreverse : ((β₁ : ℚ) : WithTop ℚ) ≤
      target.truncatedPrefixDefect c (-1) 3 1 →
      ((β₁ : ℚ) : WithTop ℚ) ≤
        target.truncatedPrefixDefect c 1 1 1 := by
    intro hfull
    have hdom := target.truncatedPrefixDefect_domination
      target c (-1) (-1) 1 3 1
    have h := (le_min (le_of_eq hself.symm) hfull).trans hdom
    simpa using h
  let third : RepresentationIndex (N + 3) (N + 3) := {
    val := 3
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hmixed := E.mixedPrefixDefect_eq_min
    a c D horders hlength hdefect third (by simp [third]) (-1) 1
  have hfirstThird := E.firstAlpha_le_thirdAlpha a D hlength hN
  have hbetaThird : ((β₁ : ℚ) : WithTop ℚ) ≤
      (target.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
    have hfirstIndex : (⟨0, by omega⟩ : Fin (N + 2)) =
        (0 : Fin (N + 2)) := by
      apply Fin.ext
      simp
    rw [hfirstIndex, E.firstAlpha] at hfirstThird
    exact_mod_cast hfirstThird
  constructor
  · intro hshort
    have hfull := hforward hshort
    rw [hmixed] at hfull
    exact hfull.trans (min_le_left _ _)
  · intro hsource
    apply hreverse
    rw [hmixed]
    exact le_min hsource hbetaThird

/-- For indices at least two, the target defect condition reduces to the shifted scalar bound. -/
theorem representationDefectAt_iff_shift
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hac : (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (E.bong.castLength hlength).truncatedPrefixDefect
          c 1 i.val i.val ↔
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        (((((E.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (E.bong.castLength hlength).order
              (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (β₁ : ℚ) : ℚ) : WithTop ℚ) := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hmixed := E.mixedPrefixDefect_eq_min
    a c D horders hlength hdefect i hi 1 i.val
  have hcomparison := E.representationAlpha_le_source
    a c D horders hlength hdefect i hi
  have hacAt : source.representationAlpha c i ≤
      source.truncatedPrefixDefect c 1 i.val i.val := by
    simpa only [← source.coe_representationAlphaValue c i] using hac i
  have hold : target.representationAlpha c i ≤
      source.truncatedPrefixDefect c 1 i.val i.val :=
    hcomparison.trans hacAt
  have hsourceAlpha : target.representationAlpha c i ≤
      (source.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : WithTop ℚ) :=
    hcomparison.trans (source.representationAlpha_le_leftAlpha c hac i)
  have htail := E.alphaValue_eq_min_sourceAlpha_shift
    a D horders hlength hdefect i hi
  have htailTop :
      (target.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : WithTop ℚ) =
        min (source.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ : WithTop ℚ)
          ((((target.order ⟨i.val, i.lt_large⟩ -
              target.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
            (β₁ : ℚ) : ℚ) : WithTop ℚ) := by
    exact_mod_cast htail
  rw [target.coe_representationAlphaValue, hmixed, htailTop]
  constructor
  · intro h
    exact (h.trans (min_le_right _ _)).trans (min_le_right _ _)
  · intro hshift
    exact le_min hold (le_min hsourceAlpha hshift)

/-- The first target defect condition reduces to the full source-prefix scalar condition. -/
theorem representationDefectAt_first_iff_sourceFull
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (hN : 0 < N) :
    let first := firstRepresentationIndex (N + 1) (N + 2)
    ((E.bong.castLength hlength).representationAlphaValue c first :
          WithTop ℚ) ≤
        (E.bong.castLength hlength).truncatedPrefixDefect
          c 1 first.val first.val ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
        (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let zero : Fin 3 := ⟨0, by omega⟩
  have htargetZero : target.order (⟨0, by omega⟩ : Fin (N + 3)) = R₁ := by
    have h := E.order_castLength_prefix a D hlength zero
    have hzero : zero = (0 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, D.order_zero] at h
    simpa [target, zero] using h
  have hsourceZero : source.order (⟨0, by omega⟩ : Fin (N + 3)) = R₁ := by
    rw [GoodBONG.order_castLength]
    have hindex : (⟨0, by omega⟩ : Fin (3 + N)) =
        Fin.castAdd N zero := by
      apply Fin.ext
      rfl
    rw [hindex, horders zero]
    rfl
  have htargetFirst : target.order (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)) :=
    htargetZero.trans (hsourceZero.symm.trans hfirst)
  let first := firstRepresentationIndex (N + 1) (N + 2)
  have halpha : target.representationAlpha c first =
      (target.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    exact target.beli2019Lemma812_i c htargetFirst
  change (target.representationAlphaValue c first : WithTop ℚ) ≤
      target.truncatedPrefixDefect c 1 first.val first.val ↔ _
  rw [target.coe_representationAlphaValue, halpha, E.firstAlpha]
  simpa only [first, firstRepresentationIndex, source, target] using
    E.firstMixedDefect_iff_sourceFull
      a c D horders hlength hdefect hN

private theorem representationIndex_eq_of_val_eq_912
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- Condition (ii) is equivalent to the two scalar conditions in the type-I claim. -/
theorem representationDefectCondition_iff_scalar
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (hac : (a.castLength hlength).RepresentationDefectCondition c)
    (hfirst : (a.castLength hlength).order
        (⟨0, by omega⟩ : Fin (N + 3)) =
      c.order (⟨0, by omega⟩ : Fin (N + 3)))
    (hN : 0 < N) :
    (E.bong.castLength hlength).RepresentationDefectCondition c ↔
      ((β₁ : ℚ) : WithTop ℚ) ≤
          (a.castLength hlength).truncatedPrefixDefect c (-1) 3 1 ∧
        ∀ i : RepresentationIndex (N + 3) (N + 3), 2 ≤ i.val →
          ((E.bong.castLength hlength).representationAlphaValue c i :
              WithTop ℚ) ≤
            (((((E.bong.castLength hlength).order
                  ⟨i.val, i.lt_large⟩ -
                (E.bong.castLength hlength).order
                  (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
              (β₁ : ℚ) : ℚ) : WithTop ℚ) := by
  let first := firstRepresentationIndex (N + 1) (N + 2)
  constructor
  · intro hbc
    refine ⟨?_, ?_⟩
    · apply (E.representationDefectAt_first_iff_sourceFull
        a c D horders hlength hdefect hfirst hN).mp
      exact hbc first
    · intro i hi
      apply (E.representationDefectAt_iff_shift
        a c D horders hlength hdefect hac i hi).mp
      exact hbc i
  · rintro ⟨hfirstScalar, hlater⟩ i
    by_cases hiFirst : i.val = 1
    · have hieq : i = first := by
        apply representationIndex_eq_of_val_eq_912
        simpa only [first, firstRepresentationIndex] using hiFirst
      subst i
      apply (E.representationDefectAt_first_iff_sourceFull
        a c D horders hlength hdefect hfirst hN).mpr
      exact hfirstScalar
    · have hiTwo : 2 ≤ i.val := by
        have := i.pos
        omega
      apply (E.representationDefectAt_iff_shift
        a c D horders hlength hdefect hac i hiTwo).mpr
      exact hlater i hiTwo

end Beli2019Lemma910Data

end BONG.GoodBONG

end Bong
