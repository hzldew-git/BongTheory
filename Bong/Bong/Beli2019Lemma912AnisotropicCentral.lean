/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicFinal

/-!
# Beli (2019), Lemma 9.12: anisotropic central trigger

This file formalizes the v2 argument producing the top prefix representation
at a nonterminal scalar-failure index.  The next essential order crossing
forces the following source alpha strictly above its complementary threshold;
capped-defect domination then verifies the central condition (iii').  The
terminal full-prefix case is handled directly by the ambient representation.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {Q : Lattice K U} {N : Nat}

theorem attainsHalfGap_of_alphaValue_eq_int_even
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (k : Fin (N + 2)) (A : Int)
    (hA : a.alphaValue k = (A : ℚ)) (hEven : Even A) :
    a.AttainsHalfGap k := by
  unfold AttainsHalfGap
  by_contra hne
  rcases a.beli2009Lemma27_iv k hne with ⟨z, hzOdd, hz⟩
  have hAz : A = z := by
    exact_mod_cast hA.symm.trans hz
  subst z
  exact (Int.not_odd_iff_even.mpr hEven) hzOdd

theorem sourceNextAlpha_ge_failureThreshold
    {A₁ : Int}
    (source : GoodBONG q L (N + 3))
    (c : GoodBONG r M (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (T : Beli2019Lemma912TopMixedDefectBounds source c A₁ i) :
    ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) ≤
      source.alphaValue ⟨i.val, by omega⟩ := by
  have htop := T.shifted.trans
    (source.truncatedPrefixDefect_le_leftCap c (-1)
      (i.val + 1) (i.val - 1))
  rw [source.prefixAlphaCap_of_internal (by omega) hinterior] at htop
  have hindex : (⟨i.val + 1 - 1, by omega⟩ : Fin (N + 2)) =
      ⟨i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega
  rw [hindex] at htop
  exact_mod_cast htop

theorem failureThreshold_eq_reverseHalfGap
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) =
      ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          (a.castLength hlength).order ⟨i.val, i.lt_large⟩ : Int) : ℚ) /
        2 + ramificationIndex K := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hsourceCurrent : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩ :=
    (E.order_castLength_eq_source_of_two_le a D horders hlength
      ⟨i.val, i.lt_large⟩ hiTwo).symm
  rcases Nat.mod_two_eq_zero_or_one i.val with hmod | hmod
  · have hprevious : (i.val - 1) % 2 = 1 := by omega
    have hthreshold : (i.val - 2) % 2 = 0 := by omega
    rw [failureThreshold_of_even (K := K) A₁ (i.val - 2) hthreshold,
      O.comparison_odd ⟨i.val - 1, by have := i.lt_large; omega⟩
        (by change i.val - 1 + 1 ≤ i.val; omega) hprevious,
      hsourceCurrent,
      O.target_even ⟨i.val, i.lt_large⟩ le_rfl hmod]
    push_cast at hformula ⊢
    linarith
  · have hprevious : (i.val - 1) % 2 = 0 := by omega
    have hthreshold : (i.val - 2) % 2 = 1 := by omega
    rw [failureThreshold_of_odd (K := K) A₁ (i.val - 2) hthreshold,
      O.comparison_even ⟨i.val - 1, by have := i.lt_large; omega⟩
        (by change i.val - 1 + 1 ≤ i.val; omega) hprevious,
      hsourceCurrent,
      O.target_odd ⟨i.val, i.lt_large⟩ le_rfl hmod]
    push_cast at hformula ⊢
    linarith

theorem sourceNextAlpha_gt_failureThreshold
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hcross : c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      (a.castLength hlength).order ⟨i.val + 1, hinterior⟩) :
    ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) <
      (a.castLength hlength).alphaValue ⟨i.val, by omega⟩ := by
  let source := a.castLength hlength
  let nextAlpha : Fin (N + 2) := ⟨i.val, by omega⟩
  have hge := sourceNextAlpha_ge_failureThreshold
    source c i hiTwo hinterior T
  change ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) <
    source.alphaValue nextAlpha
  by_contra hnot
  have hle : source.alphaValue nextAlpha ≤
      ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) :=
    le_of_not_gt hnot
  have heqAlpha : source.alphaValue nextAlpha =
      ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) := by
    apply le_antisymm hle
    simpa only [source, nextAlpha] using hge
  have hattains := attainsHalfGap_of_alphaValue_eq_int_even
    source nextAlpha (failureThreshold (K := K) A₁ (i.val - 2))
      heqAlpha (failureThreshold_even P (i.val - 2))
  have hreverse := failureThreshold_eq_reverseHalfGap
    a c D E horders hlength i hiTwo O hformula
  unfold AttainsHalfGap halfGapValue orderGap at hattains
  have hcast : nextAlpha.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hsucc : nextAlpha.succ =
      (⟨i.val + 1, hinterior⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hcast, hsucc, heqAlpha, hreverse] at hattains
  have horderQ :
      ((source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) =
        ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) := by
    push_cast at hattains
    linarith
  have horder : source.order ⟨i.val + 1, hinterior⟩ =
      c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    exact_mod_cast horderQ
  exact (ne_of_gt hcross) horder

set_option maxHeartbeats 800000 in
-- Dependent prefix indices and two coercion layers are normalized together.
theorem sourceNextAdjacentDefect_gt_failureLower
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hcross : c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      (a.castLength hlength).order ⟨i.val + 1, hinterior⟩) :
    (((((a.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (a.castLength hlength).order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
        ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ)) :
          WithTop ℚ) <
      (a.castLength hlength).truncatedPrefixDefect
        (a.castLength hlength) (-1) i.val (i.val + 2) := by
  let source := a.castLength hlength
  let nextAlpha : Fin (N + 2) := ⟨i.val, by omega⟩
  have halpha := sourceNextAlpha_gt_failureThreshold
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    a c D E horders hlength i hiTwo hinterior O P T hformula hcross
  have hlocal := source.order_sub_add_alpha_le_cappedAdjacent nextAlpha
  have hcast : nextAlpha.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hsucc : nextAlpha.succ =
      (⟨i.val + 1, hinterior⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hcast, hsucc] at hlocal
  have hshiftQ :
      ((source.order ⟨i.val, i.lt_large⟩ -
          source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
          ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) <
        ((source.order ⟨i.val, i.lt_large⟩ -
          source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
          source.alphaValue nextAlpha := by
    have h := add_lt_add_left
      (by simpa only [source, nextAlpha] using halpha)
      (((source.order ⟨i.val, i.lt_large⟩ -
        source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ))
    simpa only [source, nextAlpha, add_comm] using h
  have hshiftTop :
      ((((source.order ⟨i.val, i.lt_large⟩ -
          source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
          ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ)) :
            WithTop ℚ) <
        ((((source.order ⟨i.val, i.lt_large⟩ -
          source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
          source.alphaValue nextAlpha) : WithTop ℚ) := by
    exact_mod_cast hshiftQ
  exact hshiftTop.trans_le (by
    simpa only [source, nextAlpha, WithTop.coe_add] using hlocal)

set_option maxHeartbeats 1000000 in
-- The two complementary thresholds are normalized against four order casts.
theorem centralCurrentDefect_gt_thresholdShift
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hcross : c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      (a.castLength hlength).order ⟨i.val + 1, hinterior⟩) :
    ((((failureThreshold (K := K) A₁ (i.val - 1) : Int) : ℚ) +
        ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          (a.castLength hlength).order
            ⟨i.val + 1, hinterior⟩ : Int) : ℚ) : ℚ) : WithTop ℚ) <
      (a.castLength hlength).truncatedPrefixDefect c (-1)
        (i.val + 2) i.val := by
  let source := a.castLength hlength
  let previous := failureThreshold (K := K) A₁ (i.val - 2)
  let diagonal := failureThreshold (K := K) A₁ (i.val - 1)
  let shift : ℚ :=
    ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
      source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ)
  have hshiftNeg : shift < 0 := by
    dsimp only [shift]
    exact_mod_cast (sub_neg.mpr hcross)
  have hdiagonalWeak := T.diagonal
  have hdiagonalLowerQ : (diagonal : ℚ) + shift < (diagonal : ℚ) := by
    linarith
  have hdiagonalLowerTop :
      (((diagonal : Int) : ℚ) + shift : WithTop ℚ) <
        (((diagonal : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hdiagonalLowerQ
  have hdiagonalStrict :
      (((diagonal : Int) : ℚ) + shift : WithTop ℚ) <
        source.truncatedPrefixDefect c 1 i.val i.val :=
    hdiagonalLowerTop.trans_le (by
      simpa only [source, diagonal] using hdiagonalWeak)
  have hadjacentRaw := sourceNextAdjacentDefect_gt_failureLower
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    a c D E horders hlength i hiTwo hinterior O P T hformula hcross
  have hreverse := failureThreshold_eq_reverseHalfGap
    a c D E horders hlength i hiTwo O hformula
  have hsumIntRaw := failureThreshold_add_next (K := K) A₁ (i.val - 2)
  have hsumInt : previous + diagonal =
      2 * (ramificationIndex K : Int) := by
    dsimp only [previous, diagonal]
    rw [show i.val - 2 + 1 = i.val - 1 by omega] at hsumIntRaw
    exact hsumIntRaw
  have hsumQ : (previous : ℚ) + (diagonal : ℚ) =
      2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hsumInt
  have hlowerEq :
      ((source.order ⟨i.val, i.lt_large⟩ -
          source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ) +
          (previous : ℚ) =
        (diagonal : ℚ) + shift := by
    dsimp only [previous, diagonal, shift]
    change ((failureThreshold (K := K) A₁ (i.val - 2) : Int) : ℚ) = _ at hreverse
    push_cast at hreverse ⊢
    dsimp only [previous, diagonal] at hsumQ
    linarith
  have hadjacentStrict :
      (((diagonal : Int) : ℚ) + shift : WithTop ℚ) <
        source.truncatedPrefixDefect source (-1) (i.val + 2) i.val := by
    rw [source.truncatedPrefixDefect_comm source (-1) (i.val + 2) i.val]
    rw [← WithTop.coe_add, ← hlowerEq, WithTop.coe_add]
    simpa only [source, previous, WithTop.coe_add] using hadjacentRaw
  have hdom := source.truncatedPrefixDefect_domination
    source c (-1) 1 (i.val + 2) i.val i.val
  have hmin :
      (((diagonal : Int) : ℚ) + shift : WithTop ℚ) <
        min (source.truncatedPrefixDefect source (-1) (i.val + 2) i.val)
          (source.truncatedPrefixDefect c 1 i.val i.val) :=
    lt_min hadjacentStrict hdiagonalStrict
  have hout := hmin.trans_le hdom
  simpa only [source, diagonal, shift, mul_one, WithTop.coe_add] using hout

set_option maxHeartbeats 800000 in
-- The complementary threshold identity is lifted through `WithTop` addition.
theorem centralDefectSum_strict
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hcross : c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      (a.castLength hlength).order ⟨i.val + 1, hinterior⟩) :
    ((2 * (ramificationIndex K : ℚ) +
        (c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) -
        ((a.castLength hlength).order
          ⟨i.val + 1, hinterior⟩ : ℚ) : ℚ) : WithTop ℚ) <
      (a.castLength hlength).truncatedPrefixDefect c (-1)
          (i.val + 1) (i.val - 1) +
        (a.castLength hlength).truncatedPrefixDefect c (-1)
          (i.val + 2) i.val := by
  let source := a.castLength hlength
  let previous := failureThreshold (K := K) A₁ (i.val - 2)
  let diagonal := failureThreshold (K := K) A₁ (i.val - 1)
  let shift : ℚ :=
    ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
      source.order ⟨i.val + 1, hinterior⟩ : Int) : ℚ)
  have hpreviousWeak := T.shifted
  have hcurrentStrict := centralCurrentDefect_gt_thresholdShift
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    a c D E horders hlength i hiTwo hinterior O P T hformula hcross
  have hadd := WithTop.add_lt_add_of_le_of_lt
    (show ((((previous : Int) : ℚ) : WithTop ℚ) ≠ ⊤) by simp)
    (by simpa only [previous] using hpreviousWeak)
    (by simpa only [source, diagonal, shift, WithTop.coe_add] using
      hcurrentStrict)
  have hsumIntRaw := failureThreshold_add_next (K := K) A₁ (i.val - 2)
  have hsumInt : previous + diagonal =
      2 * (ramificationIndex K : Int) := by
    dsimp only [previous, diagonal]
    rw [show i.val - 2 + 1 = i.val - 1 by omega] at hsumIntRaw
    exact hsumIntRaw
  have hsumQ : (previous : ℚ) + (diagonal : ℚ) =
      2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hsumInt
  have hlowerQ :
      2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) -
          (source.order ⟨i.val + 1, hinterior⟩ : ℚ) =
        (previous : ℚ) + ((diagonal : ℚ) + shift) := by
    dsimp only [shift]
    push_cast
    linarith
  have hlowerTop :
      ((2 * (ramificationIndex K : ℚ) +
          (c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : ℚ) -
          (source.order ⟨i.val + 1, hinterior⟩ : ℚ) : ℚ) : WithTop ℚ) =
        (((previous : Int) : ℚ) : WithTop ℚ) +
          ((((diagonal : Int) : ℚ) + shift : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact_mod_cast hlowerQ
  rw [hlowerTop]
  simpa only [source, previous, diagonal, shift, WithTop.coe_add] using hadd

theorem prefixRepresentation_of_failure_interior
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hcentral : (a.castLength hlength).CentralRepresentationConditionsPrime c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hinterior : i.val + 1 < N + 3)
    (hnext : (E.bong.castLength hlength).IsNextEssential c i)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    DiagonalRepresents
      (c.prefixValues i.val (Nat.le_of_lt i.lt_large))
      ((a.castLength hlength).prefixValues (i.val + 1)
        (Nat.le_of_lt hinterior)) := by
  have hcross := (source_orderCrossings_of_nextEssential
    a c D E horders hlength i hiTwo hnext).1 hinterior
  have hsum := centralDefectSum_strict
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    a c D E horders hlength i hiTwo hinterior O P T hformula hcross
  exact prefixRepresentation_of_centralDefectBounds
    (a.castLength hlength) c hcentral i hiTwo hinterior hcross hsum

theorem prefixRepresentation_of_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (ambient : q.Represents r)
    (hcentral : (a.castLength hlength).CentralRepresentationConditionsPrime c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hnext : (E.bong.castLength hlength).IsNextEssential c i)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    DiagonalRepresents
      (c.prefixValues i.val (Nat.le_of_lt i.lt_large))
      ((a.castLength hlength).prefixValues (i.val + 1)
        (by have := i.lt_large; omega)) := by
  let source := a.castLength hlength
  by_cases hfull : i.val + 1 = N + 3
  · exact prefixRepresentation_of_ambient_when_target_full
      source c ambient i.val (Nat.le_of_lt i.lt_large) hfull
  · have hinterior : i.val + 1 < N + 3 := by
      have := i.lt_large
      omega
    exact prefixRepresentation_of_failure_interior
      (sourceLaws := sourceLaws) (sourceParity := sourceParity)
      a c D E horders hlength hcentral i hiTwo hinterior hnext O P T hformula

/-- The anisotropic scalar-failure branch of Beli's Lemma 9.12 is impossible.
The theorem combines the central-condition representation at the failure index
with the endpoint-complete mixed-defect propagation and prefix descent. -/
theorem false_of_anisotropic_of_failure
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q L (3 + N))
    (c : GoodBONG r M (N + 3))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (ambient : q.Represents r)
    (hcentral : (a.castLength hlength).CentralRepresentationConditionsPrime c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hanisotropic :
      (a.castLength hlength).Lemma814FirstThreeAnisotropic)
    (hnext : (E.bong.castLength hlength).IsNextEssential c i)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (S : Beli2019Lemma912SourceAlphaAlternation
      (a.castLength hlength) A₁ i)
    (C : Beli2019Lemma912ComparisonAlphaAlternation c A₁ i)
    (T : Beli2019Lemma912TopMixedDefectBounds
      (a.castLength hlength) c A₁ i)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (horderParity : Int.ModEq 2 R₁ R₂) :
    False := by
  have htop := prefixRepresentation_of_failure
    (sourceLaws := sourceLaws) (sourceParity := sourceParity)
    a c D E horders hlength ambient hcentral i hiTwo hnext O P T hformula
  exact false_of_anisotropic_of_topPrefixRepresentation
    (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
    a c D E horders hlength i hiTwo hanisotropic O P S C T hformula
      horderParity htop

end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
