/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912ScalarConditions
import Bong.Bong.PrefixRepresentationDescent
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 9.12: the anisotropic half-gap branch

This file starts the contradiction argument in the last type-I branch of
Lemma 9.12. If one of the later scalar inequalities fails, both relevant
adjacent order sums are forced below the first sum plus four. On the common
tail, the source alpha is then strictly larger than the constructed target
alpha, so parity forces every intervening constructed-target gap to be even.
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
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

/-- The two adjacent-order bounds forced by a failed later scalar inequality. -/
structure Beli2019Lemma912FailureOrderBounds
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (R₁ R₂ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  targetPair_lt :
    target.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
      target.order ⟨i.val, i.lt_large⟩ < R₁ + R₂ + 4
  comparisonPair_lt :
    c.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
      c.order ⟨i.val - 1, by have := i.le_small; omega⟩ < R₁ + R₂ + 4

/- A failed later scalar inequality bounds the two adjacent pairs used by the
anisotropic contradiction. -/
set_option maxHeartbeats 800000 in
theorem failureOrderBounds
    [Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (horderTarget :
      (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i) :
    Beli2019Lemma912FailureOrderBounds (E.bong.castLength hlength) c R₁ R₂ i := by
  let target := E.bong.castLength hlength
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let previous : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have htargetOneExact :
      (E.bong.castLength hlength).order
        (⟨1, by omega⟩ : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    rw [show (⟨1, by omega⟩ : Fin (N + 3)) =
      (⟨(1 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp]
    exact h
  have hsourceHalf : target.representationAlphaValue c i ≤
      target.halfGapValue current := by
    exact target.representationAlphaValue_le_sourceHalfGapValue_of_orderCondition
      c horderTarget i
  have htargetPairQ :
      (target.order current.castSucc : ℚ) +
          (target.order current.succ : ℚ) <
        (R₁ : ℚ) + (R₂ : ℚ) + 4 := by
    have hcurrentCast : current.castSucc =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hcurrentSucc : current.succ =
        (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
      apply Fin.ext
      simp only [current, Fin.val_succ]
      omega
    unfold halfGapValue orderGap at hsourceHalf
    rw [hcurrentCast, hcurrentSucc] at hsourceHalf
    have hsourceHalf' : target.representationAlphaValue c i ≤
      (((target.order ⟨i.val, i.lt_large⟩ -
        target.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) /
          2 + ramificationIndex K) := by
      simpa only [halfGapValue, orderGap] using hsourceHalf
    rw [htargetOneExact] at hfailure
    change (((target.order ⟨i.val, i.lt_large⟩ - (R₂ + 2) : Int) : ℚ) +
      (A₁ : ℚ) < target.representationAlphaValue c i) at hfailure
    rw [hcurrentCast, hcurrentSucc]
    push_cast at hfailure hformula hsourceHalf' ⊢
    linarith
  have htargetPair :
      target.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          target.order ⟨i.val, i.lt_large⟩ < R₁ + R₂ + 4 := by
    rw [show current.castSucc =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) by
          apply Fin.ext
          rfl,
      show current.succ = (⟨i.val, i.lt_large⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp only [current, Fin.val_succ]
        omega] at htargetPairQ
    exact_mod_cast htargetPairQ
  have hrightTop : target.representationAlpha c i ≤
      (((target.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        (c.halfGapValue previous : WithTop ℚ) := by
    exact (target.representationAlpha_le_prime c i).trans
      (target.representationAlphaPrime_le_primaryRightHalfGap c i
        (by omega))
  have hright : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
        c.halfGapValue previous := by
    rw [← target.coe_representationAlphaValue c i] at hrightTop
    exact WithTop.coe_le_coe.mp (by simpa using hrightTop)
  have hcomparisonPairQ :
      (c.order previous.castSucc : ℚ) +
          (c.order previous.succ : ℚ) <
        (R₁ : ℚ) + (R₂ : ℚ) + 4 := by
    have hpreviousCast : previous.castSucc =
        (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hpreviousSucc : previous.succ =
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      simp only [previous, Fin.val_succ]
      omega
    unfold halfGapValue orderGap at hright
    rw [hpreviousCast, hpreviousSucc] at hright
    have hright' : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
          (((c.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
            c.order ⟨i.val - 2, by have := i.le_small; omega⟩ : Int) : ℚ) /
              2 + ramificationIndex K) := by
      simpa only [halfGapValue, orderGap] using hright
    rw [htargetOneExact] at hfailure
    change (((target.order ⟨i.val, i.lt_large⟩ - (R₂ + 2) : Int) : ℚ) +
      (A₁ : ℚ) < target.representationAlphaValue c i) at hfailure
    rw [hpreviousCast, hpreviousSucc]
    push_cast at hfailure hformula hright' ⊢
    linarith
  have hcomparisonPair :
      c.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ <
        R₁ + R₂ + 4 := by
    rw [show previous.castSucc =
        (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)) by
          apply Fin.ext
          rfl,
      show previous.succ =
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) by
          apply Fin.ext
          simp only [previous, Fin.val_succ]
          omega] at hcomparisonPairQ
    exact_mod_cast hcomparisonPairQ
  exact ⟨htargetPair, hcomparisonPair⟩

/- On every common internal boundary up to the failure index, the source
alpha is strictly larger than the constructed target alpha. -/
set_option maxHeartbeats 800000 in
theorem sourceAlpha_gt_targetAlpha_of_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (k : Fin (N + 2)) (hkTwo : 2 ≤ k.val)
    (hki : k.val + 1 ≤ i.val) :
    (E.bong.castLength hlength).alphaValue k <
      (a.castLength hlength).alphaValue k := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hcomparison := E.representationAlphaValue_le_source
    a c D horders hlength hdefectSourceTarget i hiTwo
  have hsourceTop := source.representationAlpha_le_leftAlpha
    c hdefectSource i
  rw [← source.coe_representationAlphaValue c i] at hsourceTop
  have hsourceBound : source.representationAlphaValue c i ≤
      source.alphaValue ⟨i.val - 1, by have := i.lt_large; omega⟩ :=
    WithTop.coe_le_coe.mp hsourceTop
  let last : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hkLast : k ≤ last := by
    change k.val ≤ i.val - 1
    omega
  have hsourceEndpoint := source.alphaRightEndpoint_antitone hkLast
  have htargetEndpoint := target.alphaRightEndpoint_antitone
    (show (0 : Fin (N + 2)) ≤ k by exact Fin.zero_le k)
  have hsourceOrderK : source.order k.succ = target.order k.succ := by
    exact (E.order_castLength_eq_source_of_two_le
      a D horders hlength k.succ (by
        simp only [Fin.val_succ]
        omega)).symm
  have hsourceOrderI : source.order ⟨i.val, i.lt_large⟩ =
      target.order ⟨i.val, i.lt_large⟩ := by
    exact (E.order_castLength_eq_source_of_two_le
      a D horders hlength ⟨i.val, i.lt_large⟩ hiTwo).symm
  have htargetOne : target.order (1 : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    rw [show (1 : Fin (N + 3)) =
      (⟨(1 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp]
    exact h
  have htargetFirstAlpha : target.alphaValue (0 : Fin (N + 2)) =
      (A₁ : ℚ) := E.firstAlpha
  have hzeroSucc : (0 : Fin (N + 2)).succ =
      (1 : Fin (N + 3)) := by rfl
  unfold alphaRightEndpoint at hsourceEndpoint htargetEndpoint
  have hlastSucc : last.succ =
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  rw [hlastSucc, hsourceOrderK, hsourceOrderI] at hsourceEndpoint
  rw [htargetFirstAlpha, hzeroSucc, htargetOne] at htargetEndpoint
  change (((target.order ⟨i.val, i.lt_large⟩ -
      target.order (1 : Fin (N + 3)) : Int) : ℚ) + (A₁ : ℚ) <
    target.representationAlphaValue c i) at hfailure
  rw [htargetOne] at hfailure
  push_cast at hsourceEndpoint htargetEndpoint hfailure ⊢
  linarith [hcomparison, hsourceBound]

/- Every common constructed-target gap up to the failed boundary is even. -/
set_option maxHeartbeats 1200000 in
theorem targetOrderGap_even_of_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (k : Fin (N + 2)) (hkTwo : 2 ≤ k.val)
    (hki : k.val + 1 ≤ i.val) :
    Even ((E.bong.castLength hlength).orderGap k) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hgt := sourceAlpha_gt_targetAlpha_of_failure
    (sourceLaws := sourceLaws) a c D E horders hlength
      hdefectSourceTarget hdefectSource i hiTwo hfailure k hkTwo hki
  have hcast : source.order k.castSucc = target.order k.castSucc := by
    exact (E.order_castLength_eq_source_of_two_le
      a D horders hlength k.castSucc (by
        simp only [Fin.val_castSucc]
        omega)).symm
  have hsucc : source.order k.succ = target.order k.succ := by
    exact (E.order_castLength_eq_source_of_two_le
      a D horders hlength k.succ (by
        simp only [Fin.val_succ]
        omega)).symm
  have hgap : source.orderGap k = target.orderGap k := by
    unfold orderGap
    rw [hcast, hsucc]
  apply Int.not_odd_iff_even.mp
  intro hoddTarget
  have hoddSource : Odd (source.orderGap k) := by
    rwa [hgap]
  have hhalf : source.halfGapValue k = target.halfGapValue k := by
    unfold halfGapValue
    rw [hgap]
  have halpha : source.alphaValue k = target.alphaValue k := by
    rw [source.beli2009Corollary29_ii k hoddSource,
      target.beli2009Corollary29_ii k hoddTarget, hgap, hhalf]
  exact (ne_of_gt hgt) halpha

/-- An odd comparison gap makes its adjacent defect vanish. Right-endpoint
antitonicity then bounds every later alpha by the intervening order rise. -/
theorem comparisonAlpha_le_order_sub_of_orderGap_odd
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (k : Fin (N + 2)) (hki : k.val + 2 ≤ i.val)
    (hodd : Odd (c.orderGap k)) :
    c.alphaValue ⟨i.val - 2, by have := i.lt_large; omega⟩ ≤
      ((c.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
        c.order k.castSucc : Int) : ℚ) := by
  let last : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have hsumOdd : Odd (c.order k.castSucc + c.order k.succ) := by
    rcases hodd with ⟨t, ht⟩
    refine ⟨c.order k.castSucc + t, ?_⟩
    unfold orderGap at ht
    omega
  have hadjacent : c.adjacentDefect k = 0 :=
    c.adjacentDefect_eq_zero_of_order_sum_odd k hsumOdd
  have hlocalTop := c.order_sub_add_alpha_le_adjacentDefect k
  rw [hadjacent] at hlocalTop
  have hlocal :
      ((c.order k.castSucc - c.order k.succ : Int) : ℚ) +
          c.alphaValue k ≤ 0 := by
    exact_mod_cast hlocalTop
  have hkLast : k ≤ last := by
    change k.val ≤ i.val - 2
    omega
  have hendpoint := c.alphaRightEndpoint_antitone hkLast
  have hlastSucc : last.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  unfold alphaRightEndpoint at hendpoint
  rw [hlastSucc] at hendpoint
  change c.alphaValue last ≤ _
  push_cast at hlocal hendpoint ⊢
  linarith

set_option maxHeartbeats 1200000 in
-- The proof combines several rational endpoint inequalities and two parity cases.
theorem comparisonOrderGap_even_of_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hgapSharp : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4)
    (hcomparisonZero : c.order (0 : Fin (N + 3)) = R₁)
    (hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 3)))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (k : Fin (N + 2)) (hki : k.val + 2 ≤ i.val) :
    Even (c.orderGap k) := by
  let target := E.bong.castLength hlength
  let last : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have htargetOne : target.order (1 : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    rw [show (1 : Fin (N + 3)) =
      (⟨(1 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp]
    exact h
  have hprimaryTop := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact (target.representationAlpha_le_prime c i).trans
      (target.representationAlphaPrime_le_primaryRightCap c i)
  have hcapPos : 0 < i.val - 1 := by omega
  have hcapBound : i.val - 1 < N + 3 := by
    have := i.lt_large
    omega
  rw [c.prefixAlphaCap_of_internal hcapPos hcapBound] at hprimaryTop
  have hcapIndex :
      (⟨i.val - 1 - 1, by have := i.lt_large; omega⟩ : Fin (N + 2)) =
        last := by
    apply Fin.ext
    simp only [last]
    omega
  rw [hcapIndex, ← target.coe_representationAlphaValue c i] at hprimaryTop
  have hprimary : target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) +
        c.alphaValue last := by
    exact_mod_cast hprimaryTop
  have hANonnegative : 0 ≤ (A₁ : ℚ) := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hnonnegative := (target.alpha_p2 (0 : Fin (N + 2))).1
    have hfirst : target.alphaValue (0 : Fin (N + 2)) =
        (A₁ : ℚ) := E.firstAlpha
    rwa [hfirst] at hnonnegative
  apply Int.not_odd_iff_even.mp
  intro hodd
  have halpha := comparisonAlpha_le_order_sub_of_orderGap_odd
    (comparisonLaws := comparisonLaws) c i k hki hodd
  have hcritical : (c.order k.castSucc : ℚ) + (A₁ : ℚ) <
      ((R₂ + 2 : Int) : ℚ) := by
    change (((target.order ⟨i.val, i.lt_large⟩ -
      target.order (1 : Fin (N + 3)) : Int) : ℚ) +
        (A₁ : ℚ) < target.representationAlphaValue c i) at hfailure
    rw [htargetOne] at hfailure
    change (((target.order ⟨i.val, i.lt_large⟩ - (R₂ + 2) : Int) : ℚ) +
      (A₁ : ℚ) < target.representationAlphaValue c i) at hfailure
    change c.alphaValue last ≤ _ at halpha
    push_cast at hfailure hprimary halpha ⊢
    linarith
  by_cases hkEven : Even k.val
  · have hmono := c.orderSequence.entryOrZero_le_of_evenGap
      0 k.val (Nat.zero_le k.val) (by omega) hkEven
    rw [BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)] at hmono
    change c.order (0 : Fin (N + 3)) ≤ c.order k.castSucc at hmono
    rw [hcomparisonZero] at hmono
    have hmonoQ : (R₁ : ℚ) ≤ (c.order k.castSucc : ℚ) := by
      exact_mod_cast hmono
    have hgapSharpQ : ((R₂ - R₁ : Int) : ℚ) ≤
        2 * (ramificationIndex K : ℚ) - 4 := by
      exact_mod_cast hgapSharp
    push_cast at hcritical hformula hmonoQ hgapSharpQ
    linarith
  · have hkOdd : Odd k.val := Nat.not_even_iff_odd.mp hkEven
    have hkOne : 1 ≤ k.val := by
      rcases hkOdd with ⟨t, ht⟩
      omega
    have hdiffEven : Even (k.val - 1) := by
      rcases hkOdd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      omega
    have hmono := c.orderSequence.entryOrZero_le_of_evenGap
      1 k.val hkOne (by omega) hdiffEven
    rw [BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence (by omega)] at hmono
    change c.order (1 : Fin (N + 3)) ≤ c.order k.castSucc at hmono
    have hlower : R₂ + 2 ≤ c.order k.castSucc :=
      hcomparisonOne.trans hmono
    have hlowerQ : ((R₂ + 2 : Int) : ℚ) ≤
        (c.order k.castSucc : ℚ) := by
      exact_mod_cast hlower
    push_cast at hcritical hlowerQ
    linarith


/-- Failure squeezes both relevant adjacent sums to the common value
`R₁ + R₂ + 2`. -/
structure Beli2019Lemma912FailureAdjacentSumEqualities
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (R₁ R₂ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  targetPair_eq :
    target.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
      target.order ⟨i.val, i.lt_large⟩ = R₁ + R₂ + 2
  comparisonPair_eq :
    c.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
      c.order ⟨i.val - 1, by have := i.le_small; omega⟩ = R₁ + R₂ + 2

set_option maxHeartbeats 1600000 in
-- Two parity squeezes and the exceptional boundary `i = 2` require extra normalization.
theorem failureAdjacentSumEqualities
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (hdefectSourceTarget :
      (a.castLength hlength).RepresentationDefectCondition
        (E.bong.castLength hlength))
    (hdefectSource :
      (a.castLength hlength).RepresentationDefectCondition c)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hgapSharp : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4)
    (horderParity : Int.ModEq 2 R₁ R₂)
    (hcomparisonZero : c.order (0 : Fin (N + 3)) = R₁)
    (hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 3)))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hfailure :
      (((E.bong.castLength hlength).order ⟨i.val, i.lt_large⟩ -
          (E.bong.castLength hlength).order
            (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) +
          (A₁ : ℚ) <
        (E.bong.castLength hlength).representationAlphaValue c i)
    (hbounds : Beli2019Lemma912FailureOrderBounds
      (E.bong.castLength hlength) c R₁ R₂ i) :
    Beli2019Lemma912FailureAdjacentSumEqualities
      (E.bong.castLength hlength) c R₁ R₂ i := by
  let target := E.bong.castLength hlength
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let previous : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have htargetPrefix (t : Fin 3) :
      target.order ⟨t.val, by omega⟩ = ![R₁, R₂ + 2, R₁] t := by
    have h := E.order_castLength_prefix a D hlength t
    exact h.trans (D.orders t)
  have htargetZero : target.order (0 : Fin (N + 3)) = R₁ := by
    simpa using htargetPrefix (0 : Fin 3)
  have htargetOne : target.order (1 : Fin (N + 3)) = R₂ + 2 := by
    simpa using htargetPrefix (1 : Fin 3)
  have htargetTwo :
      target.order (⟨2, by omega⟩ : Fin (N + 3)) = R₁ := by
    have h := htargetPrefix (2 : Fin 3)
    change target.order (⟨2, by omega⟩ : Fin (N + 3)) = R₁ at h
    exact h
  have hbaseEven : Even (R₁ + R₂ + 2) := by
    have hdiffEven : Even (R₂ - R₁) := by
      rw [Int.modEq_iff_dvd] at horderParity
      rcases horderParity with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    rcases hdiffEven with ⟨t, ht⟩
    refine ⟨R₁ + t + 1, ?_⟩
    omega
  have hsqueeze (x : Int) (hle : R₁ + R₂ + 2 ≤ x)
      (hlt : x < R₁ + R₂ + 4) (heven : Even x) :
      x = R₁ + R₂ + 2 := by
    rcases heven with ⟨t, ht⟩
    rcases hbaseEven with ⟨u, hu⟩
    omega
  have htargetPair :
      target.order ⟨i.val - 1, by have := i.lt_large; omega⟩ +
          target.order ⟨i.val, i.lt_large⟩ = R₁ + R₂ + 2 := by
    by_cases hi : i.val = 2
    · have hleft :
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) =
            (1 : Fin (N + 3)) := by
          apply Fin.ext
          simp only [Fin.val_mk, Fin.val_one]
          omega
      have hright : (⟨i.val, i.lt_large⟩ : Fin (N + 3)) =
          (⟨2, by omega⟩ : Fin (N + 3)) := by
        apply Fin.ext
        omega
      rw [hleft, hright, htargetOne, htargetTwo]
      omega
    · have hiThree : 3 ≤ i.val := by omega
      have hgapEven := targetOrderGap_even_of_failure
        (sourceLaws := sourceLaws) (sourceParity := sourceParity)
          a c D E horders hlength hdefectSourceTarget hdefectSource
            i hiTwo hfailure current (by simp only [current]; omega)
              (by simp only [current]; omega)
      have hsumEven : Even
          (target.order current.castSucc + target.order current.succ) := by
        change Even (target.orderGap current) at hgapEven
        rcases hgapEven with ⟨t, ht⟩
        refine ⟨target.order current.castSucc + t, ?_⟩
        unfold orderGap at ht
        omega
      have hmono : R₁ + R₂ + 2 ≤
          target.order current.castSucc + target.order current.succ := by
        letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
        have h := target.adjacentOrderSum_monotone
          (show (0 : Fin (N + 2)) ≤ current by exact Fin.zero_le current)
        unfold adjacentOrderSum at h
        change target.order (0 : Fin (N + 3)) +
          target.order (1 : Fin (N + 3)) ≤
            target.order current.castSucc + target.order current.succ at h
        rw [htargetZero, htargetOne] at h
        simpa only [add_assoc] using h
      have hcurrentCast : current.castSucc =
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
        apply Fin.ext
        rfl
      have hcurrentSucc : current.succ =
          (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
        apply Fin.ext
        simp only [current, Fin.val_succ]
        omega
      have hlt : target.order current.castSucc + target.order current.succ <
          R₁ + R₂ + 4 := by
        rw [hcurrentCast, hcurrentSucc]
        exact hbounds.targetPair_lt
      have heq := hsqueeze
        (target.order current.castSucc + target.order current.succ)
        hmono hlt hsumEven
      rw [hcurrentCast, hcurrentSucc] at heq
      exact heq
  have hcomparisonPair :
      c.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          c.order ⟨i.val - 1, by have := i.le_small; omega⟩ =
        R₁ + R₂ + 2 := by
    have hgapEven := comparisonOrderGap_even_of_failure
      (sourceLaws := sourceLaws) (comparisonLaws := comparisonLaws)
        a c D E hlength hformula hgapSharp hcomparisonZero hcomparisonOne
          i hiTwo hfailure previous (by simp only [previous]; omega)
    have hsumEven : Even
        (c.order previous.castSucc + c.order previous.succ) := by
      rcases hgapEven with ⟨t, ht⟩
      refine ⟨c.order previous.castSucc + t, ?_⟩
      unfold orderGap at ht
      omega
    have hmonoFirst : c.order (0 : Fin (N + 3)) +
        c.order (1 : Fin (N + 3)) ≤
          c.order previous.castSucc + c.order previous.succ := by
      letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
      have h := c.adjacentOrderSum_monotone
        (show (0 : Fin (N + 2)) ≤ previous by exact Fin.zero_le previous)
      unfold adjacentOrderSum at h
      change c.order (0 : Fin (N + 3)) + c.order (1 : Fin (N + 3)) ≤
        c.order previous.castSucc + c.order previous.succ at h
      exact h
    have hmono : R₁ + R₂ + 2 ≤
        c.order previous.castSucc + c.order previous.succ := by
      rw [hcomparisonZero] at hmonoFirst
      omega
    have hpreviousCast : previous.castSucc =
        (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hpreviousSucc : previous.succ =
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      simp only [previous, Fin.val_succ]
      omega
    have hlt : c.order previous.castSucc + c.order previous.succ <
        R₁ + R₂ + 4 := by
      rw [hpreviousCast, hpreviousSucc]
      exact hbounds.comparisonPair_lt
    have heq := hsqueeze
      (c.order previous.castSucc + c.order previous.succ)
      hmono hlt hsumEven
    rw [hpreviousCast, hpreviousSucc] at heq
    exact heq
  exact ⟨htargetPair, hcomparisonPair⟩


/-- Corollary 2.3 data for the two alternating prefixes forced by a scalar
failure, together with the exact second comparison order. -/
structure Beli2019Lemma912FailureConstantSumConsequences
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (R₂ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  comparisonOne_eq : c.order (1 : Fin (N + 3)) = R₂ + 2
  target : ConstantAdjacentSumConsequences target
    (0 : Fin (N + 2)) ⟨i.val - 1, by have := i.lt_large; omega⟩
  comparison : ConstantAdjacentSumConsequences c
    (0 : Fin (N + 2)) ⟨i.val - 2, by have := i.lt_large; omega⟩

/-- The squeezed adjacent sums make Corollary 2.3 apply on both prefixes. -/
theorem failureConstantSumConsequences
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (hcomparisonZero : c.order (0 : Fin (N + 3)) = R₁)
    (hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 3)))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (hsums : Beli2019Lemma912FailureAdjacentSumEqualities
      (E.bong.castLength hlength) c R₁ R₂ i) :
    Beli2019Lemma912FailureConstantSumConsequences
      (E.bong.castLength hlength) c R₂ i := by
  let target := E.bong.castLength hlength
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let previous : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have htargetZero : target.order (0 : Fin (N + 3)) = R₁ := by
    have h := E.order_castLength_prefix a D hlength (0 : Fin 3)
    rw [D.order_zero] at h
    change target.order _ = R₁ at h
    rw [show (0 : Fin (N + 3)) =
      (⟨(0 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp]
    exact h
  have htargetOne : target.order (1 : Fin (N + 3)) = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    change target.order _ = R₂ + 2 at h
    rw [show (1 : Fin (N + 3)) =
      (⟨(1 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp]
    exact h
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have htargetFirstSum : target.adjacentOrderSum (0 : Fin (N + 2)) =
      R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    change target.order (0 : Fin (N + 3)) +
      target.order (1 : Fin (N + 3)) = R₁ + R₂ + 2
    rw [htargetZero, htargetOne]
    omega
  have htargetCurrentSum : target.adjacentOrderSum current =
      R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    rw [hcurrentCast, hcurrentSucc]
    exact hsums.targetPair_eq
  have htargetConsequences : ConstantAdjacentSumConsequences target
      (0 : Fin (N + 2)) current := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact target.beli2009Corollary23 (0 : Fin (N + 2)) current
      (Fin.zero_le current) (htargetFirstSum.trans htargetCurrentSum.symm)
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hcomparisonCurrentSum : c.adjacentOrderSum previous =
      R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    rw [hpreviousCast, hpreviousSucc]
    exact hsums.comparisonPair_eq
  have hcomparisonFirst_le : c.adjacentOrderSum (0 : Fin (N + 2)) ≤
      R₁ + R₂ + 2 := by
    letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
    have h := c.adjacentOrderSum_monotone
      (show (0 : Fin (N + 2)) ≤ previous by exact Fin.zero_le previous)
    exact h.trans_eq hcomparisonCurrentSum
  have hcomparisonOneEq : c.order (1 : Fin (N + 3)) = R₂ + 2 := by
    unfold adjacentOrderSum at hcomparisonFirst_le
    change c.order (0 : Fin (N + 3)) + c.order (1 : Fin (N + 3)) ≤
      R₁ + R₂ + 2 at hcomparisonFirst_le
    rw [hcomparisonZero] at hcomparisonFirst_le
    omega
  have hcomparisonFirstSum : c.adjacentOrderSum (0 : Fin (N + 2)) =
      R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    change c.order (0 : Fin (N + 3)) +
      c.order (1 : Fin (N + 3)) = R₁ + R₂ + 2
    rw [hcomparisonZero, hcomparisonOneEq]
    omega
  have hcomparisonConsequences : ConstantAdjacentSumConsequences c
      (0 : Fin (N + 2)) previous := by
    letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
    exact c.beli2009Corollary23 (0 : Fin (N + 2)) previous
      (Fin.zero_le previous)
        (hcomparisonFirstSum.trans hcomparisonCurrentSum.symm)
  exact ⟨hcomparisonOneEq, htargetConsequences, hcomparisonConsequences⟩


/-- The exact alternating order profiles on the two prefixes occurring in
the anisotropic contradiction. Parity is expressed by residues modulo two. -/
structure Beli2019Lemma912FailureAlternatingOrders
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (R₁ R₂ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  target_even : ∀ (j : Fin (N + 3)), j.val ≤ i.val → j.val % 2 = 0 →
    target.order j = R₁
  target_odd : ∀ (j : Fin (N + 3)), j.val ≤ i.val → j.val % 2 = 1 →
    target.order j = R₂ + 2
  comparison_even : ∀ (j : Fin (N + 3)), j.val + 1 ≤ i.val →
    j.val % 2 = 0 → c.order j = R₁
  comparison_odd : ∀ (j : Fin (N + 3)), j.val + 1 ≤ i.val →
    j.val % 2 = 1 → c.order j = R₂ + 2

/-- Corollary 2.3 turns constant adjacent sums into alternating orders. -/
theorem failureAlternatingOrders
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (hlength : 3 + N = N + 3)
    (hcomparisonZero : c.order (0 : Fin (N + 3)) = R₁)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiTwo : 2 ≤ i.val)
    (C : Beli2019Lemma912FailureConstantSumConsequences
      (E.bong.castLength hlength) c R₂ i) :
    Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i := by
  let target := E.bong.castLength hlength
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let previous : Fin (N + 2) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  let zeroValue : Fin (N + 3) := ⟨0, by omega⟩
  let oneValue : Fin (N + 3) := ⟨1, by omega⟩
  have htargetZero : target.order zeroValue = R₁ := by
    have h := E.order_castLength_prefix a D hlength (0 : Fin 3)
    rw [D.order_zero] at h
    change target.order _ = R₁ at h
    rw [show zeroValue =
      (⟨(0 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp only [zeroValue, Fin.val_zero]]
    exact h
  have htargetOne : target.order oneValue = R₂ + 2 := by
    have h := E.order_castLength_prefix a D hlength (1 : Fin 3)
    rw [D.order_one] at h
    change target.order _ = R₂ + 2 at h
    rw [show oneValue =
      (⟨(1 : Fin 3).val, by omega⟩ : Fin (N + 3)) by
        apply Fin.ext
        simp only [oneValue, Fin.val_one]]
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj hmod
    have heq := C.target.order_eq_of_sameParity
      j zeroValue
      (by change 0 ≤ j.val; omega)
      (by change j.val ≤ (i.val - 1) + 1; omega)
      (by change 0 ≤ zeroValue.val; omega)
      (by change zeroValue.val ≤ (i.val - 1) + 1; simp only [zeroValue]; omega)
      (by change j.val % 2 = zeroValue.val % 2; simpa only [zeroValue] using hmod)
    exact heq.trans htargetZero
  · intro j hj hmod
    have heq := C.target.order_eq_of_sameParity
      j oneValue
      (by change 0 ≤ j.val; omega)
      (by change j.val ≤ (i.val - 1) + 1; omega)
      (by change 0 ≤ oneValue.val; omega)
      (by change oneValue.val ≤ (i.val - 1) + 1; simp only [oneValue]; omega)
      (by change j.val % 2 = oneValue.val % 2; simpa only [oneValue] using hmod)
    exact heq.trans htargetOne
  · intro j hj hmod
    have heq := C.comparison.order_eq_of_sameParity
      j zeroValue
      (by change 0 ≤ j.val; omega)
      (by change j.val ≤ (i.val - 2) + 1; omega)
      (by change 0 ≤ zeroValue.val; omega)
      (by change zeroValue.val ≤ (i.val - 2) + 1; simp only [zeroValue]; omega)
      (by change j.val % 2 = zeroValue.val % 2; simpa only [zeroValue] using hmod)
    exact heq.trans hcomparisonZero
  · intro j hj hmod
    have heq := C.comparison.order_eq_of_sameParity
      j oneValue
      (by change 0 ≤ j.val; omega)
      (by change j.val ≤ (i.val - 2) + 1; omega)
      (by change 0 ≤ oneValue.val; omega)
      (by change oneValue.val ≤ (i.val - 2) + 1; simp only [oneValue]; omega)
      (by change j.val % 2 = oneValue.val % 2; simpa only [oneValue] using hmod)
    exact heq.trans C.comparisonOne_eq


/-- The first comparison alpha and its complementary dyadic depth in the
anisotropic failure branch. -/
structure Beli2019Lemma912ComparisonFirstAlphaProfile
    (c : GoodBONG s Q (N + 3)) (A₁ : Int) : Prop where
  alpha_eq : c.alphaValue (0 : Fin (N + 2)) = ((A₁ + 1 : Int) : ℚ)
  halfGap_eq : c.halfGapValue (0 : Fin (N + 2)) = ((A₁ + 1 : Int) : ℚ)
  attainsHalfGap : c.AttainsHalfGap (0 : Fin (N + 2))
  first_even : Even (A₁ + 1)
  first_pos : 0 < A₁ + 1
  first_lt_twoE : A₁ + 1 < 2 * (ramificationIndex K : Int)
  complement_even : Even (2 * (ramificationIndex K : Int) - (A₁ + 1))
  complement_pos : 0 < 2 * (ramificationIndex K : Int) - (A₁ + 1)
  complement_lt_twoE :
    2 * (ramificationIndex K : Int) - (A₁ + 1) <
      2 * (ramificationIndex K : Int)

set_option maxHeartbeats 800000 in
-- Rational half-gap normalization and the integral-alpha dichotomy are both used.
theorem comparisonFirstAlphaProfile
    [comparisonLaws : Beli2006AlphaLaws.{u, z} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, z} K]
    {R₁ R₂ A₁ : Int}
    (c : GoodBONG s Q (N + 3))
    (hzero : c.order (0 : Fin (N + 3)) = R₁)
    (hone : c.order (1 : Fin (N + 3)) = R₂ + 2)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hgapSharp : R₂ - R₁ ≤ 2 * (ramificationIndex K : Int) - 4)
    (hANonnegative : 0 ≤ A₁)
    (hAodd : Odd A₁)
    (hstrict : (A₁ : ℚ) < c.alphaValue (0 : Fin (N + 2))) :
    Beli2019Lemma912ComparisonFirstAlphaProfile c A₁ := by
  letI : Beli2006AlphaLaws.{u, z} K := comparisonLaws
  letI : Beli2009AlphaParityLaws.{u, z} K := comparisonParity
  have hgapSharpQ : ((R₂ - R₁ : Int) : ℚ) ≤
      2 * (ramificationIndex K : ℚ) - 4 := by
    exact_mod_cast hgapSharp
  have hfirstLtQ : (((A₁ + 1 : Int) : ℚ)) <
      2 * (ramificationIndex K : ℚ) := by
    push_cast at hformula hgapSharpQ ⊢
    linarith
  have hfirstLt : A₁ + 1 < 2 * (ramificationIndex K : Int) := by
    exact_mod_cast hfirstLtQ
  have hlower : ((A₁ + 1 : Int) : ℚ) ≤
      c.alphaValue (0 : Fin (N + 2)) := by
    exact c.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      (0 : Fin (N + 2)) A₁ (by omega) hstrict
  have hhalf : c.halfGapValue (0 : Fin (N + 2)) =
      ((A₁ + 1 : Int) : ℚ) := by
    unfold halfGapValue orderGap
    change (((c.order (1 : Fin (N + 3)) -
      c.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 +
        ramificationIndex K) = _
    rw [hzero, hone]
    push_cast at hformula ⊢
    linarith
  have hupper := c.alphaValue_le_halfGapValue (0 : Fin (N + 2))
  rw [hhalf] at hupper
  have halpha : c.alphaValue (0 : Fin (N + 2)) =
      ((A₁ + 1 : Int) : ℚ) := le_antisymm hupper hlower
  have hattains : c.AttainsHalfGap (0 : Fin (N + 2)) := by
    unfold AttainsHalfGap
    exact halpha.trans hhalf.symm
  have hfirstEven : Even (A₁ + 1) := by
    rcases hAodd with ⟨t, ht⟩
    refine ⟨t + 1, ?_⟩
    omega
  have hfirstPos : 0 < A₁ + 1 := by omega
  have hcomplementEven :
      Even (2 * (ramificationIndex K : Int) - (A₁ + 1)) := by
    rcases hfirstEven with ⟨t, ht⟩
    refine ⟨(ramificationIndex K : Int) - t, ?_⟩
    omega
  exact ⟨halpha, hhalf, hattains, hfirstEven, hfirstPos, hfirstLt,
    hcomplementEven, by omega, by omega⟩


/-- Corollary 2.3 propagates first-boundary half-gap attainment throughout
the comparison prefix. -/
theorem comparisonAttainsHalfGap_on_failurePrefix
    {R₂ : Int}
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (C : Beli2019Lemma912FailureConstantSumConsequences target c R₂ i)
    {A₁ : Int} (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (k : Fin (N + 2)) (hk : k.val + 2 ≤ i.val) :
    c.AttainsHalfGap k := by
  have hkPrevious : k ≤
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (N + 2)) := by
    change k.val ≤ i.val - 2
    omega
  exact (C.comparison.attainsHalfGap_iff k (Fin.zero_le k) hkPrevious).mpr
    P.attainsHalfGap

/-- The two alternating comparison-alpha values on the failure prefix. -/
structure Beli2019Lemma912ComparisonAlphaAlternation
    (c : GoodBONG s Q (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  even : ∀ (k : Fin (N + 2)), k.val + 2 ≤ i.val → k.val % 2 = 0 →
    c.alphaValue k = ((A₁ + 1 : Int) : ℚ)
  odd : ∀ (k : Fin (N + 2)), k.val + 2 ≤ i.val → k.val % 2 = 1 →
    c.alphaValue k =
      ((2 * (ramificationIndex K : Int) - (A₁ + 1) : Int) : ℚ)

/-- The alternating order profile evaluates every attained half-gap explicitly. -/
theorem comparisonAlphaAlternation
    {R₁ R₂ A₁ : Int}
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (C : Beli2019Lemma912FailureConstantSumConsequences target c R₂ i)
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    Beli2019Lemma912ComparisonAlphaAlternation c A₁ i := by
  refine ⟨?_, ?_⟩
  · intro k hk hmod
    have hnextMod : k.succ.val % 2 = 1 := by
      simp only [Fin.val_succ]
      omega
    have hleft := O.comparison_even k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod)
    have hright := O.comparison_odd k.succ (by
      simp only [Fin.val_succ]
      omega) hnextMod
    have hattains := comparisonAttainsHalfGap_on_failurePrefix
      target c i C P k hk
    unfold AttainsHalfGap at hattains
    rw [hattains]
    unfold halfGapValue orderGap
    rw [hleft, hright]
    push_cast at hformula ⊢
    linarith
  · intro k hk hmod
    have hnextMod : k.succ.val % 2 = 0 := by
      simp only [Fin.val_succ]
      omega
    have hleft := O.comparison_odd k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod)
    have hright := O.comparison_even k.succ (by
      simp only [Fin.val_succ]
      omega) hnextMod
    have hattains := comparisonAttainsHalfGap_on_failurePrefix
      target c i C P k hk
    unfold AttainsHalfGap at hattains
    rw [hattains]
    unfold halfGapValue orderGap
    rw [hleft, hright]
    push_cast at hformula ⊢
    linarith


/-- Every target adjacent sum in the alternating prefix has the baseline value. -/
theorem targetAdjacentSum_eq_of_alternatingOrders
    {R₁ R₂ : Int}
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (k : Fin (N + 2)) (hk : k.val + 1 ≤ i.val) :
    target.order k.castSucc + target.order k.succ = R₁ + R₂ + 2 := by
  rcases Nat.mod_two_eq_zero_or_one k.val with hmod | hmod
  · have hnext : k.succ.val % 2 = 1 := by
      simp only [Fin.val_succ]
      omega
    rw [O.target_even k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod),
      O.target_odd k.succ (by simp only [Fin.val_succ]; omega) hnext]
    omega
  · have hnext : k.succ.val % 2 = 0 := by
      simp only [Fin.val_succ]
      omega
    rw [O.target_odd k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod),
      O.target_even k.succ (by simp only [Fin.val_succ]; omega) hnext]
    omega

/-- Every comparison adjacent sum in its alternating prefix has the baseline value. -/
theorem comparisonAdjacentSum_eq_of_alternatingOrders
    {R₁ R₂ : Int}
    (target : GoodBONG q M (N + 3))
    (c : GoodBONG s Q (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (O : Beli2019Lemma912FailureAlternatingOrders target c R₁ R₂ i)
    (k : Fin (N + 2)) (hk : k.val + 2 ≤ i.val) :
    c.order k.castSucc + c.order k.succ = R₁ + R₂ + 2 := by
  rcases Nat.mod_two_eq_zero_or_one k.val with hmod | hmod
  · have hnext : k.succ.val % 2 = 1 := by
      simp only [Fin.val_succ]
      omega
    rw [O.comparison_even k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod),
      O.comparison_odd k.succ (by simp only [Fin.val_succ]; omega) hnext]
    omega
  · have hnext : k.succ.val % 2 = 0 := by
      simp only [Fin.val_succ]
      omega
    rw [O.comparison_odd k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod),
      O.comparison_even k.succ (by simp only [Fin.val_succ]; omega) hnext]
    omega


/-- The source alpha at the third boundary and the Corollary 2.3 data on
the remaining source prefix. -/
structure Beli2019Lemma912SourceAlphaProfile
    (source : GoodBONG q M (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiThree : 3 ≤ i.val) : Prop where
  thirdAlpha_eq : source.alphaValue
    ⟨2, by have := i.lt_large; omega⟩ = ((A₁ + 1 : Int) : ℚ)
  thirdHalfGap_eq : source.halfGapValue
    ⟨2, by have := i.lt_large; omega⟩ =
    ((A₁ + 1 : Int) : ℚ)
  thirdAttainsHalfGap : source.AttainsHalfGap
    ⟨2, by have := i.lt_large; omega⟩
  consequences : ConstantAdjacentSumConsequences source
    ⟨2, by have := i.lt_large; omega⟩
      ⟨i.val - 1, by have := i.lt_large; omega⟩

set_option maxHeartbeats 1000000 in
-- Several casted order identifications are normalized before applying Corollary 2.3.
theorem sourceAlphaProfile
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiThree : 3 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (P : Beli2019Lemma912ComparisonFirstAlphaProfile c A₁)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K)
    (hthirdStrict : (A₁ : ℚ) <
      (a.castLength hlength).alphaValue
        ⟨2, by have := i.lt_large; omega⟩) :
    Beli2019Lemma912SourceAlphaProfile (a.castLength hlength) A₁ i hiThree := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  let third : Fin (N + 2) :=
    ⟨2, by have := i.lt_large; omega⟩
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hsourceTarget (j : Fin (N + 3)) (hj : 2 ≤ j.val) :
      source.order j = target.order j :=
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength j hj).symm
  have hsourceTwo : source.order third.castSucc = R₁ := by
    rw [hsourceTarget third.castSucc (by
      simp only [third, Fin.val_castSucc]
      omega)]
    exact O.target_even third.castSucc (by
      simp only [third, Fin.val_castSucc]
      omega) (by norm_num [third])
  have hsourceThree : source.order third.succ = R₂ + 2 := by
    rw [hsourceTarget third.succ (by
      simp only [third, Fin.val_succ]
      omega)]
    exact O.target_odd third.succ (by
      simp only [third, Fin.val_succ]
      omega) (by norm_num [third])
  have hthirdHalf : source.halfGapValue third =
      ((A₁ + 1 : Int) : ℚ) := by
    unfold halfGapValue orderGap
    rw [hsourceTwo, hsourceThree]
    push_cast at hformula ⊢
    linarith
  have hthirdLower : ((A₁ + 1 : Int) : ℚ) ≤
      source.alphaValue third := by
    exact source.intCast_add_one_le_alphaValue_of_lt_of_le_twoE
      third A₁ P.first_lt_twoE.le (by simpa only [source, third] using hthirdStrict)
  have hthirdUpper := source.alphaValue_le_halfGapValue third
  rw [hthirdHalf] at hthirdUpper
  have hthirdAlpha : source.alphaValue third =
      ((A₁ + 1 : Int) : ℚ) := le_antisymm hthirdUpper hthirdLower
  have hthirdAttains : source.AttainsHalfGap third := by
    unfold AttainsHalfGap
    exact hthirdAlpha.trans hthirdHalf.symm
  have hsourcePair_eq_target (k : Fin (N + 2))
      (hkTwo : 2 ≤ k.val) :
      source.order k.castSucc + source.order k.succ =
        target.order k.castSucc + target.order k.succ := by
    rw [hsourceTarget k.castSucc (by
      simp only [Fin.val_castSucc]
      omega), hsourceTarget k.succ (by
        simp only [Fin.val_succ]
        omega)]
  have hthirdSum : source.adjacentOrderSum third = R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    rw [hsourcePair_eq_target third (by simp only [third]; omega)]
    exact targetAdjacentSum_eq_of_alternatingOrders
      target c i O third (by simp only [third]; omega)
  have hcurrentSum : source.adjacentOrderSum current = R₁ + R₂ + 2 := by
    unfold adjacentOrderSum
    rw [hsourcePair_eq_target current (by simp only [current]; omega)]
    exact targetAdjacentSum_eq_of_alternatingOrders
      target c i O current (by simp only [current]; omega)
  have hconsequences : ConstantAdjacentSumConsequences source third current := by
    exact source.beli2009Corollary23 third current (by
      change 2 ≤ i.val - 1
      omega) (hthirdSum.trans hcurrentSum.symm)
  exact ⟨by simpa only [source, third] using hthirdAlpha,
    by simpa only [source, third] using hthirdHalf,
    by simpa only [source, third] using hthirdAttains, hconsequences⟩

/-- Third-boundary half-gap attainment propagates along the source prefix. -/
theorem sourceAttainsHalfGap_on_failurePrefix
    {A₁ : Int}
    (source : GoodBONG q M (N + 3))
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiThree : 3 ≤ i.val)
    (S : Beli2019Lemma912SourceAlphaProfile source A₁ i hiThree)
    (k : Fin (N + 2)) (hkTwo : 2 ≤ k.val)
    (hki : k.val + 1 ≤ i.val) :
    source.AttainsHalfGap k := by
  let third : Fin (N + 2) :=
    ⟨2, by have := i.lt_large; omega⟩
  let current : Fin (N + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hthirdK : third ≤ k := by
    change 2 ≤ k.val
    exact hkTwo
  have hkCurrent : k ≤ current := by
    change k.val ≤ i.val - 1
    omega
  exact (S.consequences.attainsHalfGap_iff k hthirdK hkCurrent).mpr
    S.thirdAttainsHalfGap

/-- The two alternating source-alpha values from the third boundary onward. -/
structure Beli2019Lemma912SourceAlphaAlternation
    (source : GoodBONG q M (N + 3)) (A₁ : Int)
    (i : RepresentationIndex (N + 3) (N + 3)) : Prop where
  even : ∀ (k : Fin (N + 2)), 2 ≤ k.val → k.val + 1 ≤ i.val →
    k.val % 2 = 0 → source.alphaValue k = ((A₁ + 1 : Int) : ℚ)
  odd : ∀ (k : Fin (N + 2)), 2 ≤ k.val → k.val + 1 ≤ i.val →
    k.val % 2 = 1 → source.alphaValue k =
      ((2 * (ramificationIndex K : Int) - (A₁ + 1) : Int) : ℚ)

/-- Source-target order agreement evaluates all attained source half-gaps. -/
theorem sourceAlphaAlternation
    {R₁ R₂ A₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ A₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ t : Fin 3,
      a.order (Fin.castAdd N t) = ![R₁, R₂, R₁] t)
    (hlength : 3 + N = N + 3)
    (i : RepresentationIndex (N + 3) (N + 3))
    (hiThree : 3 ≤ i.val)
    (O : Beli2019Lemma912FailureAlternatingOrders
      (E.bong.castLength hlength) c R₁ R₂ i)
    (S : Beli2019Lemma912SourceAlphaProfile (a.castLength hlength) A₁ i hiThree)
    (hformula : (A₁ : ℚ) =
      ((R₂ - R₁ : Int) : ℚ) / 2 + ramificationIndex K) :
    Beli2019Lemma912SourceAlphaAlternation (a.castLength hlength) A₁ i := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hsourceTarget (j : Fin (N + 3)) (hj : 2 ≤ j.val) :
      source.order j = target.order j :=
    (E.order_castLength_eq_source_of_two_le
      a D horders hlength j hj).symm
  refine ⟨?_, ?_⟩
  · intro k hkTwo hki hmod
    have hnextMod : k.succ.val % 2 = 1 := by
      simp only [Fin.val_succ]
      omega
    have hleftTarget := O.target_even k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod)
    have hrightTarget := O.target_odd k.succ (by
      simp only [Fin.val_succ]
      omega) hnextMod
    have hleft : source.order k.castSucc = R₁ :=
      (hsourceTarget k.castSucc (by
        simp only [Fin.val_castSucc]
        omega)).trans hleftTarget
    have hright : source.order k.succ = R₂ + 2 :=
      (hsourceTarget k.succ (by
        simp only [Fin.val_succ]
        omega)).trans hrightTarget
    have hattains := sourceAttainsHalfGap_on_failurePrefix
      source i hiThree S k hkTwo hki
    unfold AttainsHalfGap at hattains
    rw [hattains]
    unfold halfGapValue orderGap
    rw [hleft, hright]
    push_cast at hformula ⊢
    linarith
  · intro k hkTwo hki hmod
    have hnextMod : k.succ.val % 2 = 0 := by
      simp only [Fin.val_succ]
      omega
    have hleftTarget := O.target_odd k.castSucc (by
      simp only [Fin.val_castSucc]
      omega) (by simpa only [Fin.val_castSucc] using hmod)
    have hrightTarget := O.target_even k.succ (by
      simp only [Fin.val_succ]
      omega) hnextMod
    have hleft : source.order k.castSucc = R₂ + 2 :=
      (hsourceTarget k.castSucc (by
        simp only [Fin.val_castSucc]
        omega)).trans hleftTarget
    have hright : source.order k.succ = R₁ :=
      (hsourceTarget k.succ (by
        simp only [Fin.val_succ]
        omega)).trans hrightTarget
    have hattains := sourceAttainsHalfGap_on_failurePrefix
      source i hiThree S k hkTwo hki
    unfold AttainsHalfGap at hattains
    rw [hattains]
    unfold halfGapValue orderGap
    rw [hleft, hright]
    push_cast at hformula ⊢
    linarith


end BONG.GoodBONG.Beli2019Lemma910Data

end Bong
