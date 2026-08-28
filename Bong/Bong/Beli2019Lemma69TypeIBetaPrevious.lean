/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftValue
import Bong.Bong.Beli2019Lemma27

/-!
# Beli (2019), Lemma 6.9(ii): the type-I previous-defect candidate

Lemma 2.7 replaces the secondary candidate at an odd type-I boundary by
one involving `d[-a_(1,i) b_(1,i-2)]`.  The preceding representation value
already bounds this defect through its primary candidate.  Endpoint
monotonicity and the constant even source profile then give the desired
target-alpha bound, including the first odd boundary after the left branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every even source entry through the right type-I switch equals the
canonical anchor entry. -/
theorem lemma69_typeI_source_even_eq_anchor
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat) (hkEven : Even k)
    (hkRight : k ≤ C.rightSwitch) :
    a.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor := by
  by_cases hkAnchor : k ≤ D.anchor
  · exact C.source_to_anchor k hkAnchor hkEven
  · have hanchorK : D.anchor ≤ k :=
      Nat.le_of_lt (lt_of_not_ge hkAnchor)
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hdistance : Even (k - D.anchor) := by
      rcases hkEven with ⟨x, hx⟩
      rcases hanchorEven with ⟨y, hy⟩
      exact ⟨x - y, by omega⟩
    exact C.source_to_right k hanchorK hkRight hdistance

/-- The order comparison needed by Lemma 2.7(i) at an odd central type-I
boundary.  At the first boundary it comes from the normalized left profile;
later it comes from the central two-unit gap. -/
theorem lemma69_typeI_beta_previous_cross
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    b.order ⟨i.val - 2, by
      have hi := i.le_small
      omega⟩ ≤ a.order ⟨i.val, i.lt_large⟩ := by
  have hgoodRaw := a.good
    (⟨i.val - 2, by have hi := i.lt_large; omega⟩ : Fin (n + 2))
    (by
      change (i.val - 2) + 2 < n + 2
      have hi := i.lt_large
      omega)
  have hgood : a.order ⟨i.val - 2, by
      have hi := i.lt_large
      omega⟩ ≤ a.order ⟨i.val, i.lt_large⟩ := by
    have hindex :
        (⟨(⟨i.val - 2, by have hi := i.lt_large; omega⟩ :
            Fin (n + 2)).val + 2, by
              change (i.val - 2) + 2 < n + 2
              have hi := i.lt_large
              omega⟩ : Fin (n + 2)) = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change (i.val - 2) + 2 = i.val
      omega
    rw [hindex] at hgoodRaw
    exact hgoodRaw
  have htargetSource : b.order ⟨i.val - 2, by
      have hi := i.le_small
      omega⟩ ≤ a.order ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ := by
    by_cases hcentral : C.leftSwitch ≤ i.val - 2
    · rcases hodd with ⟨d, hd⟩
      have hearlierOdd : Odd (i.val - 2) := ⟨d - 1, by omega⟩
      have hgap := lemma69_v_typeI_odd_entry_gap_two
        a b D C hfirst (i.val - 2) hearlierOdd hcentral (by omega)
      have hgapOrder : a.order ⟨i.val - 2, by
          have hi := i.lt_large
          omega⟩ = b.order ⟨i.val - 2, by
            have hi := i.le_small
            omega⟩ + 2 := by
        rw [← a.orderSequence_entryOrZero_eq_order,
          ← b.orderSequence_entryOrZero_eq_order]
        simpa only using hgap
      omega
    · have hfirstBoundary : i.val - 1 = C.leftSwitch := by omega
      rcases hodd with ⟨d, hd⟩
      have hboundaryEven : Even (i.val - 1) := ⟨d, by omega⟩
      have horders := lemma69_typeI_left_boundary_orders
        a b D C hfirst (i.val - 1) (by omega) (by omega) hboundaryEven
      have hindex : i.val - 1 - 1 = i.val - 2 := by omega
      have hleftOrder : b.order ⟨i.val - 2, by
          have hi := i.le_small
          omega⟩ = a.order ⟨i.val - 2, by
            have hi := i.lt_large
            omega⟩ - 1 := by
        rw [← b.orderSequence_entryOrZero_eq_order,
          ← a.orderSequence_entryOrZero_eq_order]
        simpa only [hindex] using horders.2.2
      omega
  exact htargetSource.trans hgood

set_option maxHeartbeats 2000000 in
-- The proof transports the preceding primary candidate through two endpoint shifts.
/-- At every nonendpoint odd central type-I boundary, the target alpha is
below Lemma 2.7(i)'s previous-defect replacement candidate. -/
theorem lemma69_typeI_beta_le_previousDefect_of_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ : RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationSecondaryPreviousDefect b i (by
        constructor
        · exact hiTwo
        · rcases hodd with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          have hr := C.right_le_last
          have hb := D.profile.lastDifference.bound
          omega) := by
  have hiNext : i.val + 1 < n + 2 := by
    rcases hodd with ⟨d, hd⟩
    rcases C.right_even with ⟨e, he⟩
    have hr := C.right_le_last
    have hb := D.profile.lastDifference.bound
    omega
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hiPreviousAlpha : i.val - 2 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, hiPreviousAlpha⟩
  let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, by omega, hiPrevious, by
      have hi := i.lt_large
      omega⟩
  rcases hodd with ⟨d, hd⟩
  have hpEven : Even p.val := ⟨d, by simp only [p]; omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarRight : i.val + 1 ≤ C.rightSwitch := by
    rcases C.right_even with ⟨e, he⟩
    omega
  have hgapEntries := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst p.val hpEven (by simpa only [p] using hleft) (by
      simp only [p]
      omega)
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPrevious⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc + 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    simpa only [p] using hgapEntries
  have hbetaSource : b.alphaValue p = a.alphaValue p - 2 := by
    unfold alphaLeftEndpoint at hweight
    change (a.order p.castSucc : ℚ) + a.alphaValue p =
      (b.order p.castSucc : ℚ) + b.alphaValue p at hweight
    rw [htargetPrevious] at hweight
    push_cast at hweight ⊢
    linarith
  have hsourcePrevious := lemma69_typeI_source_even_eq_anchor
    a b D C hfirst (i.val - 1) hpEven hright.le
  have hsourceFar := lemma69_typeI_source_even_eq_anchor
    a b D C hfirst (i.val + 1) hfarEven hfarRight
  have hsourceTwoStep : a.order ⟨i.val + 1, hiNext⟩ =
      a.order ⟨i.val - 1, hiPrevious⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hsourceFar.trans hsourcePrevious.symm
  let currentShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      a.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((a.order ⟨i.val - 1, hiPrevious⟩ -
      b.order ⟨i.val - 2, by have hi := i.le_small; omega⟩ : Int) : ℚ)
  let middleDefect := a.truncatedPrefixDefect b (-1)
    i.val (i.val - 2)
  have hprevious' : a.representationAlpha b previousIdx =
      (a.alphaValue previous : WithTop ℚ) := by
    simpa only [previousIdx, previous] using hprevious
  have hpreviousPrimary : (a.alphaValue previous : WithTop ℚ) ≤
      (previousShift : WithTop ℚ) + middleDefect := by
    calc
      (a.alphaValue previous : WithTop ℚ) =
          a.representationAlpha b previousIdx := hprevious'.symm
      _ ≤ a.representationPrimaryDefect b previousIdx :=
        a.representationAlpha_le_primary b previousIdx
      _ = (previousShift : WithTop ℚ) + middleDefect := by
        unfold representationPrimaryDefect
        simp only [previousIdx, previousShift, middleDefect,
          show i.val - 1 + 1 = i.val by omega,
          show i.val - 1 - 1 = i.val - 2 by omega]
  have hendpoint := a.alphaRightEndpoint_antitone
    (show previous ≤ p by
      change previous.val ≤ p.val
      simp only [previous, p]
      omega)
  have hpreviousSucc : previous.succ = p.castSucc := by
    apply Fin.ext
    simp only [previous, p, Fin.val_succ, Fin.val_castSucc]
    omega
  have hsourceRecurrence : a.alphaValue p ≤
      currentShift + a.alphaValue previous := by
    unfold alphaRightEndpoint at hendpoint
    rw [hpSucc, hpreviousSucc, hpCast] at hendpoint
    dsimp only [currentShift]
    push_cast at hendpoint ⊢
    linarith
  have hsourceBound : (a.alphaValue p : WithTop ℚ) ≤
      ((currentShift + previousShift : ℚ) : WithTop ℚ) +
        middleDefect := by
    calc
      (a.alphaValue p : WithTop ℚ) ≤
          (currentShift : WithTop ℚ) +
            (a.alphaValue previous : WithTop ℚ) := by
        exact_mod_cast hsourceRecurrence
      _ ≤ (currentShift : WithTop ℚ) +
          ((previousShift : WithTop ℚ) + middleDefect) := by
        simpa only [add_comm] using add_le_add_right hpreviousPrimary
          (currentShift : WithTop ℚ)
      _ = ((currentShift + previousShift : ℚ) : WithTop ℚ) +
          middleDefect := by
        rw [WithTop.coe_add]
        ac_rfl
  have htranslated := add_le_add_right hsourceBound
    ((-2 : ℚ) : WithTop ℚ)
  have hleftTranslate :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) =
        (b.alphaValue p : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue p + (-2 : ℚ) =
      b.alphaValue p by linarith [hbetaSource])
  have hrightTranslate :
      (((currentShift + previousShift : ℚ) : WithTop ℚ) +
          middleDefect) + ((-2 : ℚ) : WithTop ℚ) =
        ((currentShift + previousShift - 2 : ℚ) : WithTop ℚ) +
          middleDefect := by
    rw [sub_eq_add_neg, WithTop.coe_add]
    ac_rfl
  have htranslated' :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) ≤
        (((currentShift + previousShift : ℚ) : WithTop ℚ) +
          middleDefect) + ((-2 : ℚ) : WithTop ℚ) := by
    simpa only [add_comm] using htranslated
  rw [hleftTranslate, hrightTranslate] at htranslated'
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by have hi := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) =
      currentShift + previousShift - 2 := by
    rw [hsourceTwoStep]
    have htargetPrevious' :
        b.order ⟨i.val - 1, hiPrevious⟩ =
          a.order ⟨i.val - 1, hiPrevious⟩ + 2 := by
      rw [← hpCast]
      exact htargetPrevious
    rw [htargetPrevious']
    dsimp only [currentShift, previousShift]
    push_cast
    ring
  unfold representationSecondaryPreviousDefect
  rw [hcoefficient]
  simpa only [middleDefect, p] using htranslated'

end BONG.GoodBONG

end Bong
