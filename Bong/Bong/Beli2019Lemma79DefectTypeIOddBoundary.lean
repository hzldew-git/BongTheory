/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76CanonicalBoundary
import Bong.Bong.Beli2019Lemma79DefectTypeIOddEarly

/-!
# Beli (2019), Lemma 7.9(ii): the exceptional type-I odd coordinate

At the paper coordinate `i = t - 2`, the two-step target orders no longer
agree.  Lemma 7.6 identifies their skip by one, and Corollary 2.9(ii)
bounds the intervening alpha by the odd order gap.  This recovers exactly
the next-alpha estimate needed by the common odd-coordinate argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The special next-alpha estimate at the canonical type-I switch. -/
theorem lemma79_typeI_leftSwitch_nextAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch) :
    b.alphaValue ⟨C.leftSwitch - 1, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤
      ((b.orderSequence.entryOrZero (C.leftSwitch - 2) -
        b.orderSequence.entryOrZero (C.leftSwitch - 1) + 1 : Int) : ℚ) := by
  let gap : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hgapOdd : Odd (b.orderGap gap) := by
    simpa only [gap] using
      a.lemma76_leftSwitch_gap_odd b D C hfirst hleftPos
  have halphaGap : b.alphaValue gap ≤ (b.orderGap gap : ℚ) := by
    rw [b.beli2009Corollary29_ii gap hgapOdd]
    exact min_le_right _ _
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpreviousBound : C.leftSwitch - 2 < n + 2 := by omega
  have hskipEntries :
      b.orderSequence.entryOrZero C.leftSwitch =
        b.orderSequence.entryOrZero (C.leftSwitch - 2) + 1 := by
    rw [b.orderSequence_entryOrZero_eq_order
        ⟨C.leftSwitch, hleftBound⟩,
      b.orderSequence_entryOrZero_eq_order
        ⟨C.leftSwitch - 2, hpreviousBound⟩]
    exact a.lemma76_leftSwitch_skip b D C hleftPos
  have hgapEntries : b.orderGap gap =
      b.orderSequence.entryOrZero C.leftSwitch -
        b.orderSequence.entryOrZero (C.leftSwitch - 1) := by
    unfold orderGap
    rw [← b.orderSequence_entryOrZero_eq_order gap.succ,
      ← b.orderSequence_entryOrZero_eq_order gap.castSucc]
    simp only [gap, Fin.val_succ, Fin.val_castSucc]
    congr 2 <;> omega
  have hgapIdentity : b.orderGap gap =
      b.orderSequence.entryOrZero (C.leftSwitch - 2) -
        b.orderSequence.entryOrZero (C.leftSwitch - 1) + 1 := by
    rw [hgapEntries, hskipEntries]
    omega
  have hbound : b.alphaValue gap ≤
      ((b.orderSequence.entryOrZero (C.leftSwitch - 2) -
        b.orderSequence.entryOrZero (C.leftSwitch - 1) + 1 : Int) : ℚ) := by
    calc
      b.alphaValue gap ≤ (b.orderGap gap : ℚ) := halphaGap
      _ = ((b.orderSequence.entryOrZero (C.leftSwitch - 2) -
          b.orderSequence.entryOrZero (C.leftSwitch - 1) + 1 : Int) : ℚ) := by
        exact_mod_cast hgapIdentity
  simpa only [gap] using hbound

/-- Lemma 7.9(ii), case 2, at the exceptional type-I coordinate
`i = t - 2`. -/
theorem beli2019Lemma79_ii_typeI_odd_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val + 1 = C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  rcases C.left_even with ⟨d, hd⟩
  have hodd : Odd i.val := ⟨d - 1, by omega⟩
  have hkEven : Even k := ⟨d - 1, by
    simp only [k]
    omega⟩
  have hkLeft : k < C.leftSwitch := by
    simp only [k]
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
    omega
  have hswitchAlpha := a.lemma79_typeI_leftSwitch_nextAlpha
    b D C hfirst hleftPos
  have hiEq : i.val = C.leftSwitch - 1 := by omega
  have hkEq : i.val - 1 = C.leftSwitch - 2 := by omega
  have hnextAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
    calc
      b.alphaValue ⟨i.val, by omega⟩ =
          b.alphaValue ⟨C.leftSwitch - 1, by omega⟩ := by
        congr 1
        apply Fin.ext
        exact hiEq
      _ ≤ ((b.orderSequence.entryOrZero (C.leftSwitch - 2) -
          b.orderSequence.entryOrZero (C.leftSwitch - 1) + 1 : Int) : ℚ) :=
        hswitchAlpha
      _ = ((b.orderSequence.entryOrZero (i.val - 1) -
          b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
        rw [hkEq, hiEq]
  have haZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hbZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have hbPrevious := C.target_before_left k hkLeft hkEven
  have hfirstTarget : b.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero 0 + 1 := by
    rw [hbZero, haZero]
  have hcurrentTarget : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero 0 + 1 := by
    simpa only [k, haZero] using hbPrevious
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpairParity : Even (D.anchor - k) := by
    rcases hanchorEven with ⟨e, he⟩
    refine ⟨e - (d - 1), ?_⟩
    have hkAnchor : k ≤ D.anchor := by
      exact (Nat.le_of_lt hkLeft).trans C.left_le_anchor
    simp only [k] at hkAnchor ⊢
    omega
  have hpairRaw := D.profile.leftPairEq k (by
    have hleftAnchor := C.left_le_anchor
    simp only [k]
    omega) hpairParity
  have hpairSource : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero (i.val - 1) +
        a.orderSequence.entryOrZero i.val := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hpairRaw.symm
  exact lemma79_ii_of_odd_profile a b c hac hnorm i hiNext hodd
    hnextAlpha hfirstTarget hcurrentTarget hpairSource

end BONG.GoodBONG

end Bong
