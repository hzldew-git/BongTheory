/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeft
import Bong.Bong.Beli2019Lemma79DefectOddProfile

/-!
# Beli (2019), Lemma 7.9(ii): early odd coordinates in type I

Before the last odd coordinate preceding the canonical type-I switch, the
two surrounding even target orders agree.  Property P1 and Lemma 6.9(i)
then give the next-alpha estimate, while Lemma 6.7 gives the adjacent-pair
identity needed by the common odd-coordinate assembly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 2, at an odd type-I coordinate strictly before
the exceptional coordinate `t - 2`. -/
theorem beli2019Lemma79_ii_typeI_odd_early
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
    (hodd : Odd i.val) (hearly : i.val + 1 < C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  rcases hodd with ⟨d, hd⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hkLeft : k < C.leftSwitch := by
    simp only [k]
    omega
  have hfarLeft : i.val + 1 < C.leftSwitch := hearly
  have hiNext : i.val + 1 < n + 2 := by
    have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
    omega
  have hiAlpha : i.val < n + 1 := by omega
  have hkAlpha : k < n + 1 := by
    simp only [k]
    omega
  have hpreviousAlpha := a.beli2019Lemma69_i_typeI_targetLeftTail
    b D C hfirst hleftPos k hkLeft hkEven
  have hbPrevious := C.target_before_left k hkLeft hkEven
  have hbFar := C.target_before_left (i.val + 1) hfarLeft hfarEven
  have htwoStep : b.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hbFar.trans hbPrevious.symm
  let alphaIndex : Fin (n + 1) := ⟨i.val, hiAlpha⟩
  have hnextAlpha := b.nextAlphaValue_le_of_twoStep_eq
    alphaIndex i.pos (by simpa only [alphaIndex] using htwoStep) (by
      simpa only [alphaIndex, k] using hpreviousAlpha)
  have hnextAlpha' : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
    simpa only [alphaIndex] using hnextAlpha
  have haZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hbZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
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
    refine ⟨e - d, ?_⟩
    have hkAnchor : k ≤ D.anchor := by
      exact (Nat.le_of_lt hkLeft).trans C.left_le_anchor
    simp only [k] at hd hkAnchor ⊢
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
  exact lemma79_ii_of_odd_profile a b c hac hnorm i hiNext
    ⟨d, hd⟩ hnextAlpha' hfirstTarget hcurrentTarget hpairSource

end BONG.GoodBONG

end Bong
