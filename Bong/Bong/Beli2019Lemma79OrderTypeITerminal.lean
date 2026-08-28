/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77TypeITerminal
import Bong.Bong.Beli2019Lemma79OrderTypeIPrimaryCentral

/-!
# Beli (2019), Lemma 7.9(i): the terminal type-I class

This file treats the last unequal even coordinate in the type-I case. It is
the sole point where the common source-target suffix removes the one-unit
shift used by the nonterminal primary branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the last unequal type-I coordinate, Lemma 7.7 still puts the source
self-prefix strictly above the primary-candidate coefficient cut. -/
theorem lemma79_typeI_even_sourcePrefix_gt_primaryCut_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hkNext : D.profile.last + 1 < n + 2) :
    (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2) / 2)) 0
          (D.profile.last + 2) := by
  have hk := D.profile.lastDifference.bound
  have hdata := lemma77_typeI_terminal_data
    a b D C hfirst hrightLast hdefect hkNext
  have hcoefficientQ :
      ((a.order ⟨D.profile.last, hk⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 ≤ 0 := by
    exact_mod_cast hdata.1
  have hcap :
      ((((a.order ⟨D.profile.last, hk⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤ a.prefixAlphaCap (D.profile.last + 2) := by
    exact (WithTop.coe_le_coe.mpr hcoefficientQ).trans
      (a.prefixAlphaCap_nonneg (D.profile.last + 2))
  have hself :
      ((((a.order ⟨D.profile.last, hk⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤
          a.truncatedPrefixDefect a
            ((-1) ^ ((D.profile.last + 2) / 2)) 0
              (D.profile.last + 2) := by
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [min_top_left]
    apply le_min
    · simpa only [alternatingPrefixDefect, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one] using hdata.2
    · exact hcap
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) :=
    (D.profile.rightProfile
      (C.anchor_le_right.trans_lt hrightLast)).1
  have hlastEven : Even D.profile.last := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨e + d, by
      have hanchorLast := C.anchor_le_right.trans_lt hrightLast
      omega⟩
  have hsourceCurrentLowerEntry : a.orderSequence.entryOrZero 0 ≤
      a.orderSequence.entryOrZero D.profile.last :=
    a.orderSequence.entryOrZero_le_of_evenGap 0 D.profile.last
      (Nat.zero_le _) hk hlastEven
  have hsourceCurrentLower : a.order (0 : Fin (n + 2)) ≤
      a.order ⟨D.profile.last, hk⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← a.orderSequence_entryOrZero_eq_order ⟨D.profile.last, hk⟩]
    exact hsourceCurrentLowerEntry
  have hstrict :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        ((((a.order ⟨D.profile.last, hk⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
            WithTop ℚ) := by
    norm_cast
    linarith
  exact hstrict.trans_le hself

/-- At the terminal type-I coordinate the primary candidate cannot be
nonpositive: its mixed defect is nonnegative, while Lemma 7.7 makes the
candidate's order cut strictly negative. This is the terminal equality
exception in the paper, compressed to its decisive contradiction. -/
theorem lemma79_typeI_even_primary_impossible_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hkNext : D.profile.last + 1 < n + 2)
    (hnot : ¬ b.orderSequence.entry D.profile.last
        D.profile.lastDifference.bound ≤
      c.orderSequence.entry D.profile.last
        D.profile.lastDifference.bound)
    (hprimary : a.representationPrimaryDefect c {
      val := D.profile.last + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) : False := by
  have hk := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) :=
    (D.profile.rightProfile
      (C.anchor_le_right.trans_lt hrightLast)).1
  have hlastEven : Even D.profile.last := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨e + d, by
      have hanchorLast := C.anchor_le_right.trans_lt hrightLast
      omega⟩
  have hleftLast : C.leftSwitch ≤ D.profile.last :=
    C.left_le_anchor.trans
      (C.anchor_le_right.trans hrightLast.le)
  have hmixedLe := lemma79_typeI_even_primary_mixed_le_cut
    a b c D C hfirst hnorm D.profile.last hk hkNext hlastEven
      hleftLast le_rfl hnot hprimary
  have hterminalData := lemma77_typeI_terminal_data
    a b D C hfirst hrightLast hdefect hkNext
  have hterminalCoefficient :
      a.orderSequence.entryOrZero D.profile.last -
          a.orderSequence.entryOrZero (D.profile.last + 1) + 2 ≤ 0 := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hk,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hkNext]
    exact hterminalData.1
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceLast := C.source_after_right D.profile.last hrightLast
    le_rfl hlastDistance
  have hsourceNextLower :
      a.orderSequence.entryOrZero 0 + 3 ≤
        a.orderSequence.entryOrZero (D.profile.last + 1) := by
    omega
  have hcutNegativeInt :
      a.orderSequence.entryOrZero 0 + 1 -
          a.orderSequence.entryOrZero (D.profile.last + 1) < 0 := by
    omega
  have hcutNegative :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        0 := by
    rw [← a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← a.orderSequence_entryOrZero_eq_order
        ⟨D.profile.last + 1, hkNext⟩]
    norm_cast
  have hmixedNonnegative := a.truncatedPrefixDefect_nonneg
    c (-1) (D.profile.last + 2) D.profile.last
  exact (not_lt_of_ge hmixedNonnegative) (hmixedLe.trans_lt hcutNegative)

/-- Condition 2.1(i) at the last unequal type-I coordinate. -/
theorem beli2019Lemma79_i_typeI_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hkNext : D.profile.last + 1 < n + 2) :
    b.orderSequence.entry D.profile.last
        D.profile.lastDifference.bound ≤
        c.orderSequence.entry D.profile.last
          D.profile.lastDifference.bound ∨
      ∃ (hk0 : 0 < D.profile.last)
          (hkNext' : D.profile.last + 1 < n + 2),
        b.orderSequence.entry D.profile.last
              D.profile.lastDifference.bound +
            b.orderSequence.entry (D.profile.last + 1) hkNext' ≤
          c.orderSequence.entry (D.profile.last - 1) (by omega) +
            c.orderSequence.entry D.profile.last
              D.profile.lastDifference.bound := by
  have hk := D.profile.lastDifference.bound
  by_cases hdirect : b.orderSequence.entry D.profile.last hk ≤
      c.orderSequence.entry D.profile.last hk
  · exact Or.inl hdirect
  · have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hlastDistance : Even (D.profile.last - D.anchor) :=
      (D.profile.rightProfile
        (C.anchor_le_right.trans_lt hrightLast)).1
    have hlastEven : Even D.profile.last := by
      rcases hlastDistance with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨e + d, by
        have hanchorLast := C.anchor_le_right.trans_lt hrightLast
        omega⟩
    have hleftLast : C.leftSwitch ≤ D.profile.last :=
      C.left_le_anchor.trans
        (C.anchor_le_right.trans hrightLast.le)
    let idx : RepresentationIndex (n + 2) (n + 2) := {
      val := D.profile.last + 1
      pos := by
        have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
          a b D C hfirst hrightLast
        omega
      lt_large := hkNext
      le_small := hkNext.le }
    have hAlpha := lemma79_typeI_even_alphaValue_le_zero_of_not_le
      a b c D C hfirst hdefectAC hnorm D.profile.last hk hkNext
        hlastEven hleftLast le_rfl hdirect
    have hHalf := lemma79_typeI_even_halfGap_pos_of_not_le
      a b c D C hfirst hinitial hnorm D.profile.last hk hkNext
        hlastEven hleftLast le_rfl hdirect
    have hcandidates :=
      a.representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
        c idx 0 (by simpa only [idx] using hAlpha) (by
          simpa only [idx] using hHalf)
    rcases hcandidates with hprimary | ⟨hi, hsecondary⟩
    · exact False.elim (lemma79_typeI_even_primary_impossible_terminal
        a b c D C hfirst hrightLast hdefectAB hnorm hkNext hdirect (by
          simpa only [idx] using hprimary))
    · have hpair := lemma79_typeI_even_pair_of_secondary_le_zero
        a b c D C hfirst D.profile.last hk hkNext hlastEven hleftLast (by
          simpa only [idx] using hi) (by
            simpa only [idx] using hsecondary)
      exact Or.inr ⟨by
        have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
          a b D C hfirst hrightLast
        omega, hkNext, hpair⟩

end BONG.GoodBONG

end Bong
