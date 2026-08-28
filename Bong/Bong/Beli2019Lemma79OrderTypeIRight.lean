/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77TypeIRight
import Bong.Bong.Beli2019Lemma79OrderTypeIPrimaryCentral

/-!
# Beli (2019), Lemma 7.9(i): the nonterminal type-I right class

The right branch of Lemma 7.7 makes the alternating source prefix strictly
larger than the primary-candidate cut.  The generic primary core then applies
because the next source order is one above the corresponding target order.
Together with the already uniform secondary branch, this proves condition
2.1(i) at every even right-tail coordinate before the last difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- On the nonterminal type-I right tail, the self-prefix from Lemma 7.7 is
strictly above the primary-candidate coefficient cut. -/
theorem lemma79_typeI_even_sourcePrefix_gt_primaryCut_right
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hright : C.rightSwitch ≤ k) (hlast : k < D.profile.last) :
    (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0 (k + 2) := by
  have hdata := lemma77_typeI_right_data
    a b D C hfirst hrightLast hdefect k hkEven hright hlast
  have hcoefficientQ :
      ((a.order ⟨k, hk⟩ - a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 ≤
        0 := by
    exact_mod_cast hdata.1
  have hcap :
      ((((a.order ⟨k, hk⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤ a.prefixAlphaCap (k + 2) := by
    exact (WithTop.coe_le_coe.mpr hcoefficientQ).trans
      (a.prefixAlphaCap_nonneg (k + 2))
  have hself :
      ((((a.order ⟨k, hk⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
        WithTop ℚ) ≤
          a.truncatedPrefixDefect a ((-1) ^ ((k + 2) / 2)) 0
            (k + 2) := by
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [min_top_left]
    apply le_min
    · simpa only [alternatingPrefixDefect, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one] using hdata.2
    · exact hcap
  have hsourceCurrentLowerEntry : a.orderSequence.entryOrZero 0 ≤
      a.orderSequence.entryOrZero k :=
    a.orderSequence.entryOrZero_le_of_evenGap 0 k (Nat.zero_le k) hk
      hkEven
  have hsourceCurrentLower : a.order (0 : Fin (n + 2)) ≤
      a.order ⟨k, hk⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← a.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
    exact hsourceCurrentLowerEntry
  have hstrict :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) : WithTop ℚ) <
        ((((a.order ⟨k, hk⟩ -
          a.order ⟨k + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ) :
            WithTop ℚ) := by
    norm_cast
    linarith
  exact hstrict.trans_le hself

/-- A nonpositive primary candidate proves the adjacent-pair alternative on
the nonterminal even type-I right tail. -/
theorem lemma79_typeI_even_primary_data_right
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
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hright : C.rightSwitch ≤ k)
    (hlast : k < D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk)
    (hprimary : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0) :
    2 ≤ k ∧
      b.orderSequence.entry k hk +
          b.orderSequence.entry (k + 1) hkNext ≤
        c.orderSequence.entry (k - 1) (by omega) +
          c.orderSequence.entry k hk := by
  have hsource := lemma79_typeI_even_sourcePrefix_gt_primaryCut_right
    a b D C hfirst hrightLast hdefect k hk hkNext hkTwo hkEven
      hright hlast
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
  have hnextLast : k + 1 < D.profile.last := by
    rcases hkEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hnextOdd : Odd (k + 1) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hsourceTargetNext := lemma69_typeI_rightOdd_orders
    a b D C hfirst (k + 1) (by omega) hnextLast hnextOdd
  have hsourceTargetNextLower :
      b.orderSequence.entryOrZero (k + 1) + 1 ≤
        a.orderSequence.entryOrZero (k + 1) := by
    omega
  exact lemma79_typeI_even_primary_data_of_sourcePrefix
    a b c D C hfirst hnorm k hk hkNext hkTwo hkEven hleft hlast.le
      hnot hsource hsourceTargetNextLower hprimary

/-- Condition 2.1(i) at every even type-I right-tail coordinate strictly
before the last unequal order. -/
theorem beli2019Lemma79_i_typeI_rightEven
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
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hright : C.rightSwitch ≤ k)
    (hlast : k < D.profile.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hdirect : b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk
  · exact Or.inl hdirect
  · let idx : RepresentationIndex (n + 2) (n + 2) := {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le }
    have hAlpha := lemma79_typeI_even_alphaValue_le_zero_of_not_le
      a b c D C hfirst hdefectAC hnorm k hk hkNext hkEven hleft
        hlast.le hdirect
    have hHalf := lemma79_typeI_even_halfGap_pos_of_not_le
      a b c D C hfirst hinitial hnorm k hk hkNext hkEven hleft
        hlast.le hdirect
    have hcandidates :=
      a.representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
        c idx 0 (by simpa only [idx] using hAlpha) (by
          simpa only [idx] using hHalf)
    rcases hcandidates with hprimary | ⟨hi, hsecondary⟩
    · have hdata := lemma79_typeI_even_primary_data_right
        a b c D C hfirst hrightLast hdefectAB hnorm k hk hkNext hkTwo
          hkEven hleft hright hlast hdirect (by
            simpa only [idx] using hprimary)
      exact Or.inr ⟨by omega, hkNext, hdata.2⟩
    · have hpair := lemma79_typeI_even_pair_of_secondary_le_zero
        a b c D C hfirst k hk hkNext hkEven hleft (by
          simpa only [idx] using hi) (by
            simpa only [idx] using hsecondary)
      exact Or.inr ⟨by
        have := hi.1
        dsimp only [idx] at this
        omega, hkNext, hpair⟩

end BONG.GoodBONG

end Bong
