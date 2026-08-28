/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeICentral
import Bong.Bong.Beli2019Lemma79OrderTypeICentralComplete

/-!
# Beli (2019), Lemma 7.9(i): endpoint-complete central type-I class

The central even-coordinate argument does not require the right switch to
precede the last unequal coordinate.  The endpoint-complete form of Lemma
7.7 supplies the only place where that restriction occurred.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A nonpositive primary candidate gives the adjacent-pair alternative at
every even coordinate strictly between the canonical switches, including
when the right switch is the last unequal coordinate. -/
theorem lemma79_typeI_even_primary_data_completeCentral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hright : k < C.rightSwitch)
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
  have hsource := lemma79_typeI_even_sourcePrefix_gt_primaryCut_completeCentral
    a b D C hfirst horder hdefect k hkNext hkTwo hkEven hleft hright
  have hnextOdd : Odd (k + 1) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hsourceTargetNext := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (k + 1) hnextOdd (by omega) (by omega)
  have hsourceTargetNextLower :
      b.orderSequence.entryOrZero (k + 1) + 1 ≤
        a.orderSequence.entryOrZero (k + 1) := by
    omega
  exact lemma79_typeI_even_primary_data_of_sourcePrefix
    a b c D C hfirst hnorm k hk hkNext hkTwo hkEven hleft hlast
      hnot hsource hsourceTargetNextLower hprimary

/-- Condition 2.1(i) on every even coordinate strictly between the
canonical type-I switches, with no nonterminal-switch hypothesis. -/
theorem beli2019Lemma79_i_typeI_centralEven_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hright : k < C.rightSwitch) :
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
      a b c D C hfirst hdefectAC hnorm k hk hkNext hkEven hleft hlast
        hdirect
    have hHalf := lemma79_typeI_even_halfGap_pos_of_not_le
      a b c D C hfirst hinitial hnorm k hk hkNext hkEven hleft hlast
        hdirect
    have hcandidates :=
      a.representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
        c idx 0 (by simpa only [idx] using hAlpha) (by
          simpa only [idx] using hHalf)
    rcases hcandidates with hprimary | ⟨hi, hsecondary⟩
    · have hdata := lemma79_typeI_even_primary_data_completeCentral
        a b c D C hfirst hab hdefectAB hnorm k hk hkNext hkTwo hkEven
          hleft hlast hright hdirect (by
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
