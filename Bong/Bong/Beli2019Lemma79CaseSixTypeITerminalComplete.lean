/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixTypeIAssembly
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.9(ii), case 6: terminal-complete type I

The published interval is `t' < i < u`.  Since difference-profile coordinates
are zero based, its final Lean coordinate is `i = last`, not `i < last`.
At that endpoint the next source and intermediate orders already lie in the
common suffix.  Lemma 6.3 therefore replaces the strict right-tail alpha
formula; if the relevant prefix is full, invariance under changing a BONG of
the same quadratic space replaces it directly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- The endpoint uses either a full prefix or the first common-suffix alpha.
/-- The primary one-unit candidate comparison through the last unequal
type-I coordinate. -/
theorem beli2019Lemma79_typeI_caseSix_primary_le_add_one_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ) := by
  by_cases hbeforeLast : i.val < D.profile.last
  · have hrightLast : C.rightSwitch < D.profile.last :=
      hright.trans hbeforeLast
    exact beli2019Lemma79_typeI_caseSix_primary_le_add_one
      a b c D C hfirst hrightLast hdefect i hright hbeforeLast hiEven
  · have hiLast : i.val = D.profile.last := by omega
    have hcurrentRaw := lemma79_typeI_caseSix_current_eq_source_add_one
      a b D C hfirst i hright hthroughLast hiEven
    have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.val, i.lt_large⟩ + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hcurrentRaw
    have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
        (i.val - 1) ≤
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      by_cases hfull : i.val + 1 = n + 2
      · simpa only [hfull] using
          (truncatedPrefixDefect_fullLeft_change
            a b c (-1) (i.val - 1)).le
      · have hnextBound : i.val + 1 < n + 2 := by
          have hiBound := i.lt_large
          omega
        let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
        have hAlpha := a.beli2019Lemma63_sameRank_right_value
          b hdefect nextIdx (by
            intro k hk hkn
            exact D.profile.lastDifference.after k (by
              simp only [nextIdx] at hk
              omega) hkn)
        have hformula := beli2019Remark616_rightMixedPrefix_at
          a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
        simpa only [nextIdx] using
          (hformula.le.trans (min_le_left _ _))
    exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
      a b c i hcurrent hprefix

set_option maxHeartbeats 4000000 in
-- The adjacent order sum shifts by one; the following order is common.
/-- The secondary one-unit candidate comparison through the last unequal
type-I coordinate. -/
theorem beli2019Lemma79_typeI_caseSix_secondary_le_add_one_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  by_cases hbeforeLast : i.val < D.profile.last
  · have hrightLast : C.rightSwitch < D.profile.last :=
      hright.trans hbeforeLast
    exact beli2019Lemma79_typeI_caseSix_secondary_le_add_one
      a b c D C hfirst hrightLast hdefect i hi hright hbeforeLast hiEven
  · have hiLast : i.val = D.profile.last := by omega
    have hcurrentRaw := lemma79_typeI_caseSix_current_eq_source_add_one
      a b D C hfirst i hright hthroughLast hiEven
    have hnextCommon : a.orderSequence.entryOrZero (i.val + 1) =
        b.orderSequence.entryOrZero (i.val + 1) :=
      D.profile.lastDifference.after (i.val + 1) (by omega) hi.2
    have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.val, i.lt_large⟩ + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hcurrentRaw
    have hnext : b.order ⟨i.val + 1, hi.2⟩ =
        a.order ⟨i.val + 1, hi.2⟩ := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hnextCommon.symm
    have hsum : b.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val + 1, hi.2⟩ =
        a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ + 1 := by
      rw [hcurrent, hnext]
      omega
    have hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
        (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
      by_cases hfull : i.val + 2 = n + 2
      · simpa only [hfull] using
          (truncatedPrefixDefect_fullLeft_change
            a b c 1 (i.val - 2)).le
      · have hfarBound : i.val + 2 < n + 2 := by omega
        let farIdx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
        have hAlpha := a.beli2019Lemma63_sameRank_right_value
          b hdefect farIdx (by
            intro k hk hkn
            exact D.profile.lastDifference.after k (by
              simp only [farIdx] at hk
              omega) hkn)
        have hformula := beli2019Remark616_rightMixedPrefix_at
          a b c hdefect farIdx hAlpha 1 (i.val - 2)
        calc
          b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
              min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
                (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
            simpa only [farIdx,
              show i.val + 2 - 1 = i.val + 1 by omega] using hformula
          _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
            min_le_left _ _
    exact representationSecondaryDefect_le_add_one_of_orderSum_eq_add_one
      a b c i hi hsum hprefix

set_option maxHeartbeats 5000000 in
-- Candidatewise comparison also covers the final representation coordinate.
/-- The one-unit alpha comparison on the whole type-I case-6 interval. -/
theorem beli2019Lemma79_typeI_caseSix_alpha_le_add_one_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact lemma79_typeI_caseSix_halfGap_le_add_one
      a b c D C hfirst i hright hthroughLast hiEven
  · exact beli2019Lemma79_typeI_caseSix_primary_le_add_one_complete
      a b c D C hfirst hdefect i hright hthroughLast hiEven
  · intro hi
    exact beli2019Lemma79_typeI_caseSix_secondary_le_add_one_complete
      a b c D C hfirst hdefect i hi hright hthroughLast hiEven

set_option maxHeartbeats 6000000 in
-- The zero-alpha branch consumes the already established order condition.
/-- The complete first comparison-parity branch, including `i = last` and
the full-prefix endpoint. -/
theorem beli2019Lemma79_typeI_caseSix_firstParity_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hrightLast : C.rightSwitch < D.profile.last :=
    hright.trans_le hthroughLast
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · have hshift := beli2019Lemma79_typeI_caseSix_alpha_le_add_one_complete
      a b c D C hfirst hdefectAB i hright hthroughLast hiEven
    have hpreviousRight : C.rightSwitch < i.val - 1 := by
      rcases hiEven with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    have hpreviousOdd : Odd (i.val - 1) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hbeta := beli2019Remark613_typeI_targetRightAlpha_eq_one
      a b D C hfirst hrightLast hdefectAB (i.val - 1)
        hpreviousRight (by omega) hpreviousOdd
    exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
      a b c hdefectAC i hshift hbeta
        (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    have hsequence :=
      (b.representationOrderCondition_iff c le_rfl).mp horderBC
    rcases hsequence.compare i.val i.lt_large with
      hcurrent | ⟨hi0, hiNext, hpair⟩
    · apply lemma79_caseSix_of_gamma_eq_zero_and_current_order b c i
      · simpa only [orderSequence_at] using hcurrent
      · simpa only [previous] using hgammaZero
    · exact lemma79_caseSix_of_gamma_eq_zero_and_compare
        b c i hiNext (Or.inr ⟨hi0, hiNext, hpair⟩)
          (by simpa only [previous] using hgammaZero)

set_option maxHeartbeats 7000000 in
-- Both comparison-prefix parities now include the profile endpoint.
/-- Lemma 7.9(ii), case 6, on the complete even type-I right interval. -/
theorem beli2019Lemma79_ii_typeI_caseSix_terminalComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeI_caseSix_prefix_opposite
    a b D C hfirst i hright hthroughLast hiEven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeI_caseSix_firstParity_complete
      a b c D C hfirst hdefectAB hdefectAC horderBC i hright
        hthroughLast hiEven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeI_caseSix_secondParity
      a b c D C hfirst hnorm i hright hthroughLast hiEven hsecondParity.1

end BONG.GoodBONG

end Bong
