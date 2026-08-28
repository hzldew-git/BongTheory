/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitch
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.9(ii): the terminal type-I right switch

When the canonical right switch is the last unequal order, its successor is
already in the common suffix.  The primary candidate is therefore controlled
by Lemma 6.3.  For the secondary candidate the adjacent order sum shifts by
two and Remark 6.16 compares the mixed prefix; at full prefix length the same
comparison is the full-left change identity.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- Lemma 6.3 is instantiated at the first common-suffix coordinate.
/-- Primary-candidate comparison at a terminal canonical right switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_primary_terminal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  have hentry := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven hiLeft hrightEq.le
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  have hAlpha := a.beli2019Lemma63_sameRank_right_value
    b hdefect nextIdx (by
      intro k hk hkn
      exact D.profile.lastDifference.after k (by
        simp only [nextIdx] at hk
        omega) hkn)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_two_of_order_eq_add_two
    a b c i horderShift hprefix

set_option maxHeartbeats 4000000 in
-- The full-prefix and proper-suffix mixed-prefix comparisons are distinct.
/-- Secondary-candidate comparison at a terminal canonical right switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_secondary_terminal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  have hentry := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven hiLeft hrightEq.le
  have hnextCommon : a.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val + 1) :=
    D.profile.lastDifference.after (i.val + 1) (by omega) (by omega)
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextOrder : b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnextCommon.symm
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 2 := by
    rw [hcurrentOrder, hnextOrder]
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
  exact representationSecondaryDefect_le_add_two_of_orderSum_eq_add_two
    a b c i hi hsum hprefix

set_option maxHeartbeats 5000000 in
-- The small-gap branch compares all three terminal candidates.
/-- Scalar beta estimate at a terminal canonical right switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_beta_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap previous
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross (by simpa only [previous] using hlarge)
  · have hsmall : b.orderGap previous <
        2 * (ramificationIndex K : Int) := lt_of_not_ge hlarge
    have hiLeft : C.leftSwitch ≤ i.val := by
      rw [hrightEq]
      exact C.left_le_anchor.trans C.anchor_le_right
    have halpha : b.alphaValue ⟨i.val - 1, by omega⟩ =
        a.alphaValue ⟨i.val - 1, by omega⟩ + 2 := by
      by_cases hswitch : C.leftSwitch < C.rightSwitch
      · have hleftAlpha : C.leftSwitch ≤ i.val - 1 := by
          rcases C.left_even with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          omega
        exact beli2019Lemma79_typeI_central_even_alphaShift_complete
          a b D C hfirst horderAB hdefectAB i hiEven hleftAlpha
            (by omega)
      · have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
          C.left_le_anchor.trans C.anchor_le_right
        have hswitchEq : C.leftSwitch = C.rightSwitch := by omega
        have hleftEq : i.val = C.leftSwitch :=
          hrightEq.trans hswitchEq.symm
        have hraw :=
          beli2019Lemma79_typeI_leftSwitch_alphaShift_of_gap_lt_twoE
            a b D C hfirst hdefectAB (by omega) (by
              simpa only [previous, hleftEq] using hsmall)
        simpa only [hleftEq] using hraw
    have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
      a b c D C hfirst i hiEven hiLeft hrightEq.le
    have hprimary :=
      beli2019Lemma79_typeI_rightSwitch_even_primary_terminal
        a b c D C hfirst hrightLast hdefectAB i hi.2 hiEven hrightEq
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeI_rightSwitch_even_secondary_terminal
        a b c D C hfirst hrightLast hdefectAB i hi' hiEven hrightEq
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- Source self-prefix estimate at a terminal canonical right switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_sourceCapped_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have hbeta := beli2019Lemma79_typeI_rightSwitch_even_beta_terminal
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      i hi hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  by_cases hstrict : C.leftSwitch < i.val
  · exact beli2019Lemma76_typeI_central_sourceCapped_complete
      a b c D C hfirst i hi.2 hiEven hstrict hrightEq.le hcross hbeta
  · have hleftEq : i.val = C.leftSwitch := by omega
    have hbetaTop : (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨C.leftSwitch - 1, by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega⟩ : WithTop ℚ) := by
      exact_mod_cast (by simpa only [hleftEq] using hbeta)
    have htwoE := representationAlphaValue_le_twoE_of_crossGap_le
      b c i hcross
    have hboundary := beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst (by omega)
        (b.representationAlphaValue c i : WithTop ℚ) hbetaTop htwoE
    simpa only [hleftEq] using hboundary

/-- Lemma 7.9(ii) at a terminal canonical right switch. -/
theorem beli2019Lemma79_ii_typeI_even_rightSwitch_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsource :=
    beli2019Lemma79_typeI_rightSwitch_even_sourceCapped_terminal
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        i hi hiEven hrightEq hcross
  have hiLeft : C.leftSwitch ≤ i.val := by
    rw [hrightEq]
    exact C.left_le_anchor.trans C.anchor_le_right
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i (by omega) hiEven hiLeft hrightEq.le hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

/-- Lemma 7.9(ii) at the canonical right switch, dispatching between a
proper and terminal type-I profile. -/
theorem beli2019Lemma79_ii_typeI_even_rightSwitch_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hrightEq : i.val = C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
  · exact beli2019Lemma79_ii_typeI_even_rightSwitch
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        hnorm i hi hiEven hrightEq hcross
  · exact beli2019Lemma79_ii_typeI_even_rightSwitch_terminal
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        hnorm i hi hiEven hrightEq hcross

end BONG.GoodBONG

end Bong
