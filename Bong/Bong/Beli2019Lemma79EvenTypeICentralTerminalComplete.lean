/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeICentralAssembly
import Bong.Bong.Beli2019Lemma79EvenTypeILeftSwitch

/-!
# Beli (2019), Lemma 7.9(ii): terminal-complete central type-I interval

The terminal-complete form of Lemma 6.9(ii),(v) removes the old assumption
that the canonical right switch precedes the last unequal order.  This file
rebuilds the central candidate comparisons on that stronger interface.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The central identity `beta_i = alpha_i + 2`, valid also when the right
switch is the last unequal order. -/
theorem beli2019Lemma79_typeI_central_even_alphaShift_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ + 2 := by
  have hodd : Odd (i.val - 1) := by
    rcases hiEven with ⟨d, hd⟩
    have hip := i.pos
    exact ⟨d - 1, by omega⟩
  have hweight := a.beli2019Lemma69_v_typeI_from_conditions
    b D C hfirst horder hdefect (i.val - 1) hiLeft hiRight
  have hentry := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val - 1) hodd hiLeft hiRight.le
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hi := i.lt_large
    omega⟩
  have hweight' : a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
    simpa only [p] using hweight
  have horderShift : a.order p.castSucc = b.order p.castSucc + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1) + 2
    exact hentry
  have horderShiftQ : (a.order p.castSucc : ℚ) =
      (b.order p.castSucc : ℚ) + 2 := by
    exact_mod_cast horderShift
  unfold alphaLeftEndpoint at hweight'
  have hresult : b.alphaValue p = a.alphaValue p + 2 := by
    rw [horderShiftQ] at hweight'
    linarith
  simpa only [p] using hresult

set_option maxHeartbeats 3000000 in
-- Remark 6.16 is instantiated at the dependent following odd boundary.
/-- Primary-candidate comparison throughout the strict central interval,
including a terminal type-I profile. -/
theorem beli2019Lemma79_typeI_central_even_primary_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val < C.rightSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hentry := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven hiLeft hiRight.le
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  have hnextOdd : Odd nextIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hAlpha :=
    beli2019Lemma69_ii_typeI_targetValue_from_conditions_complete
      a b D C hfirst horderAB hdefectAB nextIdx hnextOdd
        (by simp only [nextIdx]; omega) (by simp only [nextIdx]; omega)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefectAB nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_two_of_order_eq_add_two
    a b c i horderShift hprefix

set_option maxHeartbeats 4000000 in
-- The two-step candidate transports dependent prefix and alpha indices.
/-- Secondary-candidate comparison throughout the central type-I interval,
including a terminal type-I profile. -/
theorem beli2019Lemma79_typeI_central_even_secondary_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hfarBound : i.val + 2 < n + 2 := by omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hfarLeft : C.leftSwitch ≤ farIdx.val - 1 := by
    simp only [farIdx]
    omega
  have hfarRight' : farIdx.val - 1 < C.rightSwitch := by
    simp only [farIdx]
    omega
  have hAlphaRaw :=
    (lemma69_typeI_central_values_from_conditions_complete
      a b D C hfirst horderAB hdefectAB farIdx
        hfarLeft hfarRight').2 hfarEven
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hf := farIdx.lt_large
        omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b farIdx]
    exact hAlphaRaw
  have hclose := beli2019Lemma79_typeI_central_even_alphaShift_complete
    a b D C hfirst horderAB hdefectAB farIdx hfarEven
      hfarLeft hfarRight'
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefectAB i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose.le)
  have hsumRaw := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst i.val hiLeft (by omega)
  apply representationSecondaryDefect_le_add_two_of_orderSum_eq
    a b c i hi
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hsumRaw.symm
  · exact hprefix

set_option maxHeartbeats 5000000 in
-- Candidate assembly carries dependent representation indices through the
-- terminal-complete Lemma 6.9 values.
/-- The scalar beta estimate on the strict central interval, without a
nonterminal-profile assumption. -/
theorem beli2019Lemma79_typeI_central_even_beta_complete
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  have halpha := beli2019Lemma79_typeI_central_even_alphaShift_complete
    a b D C hfirst horderAB hdefectAB i hiEven (by omega) (by omega)
  have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
    a b c D C hfirst i hiEven hiLeft.le (by omega)
  have hprimary := beli2019Lemma79_typeI_central_even_primary_complete
    a b c D C hfirst horderAB hdefectAB i hi.2 hiEven hiLeft.le
      (by omega)
  have hsecondary : ∀
      (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
      b.representationSecondaryDefect c i hi' ≤
        a.representationSecondaryDefect c i hi' +
          ((2 : ℚ) : WithTop ℚ) := by
    intro hi'
    exact beli2019Lemma79_typeI_central_even_secondary_complete
      a b c D C hfirst horderAB hdefectAB i hi' hiEven hiLeft.le
        hfarRight
  exact lemma79_even_beta_bound_of_candidate_shifts
    a b c hdefectAC i halpha hhalf hprimary hsecondary

set_option maxHeartbeats 5000000 in
-- The proof reuses the complete candidate and Lemma 7.6 assemblies.
/-- The source capped-prefix estimate on the strict central interval,
including a terminal type-I profile. -/
theorem beli2019Lemma79_typeI_central_even_sourceCapped_complete
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
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have hiTwo : 2 ≤ i.val := by omega
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousLeft : C.leftSwitch ≤ i.val - 2 := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hpreviousRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) hpreviousLeft (by omega) hpreviousEven
  have hcurrentRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le (by omega) hiEven
  have htwo : b.order ⟨i.val - 2, by omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpreviousRaw.symm.trans hcurrentRaw
  have hsourceGap := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceGap
  have hbeta := beli2019Lemma79_typeI_central_even_beta_complete
    a b c D C hfirst horderAB hdefectAB hdefectAC i hi hiEven
      hiLeft hfarRight
  exact beli2019Lemma76_typeI_central_sourceCapped_complete
    a b c D C hfirst i hi.2 hiEven hiLeft (by omega) hcross hbeta

set_option maxHeartbeats 5000000 in
-- Source and target self-prefix estimates are assembled at dependent indices.
/-- Lemma 7.9(ii) at strict central even type-I coordinates, with no
assumption that the right switch precedes the last unequal order. -/
theorem beli2019Lemma79_ii_typeI_even_central_complete
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
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by omega
  have hsource := beli2019Lemma79_typeI_central_even_sourceCapped_complete
    a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
      i hi hiEven hiLeft hfarRight
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousLeft : C.leftSwitch ≤ i.val - 2 := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hpreviousRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) hpreviousLeft (by omega) hpreviousEven
  have hcurrentRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le (by omega) hiEven
  have htwo : b.order ⟨i.val - 2, by omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpreviousRaw.symm.trans hcurrentRaw
  have hsourceGap := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceGap
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i hiTwo hiEven hiLeft.le (by omega) hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

set_option maxHeartbeats 5000000 in
-- The first-switch candidate comparison reuses both complete central candidates.
/-- The scalar beta estimate at the first canonical switch, including a
terminal type-I profile. -/
theorem beli2019Lemma79_typeI_leftSwitch_even_beta_complete
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hgapSmall : b.orderGap ⟨i.val - 1, by omega⟩ <
      2 * (ramificationIndex K : Int)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  have hleftTwo : 2 ≤ C.leftSwitch := by omega
  have halphaRaw :=
    beli2019Lemma79_typeI_leftSwitch_alphaShift_of_gap_lt_twoE
      a b D C hfirst hdefectAB hleftTwo (by
        simpa only [← hleftEq] using hgapSmall)
  have halpha : b.alphaValue ⟨i.val - 1, by omega⟩ =
      a.alphaValue ⟨i.val - 1, by omega⟩ + 2 := by
    simpa only [← hleftEq] using halphaRaw
  have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
    a b c D C hfirst i hiEven (by omega) (by omega)
  have hprimary := beli2019Lemma79_typeI_central_even_primary_complete
    a b c D C hfirst horderAB hdefectAB i hi.2 hiEven
      (by omega) (by omega)
  have hsecondary : ∀
      (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
      b.representationSecondaryDefect c i hi' ≤
        a.representationSecondaryDefect c i hi' +
          ((2 : ℚ) : WithTop ℚ) := by
    intro hi'
    exact beli2019Lemma79_typeI_central_even_secondary_complete
      a b c D C hfirst horderAB hdefectAB i hi' hiEven
        (by omega) hfarRight
  exact lemma79_even_beta_bound_of_candidate_shifts
    a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- The source self-prefix estimate at the first canonical switch, without
the old nonterminal-profile hypothesis. -/
theorem beli2019Lemma79_typeI_leftSwitch_even_sourceCapped_complete
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have htwoE := representationAlphaValue_le_twoE_of_crossGap_le
    b c i hcross
  have hleftPos : 0 < C.leftSwitch := by omega
  let current : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hupper : b.orderGap current ≤
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [current] using
      lemma79_typeI_leftSwitch_gap_le_twoE_add_one a b D C hleftPos
  by_cases hgap : b.orderGap current ≤
      2 * (ramificationIndex K : Int)
  · have hodd : Odd (b.orderGap current) := by
      simpa only [current] using
        lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
    rcases hodd with ⟨z, hz⟩
    have hgapSmall : b.orderGap current <
        2 * (ramificationIndex K : Int) := by
      omega
    have hbeta := beli2019Lemma79_typeI_leftSwitch_even_beta_complete
      a b c D C hfirst horderAB hdefectAB hdefectAC i hi hiEven
        hleftEq hfarRight (by
          simpa only [current, ← hleftEq] using hgapSmall)
    have hbetaTop : (b.representationAlphaValue c i : WithTop ℚ) ≤
        (b.alphaValue ⟨C.leftSwitch - 1, by omega⟩ : WithTop ℚ) := by
      exact_mod_cast (by simpa only [← hleftEq] using hbeta)
    have hboundary := beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst hleftPos
        (b.representationAlphaValue c i : WithTop ℚ) hbetaTop htwoE
    simpa only [← hleftEq] using hboundary
  · have hgapEq : b.orderGap current =
        2 * (ramificationIndex K : Int) + 1 := by
      omega
    have hcases := beli2019Lemma76_typeI a b D C hfirst hleftPos
    dsimp only at hcases
    let caseCurrent : Fin (n + 1) :=
      ⟨C.leftSwitch - 2 + 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩
    have hcurrentEq : caseCurrent = current := by
      apply Fin.ext
      simp only [caseCurrent, current]
      omega
    have hgapEq' : b.orderGap caseCurrent =
        2 * (ramificationIndex K : Int) + 1 := by
      rw [hcurrentEq]
      exact hgapEq
    have hlarge := htwoE.trans (hcases.2 hgapEq')
    simpa only [← hleftEq] using hlarge

/-- Lemma 7.9(ii) at the first central even type-I switch, including a
terminal type-I profile. -/
theorem beli2019Lemma79_ii_typeI_even_leftSwitch_complete
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
    (hiEven : Even i.val) (hleftEq : i.val = C.leftSwitch)
    (hfarRight : i.val + 2 ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsource :=
    beli2019Lemma79_typeI_leftSwitch_even_sourceCapped_complete
      a b c D C hfirst horderAB hdefectAB hdefectAC i hi hiEven
        hleftEq hfarRight hcross
  have htarget := beli2019Lemma79_typeI_central_even_target
    a b c D C hfirst hnorm i (by omega) hiEven (by omega) (by omega)
      hcross
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

end BONG.GoodBONG

end Bong
