/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralExclusions
import Bong.Bong.Beli2019Lemma69TypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAlpha
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(iii), case 2: the type-I middle interval

At an odd boundary between the two canonical type-I switches, the first
alternative of Lemma 2.18 gives the first Lemma 1.5 diagram.  Lemma 6.9
identifies the current comparison invariant with the target alpha.  The
neighboring even comparison invariants are source alphas, while Remark 6.13
puts the corresponding target alphas at most two units above them.  Those
two units are exactly cancelled by the alternating order shift.

Remark 6.16 performs the same cancellation when the active `(b,c)` trigger
is transferred to `(a,c)`.  The other Lemma 2.18 alternative is impossible
at an odd middle boundary by the constant even-order plateau.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- On an odd order coordinate strictly between the canonical switches,
the target alpha is the source alpha plus two. -/
theorem lemma79Central_typeI_oddTargetAlpha_eq_source_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (k : Nat) (hkOdd : Odd k)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    b.alphaValue ⟨k, by
        have hlast := C.right_le_last
        have hbound := D.profile.lastDifference.bound
        omega⟩ =
      a.alphaValue ⟨k, by
        have hlast := C.right_le_last
        have hbound := D.profile.lastDifference.bound
        omega⟩ + 2 := by
  let p : Fin (n + 1) := ⟨k, by
    have hlast := C.right_le_last
    have hbound := D.profile.lastDifference.bound
    omega⟩
  have hweight := a.beli2019Lemma69_v_typeI_from_conditions
    b D C hfirst hab.orderCondition hab.defectCondition k hleft hright
  have hgapEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst k hkOdd hleft hright.le
  have hgap : a.order p.castSucc = b.order p.castSucc + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    simpa only [p, Fin.val_castSucc] using hgapEntries
  change a.alphaLeftEndpoint p = b.alphaLeftEndpoint p at hweight
  unfold alphaLeftEndpoint at hweight
  rw [hgap] at hweight
  push_cast at hweight
  simpa only [p] using (show b.alphaValue p = a.alphaValue p + 2 by
    linarith)

/-- Every even comparison invariant in the canonical middle interval is
the corresponding source alpha. -/
theorem lemma79Central_typeI_evenValue_eq_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (j : RepresentationIndex (n + 2) (n + 2)) (hjEven : Even j.val)
    (hleft : C.leftSwitch ≤ j.val - 1)
    (hright : j.val - 1 < C.rightSwitch) :
    a.representationAlphaValue b j =
      a.alphaValue ⟨j.val - 1, by
        have := j.lt_large
        omega⟩ := by
  have hvalue :=
    (lemma69_typeI_central_values_from_conditions_complete
      a b D C hfirst hab.orderCondition hab.defectCondition
        j hleft hright).2 hjEven
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b j]
  exact hvalue

/-- At an odd middle boundary, the preceding comparison invariant is the
source alpha immediately to its left.  The first-switch endpoint is supplied
by the left-profile form of Lemma 6.9(ii). -/
theorem lemma79Central_typeI_previousValue_eq_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val) :
    a.representationAlphaValue b i.previous =
      a.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ := by
  have hpreviousEven : Even i.previous.val := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by simp only [CentralRepresentationIndex.previous]; omega⟩
  by_cases hboundary : i.val = C.leftSwitch + 1
  · have hleftTwo : 1 < C.leftSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      have := i.one_lt
      omega
    have hvalue := a.beli2019Lemma69_ii_typeI_sourceLeftValue_complete
      b D C hfirst hab.defectCondition i.previous (by
        simp only [CentralRepresentationIndex.previous]
        omega) (by
        simp only [CentralRepresentationIndex.previous]
        omega) hpreviousEven
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b i.previous]
    simpa only [CentralRepresentationIndex.previous,
      show i.val - 1 - 1 = i.val - 2 by omega] using hvalue
  · apply lemma79Central_typeI_evenValue_eq_sourceAlpha
      a b D C hfirst hab i.previous hpreviousEven
    · simp only [CentralRepresentationIndex.previous]
      rcases C.left_even with ⟨d, hd⟩
      rcases hiOdd with ⟨e, he⟩
      omega
    · simp only [CentralRepresentationIndex.previous]
      omega

/-- The target alpha preceding an odd middle boundary is at most two above
the preceding comparison invariant. -/
theorem lemma79Central_typeI_previousAlpha_le_value_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val) :
    b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ ≤
      a.representationAlphaValue b i.previous + 2 := by
  have hvalue := lemma79Central_typeI_previousValue_eq_sourceAlpha
    a b D C hfirst hab i hleft hright hiOdd
  by_cases hboundary : i.val = C.leftSwitch + 1
  · have hleftTwo : 2 ≤ C.leftSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      have := i.one_lt
      omega
    have hclose := beli2019Lemma79_typeI_leftSwitch_alphaClose
      a b D C hfirst hab.defectCondition hleftTwo
    simpa only [hboundary,
      show C.leftSwitch + 1 - 2 = C.leftSwitch - 1 by omega,
      hvalue] using hclose
  · have hiPreviousOdd : Odd (i.val - 2) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hshift := lemma79Central_typeI_oddTargetAlpha_eq_source_add_two
      a b D C hfirst hab (i.val - 2) hiPreviousOdd (by
        rcases C.left_even with ⟨d, hd⟩
        rcases hiOdd with ⟨e, he⟩
        omega) (by omega)
    rw [hvalue]
    exact hshift.le

/-- The current comparison invariant at an odd middle boundary is exactly
the current target alpha. -/
theorem lemma79Central_typeI_currentValue_eq_targetAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val) :
    a.representationAlphaValue b (i.current i.lt_large.le) =
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  apply a.beli2019Lemma69_ii_typeI_targetValue_from_conditions_complete
    b D C hfirst hab.orderCondition hab.defectCondition
      (i.current i.lt_large.le) hiOdd
  · simp only [CentralRepresentationIndex.current]
    rcases C.left_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  · simp only [CentralRepresentationIndex.current]
    rcases C.right_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega

/-- The first adjacent-alpha alternative activates condition (iii) for
`(a,b)` at an odd type-I middle boundary. -/
theorem lemma79Central_typeIMiddle_odd_triggerAB
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    a.centralAlphaTrigger b i := by
  have hrightStrict : i.val < C.rightSwitch := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  have hcurrentEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val hiOdd hleft.le hright
  have hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentEntries
  have hmiddleEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hmiddleEntries := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst (i.val - 1) hmiddleEven (by
      rcases C.left_even with ⟨d, hd⟩
      rcases hiOdd with ⟨e, he⟩
      omega) (by omega)
  have hmiddleOrder : b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hmiddleEntries
  have htargetCross := b.order_twoStep_lt_of_alphaSum_gt_twoE i hsum
  have hpreviousClose :=
    lemma79Central_typeI_previousAlpha_le_value_add_two
      a b D C hfirst hab i hleft hright hiOdd
  have hcurrentValue := lemma79Central_typeI_currentValue_eq_targetAlpha
    a b D C hfirst hab i hleft hright hiOdd
  constructor
  · exact htargetCross.trans (by omega)
  · unfold centralAdjustedAlpha
    rw [dif_pos i.lt_large.le]
    norm_cast
    push_cast
    rw [hcurrentValue]
    have hpreviousLower :
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ - 2 ≤
        a.representationAlphaValue b i.previous := by
      linarith
    have hmiddleOrderQ :
        (b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) =
        (a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) + 2 := by
      exact_mod_cast hmiddleOrder
    linarith

/-- The active `(b,c)` central trigger transfers to `(a,c)` at an odd
type-I middle boundary.  The loss of two in the right mixed prefix is
cancelled by the two-unit order shift. -/
theorem lemma79Central_typeIMiddle_odd_triggerAC
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val) (htriggerBC : b.centralAlphaTrigger c i) :
    a.centralAlphaTrigger c i := by
  have hiNext : i.val + 1 < n + 2 := by
    have hlast := C.right_le_last
    have hbound := D.profile.lastDifference.bound
    rcases C.right_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  have hcurrentValue : a.representationAlphaValue b currentIdx =
      b.alphaValue ⟨currentIdx.val - 1, by
        have := currentIdx.lt_large
        omega⟩ := by
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      lemma79Central_typeI_currentValue_eq_targetAlpha
        a b D C hfirst hab i hleft hright hiOdd
  have hnextEven : Even nextIdx.val := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [nextIdx]; omega⟩
  have hrightStrict : i.val < C.rightSwitch := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  have hnextValue : a.representationAlphaValue b nextIdx =
      a.alphaValue ⟨nextIdx.val - 1, by
        have := nextIdx.lt_large
        omega⟩ := by
    apply lemma79Central_typeI_evenValue_eq_sourceAlpha
      a b D C hfirst hab nextIdx hnextEven
    · simp only [nextIdx]
      omega
    · simp only [nextIdx]
      omega
  have hnextClose : b.alphaValue ⟨nextIdx.val - 1, by
        have := nextIdx.lt_large
        omega⟩ ≤
      a.alphaValue ⟨nextIdx.val - 1, by
        have := nextIdx.lt_large
        omega⟩ + 2 := by
    have hshift := lemma79Central_typeI_oddTargetAlpha_eq_source_add_two
      a b D C hfirst hab i.val hiOdd hleft.le hrightStrict
    simpa only [nextIdx, show i.val + 1 - 1 = i.val by omega] using hshift.le
  have hpreviousTransfer : b.centralPreviousDefect c i ≤
      a.centralPreviousDefect c i := by
    unfold centralPreviousDefect
    have hformula := beli2019Remark616_rightMixedPrefix_at
      a b c hab.defectCondition currentIdx hcurrentValue
        (-1) (i.val - 2)
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      (hformula.trans_le (min_le_left _ _))
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i + ((2 : ℚ) : WithTop ℚ) := by
    unfold centralCurrentDefect
    simpa only [nextIdx] using
      (beli2019Remark616_leftMixedPrefix_right_le_add_two
        a b c hab.defectCondition nextIdx hnextValue hnextClose
          (-1) (i.val - 1))
  have hcurrentEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val hiOdd hleft.le hright
  have hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentEntries
  have hdefectTriggerBC : b.centralDefectTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horderBC hdefectBC) i).mp htriggerBC
  apply ((a.beli2019Lemma216 c le_rfl hac.orderCondition
    hac.defectCondition) i).mpr
  unfold centralDefectTrigger at hdefectTriggerBC ⊢
  rcases hdefectTriggerBC with ⟨hcrossBC, hsumBC⟩
  constructor
  · exact hcrossBC.trans (by omega)
  · have hsumTransfer :
        b.centralPreviousDefect c i + b.centralCurrentDefect c i ≤
          (a.centralPreviousDefect c i + a.centralCurrentDefect c i) +
            ((2 : ℚ) : WithTop ℚ) := by
      calc
        b.centralPreviousDefect c i + b.centralCurrentDefect c i ≤
            a.centralPreviousDefect c i +
              (a.centralCurrentDefect c i + ((2 : ℚ) : WithTop ℚ)) :=
          add_le_add hpreviousTransfer hcurrentTransfer
        _ = (a.centralPreviousDefect c i + a.centralCurrentDefect c i) +
            ((2 : ℚ) : WithTop ℚ) := by ac_rfl
    have hshift :
        (((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) +
              ((2 : ℚ) : WithTop ℚ)) =
          ((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (b.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) := by
      norm_cast
      have hcurrentOrderQ : (a.order ⟨i.val, i.lt_large⟩ : ℚ) =
          (b.order ⟨i.val, i.lt_large⟩ : ℚ) + 2 := by
        exact_mod_cast hcurrentOrder
      linarith
    have hshifted :
        (((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) +
              ((2 : ℚ) : WithTop ℚ)) <
          (a.centralPreviousDefect c i + a.centralCurrentDefect c i) +
            ((2 : ℚ) : WithTop ℚ) := by
      calc
        _ = ((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (b.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) := hshift
        _ < b.centralPreviousDefect c i + b.centralCurrentDefect c i := hsumBC
        _ ≤ _ := hsumTransfer
    exact (WithTop.add_lt_add_iff_right WithTop.coe_ne_top).mp hshifted

set_option maxHeartbeats 3000000 in
-- The certificate combines the profile calculations with two applications
-- of condition (iii) and the defect-sum Hilbert criterion.
/-- Case 2 of the proof of Lemma 7.9(iii): an odd type-I middle boundary
produces the first Lemma 1.5 certificate. -/
theorem lemma79CentralCertificate_typeIMiddle_odd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiOdd : Odd i.val) (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  have hiNext : i.val + 1 < n + 2 := by
    have hlast := C.right_le_last
    have hbound := D.profile.lastDifference.bound
    rcases C.right_even with ⟨d, hd⟩
    rcases hiOdd with ⟨e, he⟩
    omega
  have hrightSumNot :=
    lemma79Central_typeIMiddle_not_rightAlphaSum_of_odd
      a b D C hfirst i hleft hright hiNext hiOdd
  rcases b.beli2019Lemma218_target c hdefectBC i htriggerBC with
    hprevious | hcurrent
  · have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by omega⟩ +
          b.alphaValue ⟨i.val - 1, by omega⟩ := by
      have halternative := b.centralTrigger_targetAdjacentAlphaAlternative
        c hdefectBC i hiNext htriggerBC
      exact halternative.resolve_right hrightSumNot
    have htriggerAB := lemma79Central_typeIMiddle_odd_triggerAB
      a b D C hfirst hab i hleft hright hiOdd hsum
    have htriggerAC := lemma79Central_typeIMiddle_odd_triggerAC
      a b c D C hfirst hab hac horderBC hdefectBC i hleft hright
        hiOdd htriggerBC
    have hmiddle := hab.centralRepresentations i htriggerAB
    have hsource := hac.centralRepresentations i htriggerAC
    let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
      i.current i.lt_large.le
    have hcurrentValue : a.representationAlphaValue b currentIdx =
        b.alphaValue ⟨currentIdx.val - 1, by
          have := currentIdx.lt_large
          omega⟩ := by
      simpa only [currentIdx, CentralRepresentationIndex.current] using
        lemma79Central_typeI_currentValue_eq_targetAlpha
          a b D C hfirst hab i hleft hright hiOdd
    have hbeta : b.prefixAlphaCap i.val ≤
        a.truncatedPrefixDefect b 1 i.val i.val := by
      rw [b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large]
      have hraw := hab.defectCondition currentIdx
      rw [hcurrentValue] at hraw
      simpa only [currentIdx, CentralRepresentationIndex.current] using hraw
    have hcomparison : b.representationAlpha c i.previous ≤
        b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
      have hraw := hdefectBC i.previous
      rw [b.coe_representationAlphaValue c i.previous] at hraw
      simpa only [CentralRepresentationIndex.previous] using hraw
    apply Lemma79CentralCertificate.first_of_truncatedDefects
      hmiddle hsource
    exact hprevious.trans_le (add_le_add hbeta hcomparison)
  · exfalso
    apply hrightSumNot
    have hcap :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) := by
      apply hcurrent.trans_le
      apply add_le_add le_rfl
      unfold centralCurrentDefect
      exact b.truncatedPrefixDefect_le_leftCap c (-1)
        (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) i.lt_large,
      b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) hiNext] at hcap
    have hcapQ : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by omega⟩ +
          b.alphaValue ⟨i.val + 1 - 1, by omega⟩ := by
      exact_mod_cast hcap
    simpa only [show i.val + 1 - 1 = i.val by omega] using hcapQ

end BONG.GoodBONG

end Bong
