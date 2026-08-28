/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIMiddleComplete
import Bong.Bong.Beli2019Lemma79EvenTypeICentralTerminalComplete
import Bong.Bong.Beli2019Lemma79CaseSixTypeIProfile

/-!
# Beli (2019), Lemma 7.9(iii), case 3: the type-I right boundary

At the first odd coordinate after the canonical right switch, the preceding
comparison invariant is the corresponding source alpha and the current one is
the target alpha.  The preceding target alpha can exceed the source alpha by
at most two; the even order shift at the switch cancels those two units.

On the `(a,c)` side, Remark 6.16 transfers the preceding mixed defect without
loss.  The following target alpha is exactly one, so the current mixed defect
loses only one unit.  That unit is cancelled by the one-unit source-target
order shift after the right switch.  This is case 3 in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the first coordinate after the right switch, the preceding comparison
invariant is the source alpha immediately to the left. -/
theorem lemma79Central_typeIRightBoundary_previousValue_eq_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1) :
    a.representationAlphaValue b i.previous =
      a.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ := by
  have hpreviousEven : Even i.previous.val := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by
      simp only [CentralRepresentationIndex.previous]
      omega⟩
  by_cases hcoincident : C.leftSwitch = C.rightSwitch
  · have hvalue := a.beli2019Lemma69_ii_typeI_sourceLeftValue_complete
      b D C hfirst hab.defectCondition i.previous (by
        simp only [CentralRepresentationIndex.previous]
        rcases C.right_even with ⟨d, hd⟩
        have := i.one_lt
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
      rcases C.right_even with ⟨e, he⟩
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega
    · simp only [CentralRepresentationIndex.previous]
      rw [hi]
      have := i.one_lt
      omega

/-- The target alpha before the right boundary is at most two above the
preceding comparison invariant. -/
theorem lemma79Central_typeIRightBoundary_previousAlpha_le_value_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1) :
    b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ ≤
      a.representationAlphaValue b i.previous + 2 := by
  have hvalue :=
    lemma79Central_typeIRightBoundary_previousValue_eq_sourceAlpha
      a b D C hfirst hab i hi
  have hpreviousEven : Even i.previous.val := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by
      simp only [CentralRepresentationIndex.previous]
      omega⟩
  by_cases hcoincident : C.leftSwitch = C.rightSwitch
  · have hrightTwo : 2 ≤ C.rightSwitch := by
      rcases C.right_even with ⟨d, hd⟩
      have := i.one_lt
      omega
    have hclose := beli2019Lemma79_typeI_leftSwitch_alphaClose
      a b D C hfirst hab.defectCondition (by
        simpa only [hcoincident] using hrightTwo)
    rw [hvalue]
    simpa only [hi, hcoincident,
      show C.rightSwitch + 1 - 2 = C.rightSwitch - 1 by omega]
      using hclose
  · have hshift :=
      beli2019Lemma79_typeI_central_even_alphaShift_complete
        a b D C hfirst hab.orderCondition hab.defectCondition i.previous
          hpreviousEven (by
            simp only [CentralRepresentationIndex.previous]
            rcases C.left_even with ⟨d, hd⟩
            rcases C.right_even with ⟨e, he⟩
            have hleftRight := C.left_le_anchor.trans C.anchor_le_right
            omega) (by
            simp only [CentralRepresentationIndex.previous]
            rw [hi]
            have := i.one_lt
            omega)
    rw [hvalue]
    simpa only [CentralRepresentationIndex.previous,
      show i.val - 1 - 1 = i.val - 2 by omega] using hshift.le

/-- The current comparison invariant at the right boundary is exactly the
current target alpha. -/
theorem lemma79Central_typeIRightBoundary_currentValue_eq_targetAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1) :
    a.representationAlphaValue b (i.current i.lt_large.le) =
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
  exact a.beli2019Lemma69_ii_typeI_rightSuccessorTargetValue_complete
    b D C hfirst hab.defectCondition (i.current i.lt_large.le) (by
      simp only [CentralRepresentationIndex.current]
      exact hi)

/-- At the right boundary the source current order is one above the target
current order. -/
theorem lemma79Central_typeIRightBoundary_currentOrder
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1)
    (hthroughLast : i.val ≤ D.profile.last) :
    a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  have hraw := lemma69_v_typeI_next_source_target_order
    a b D C hfirst hrightLast
  rw [← a.orderSequence_entryOrZero_eq_order,
    ← b.orderSequence_entryOrZero_eq_order]
  simpa only [hi] using hraw

/-- At the even right switch, the target order is two above the source
order. -/
theorem lemma79Central_typeIRightBoundary_previousOrder
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1) :
    b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ + 2 := by
  have hraw := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst (i.val - 1) (by
      simpa only [hi, show C.rightSwitch + 1 - 1 = C.rightSwitch by omega]
        using C.right_even) (by
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega) (by omega)
  rw [← a.orderSequence_entryOrZero_eq_order,
    ← b.orderSequence_entryOrZero_eq_order]
  exact hraw

/-- The first adjacent-alpha alternative activates condition (iii) for
`(a,b)` at the type-I right boundary. -/
theorem lemma79Central_typeIRightBoundary_triggerAB
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hi : i.val = C.rightSwitch + 1)
    (hthroughLast : i.val ≤ D.profile.last)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    a.centralAlphaTrigger b i := by
  have htargetCross := b.order_twoStep_lt_of_alphaSum_gt_twoE i hsum
  have hcurrentOrder := lemma79Central_typeIRightBoundary_currentOrder
    a b D C hfirst i hi hthroughLast
  have hpreviousOrder := lemma79Central_typeIRightBoundary_previousOrder
    a b D C hfirst i hi
  have hpreviousClose :=
    lemma79Central_typeIRightBoundary_previousAlpha_le_value_add_two
      a b D C hfirst hab i hi
  have hcurrentValue :=
    lemma79Central_typeIRightBoundary_currentValue_eq_targetAlpha
      a b D C hfirst hab i hi
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
    have hpreviousOrderQ :
        (b.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) =
        (a.order ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : ℚ) + 2 := by
      exact_mod_cast hpreviousOrder
    linarith

/-- The active `(b,c)` central trigger transfers to `(a,c)` at the type-I
right boundary.  The current mixed defect loses at most one, exactly
cancelled by the one-unit current-order shift. -/
theorem lemma79Central_typeIRightBoundary_triggerAC
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
    (hi : i.val = C.rightSwitch + 1)
    (hthroughLast : i.val ≤ D.profile.last)
    (htriggerBC : b.centralAlphaTrigger c i) :
    a.centralAlphaTrigger c i := by
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := D.profile.lastDifference.bound
    omega
  have hiOdd : Odd i.val := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hcurrentValue : a.representationAlphaValue b currentIdx =
      b.alphaValue ⟨currentIdx.val - 1, by
        have := currentIdx.lt_large
        omega⟩ := by
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      lemma79Central_typeIRightBoundary_currentValue_eq_targetAlpha
        a b D C hfirst hab i hi
  have hpreviousTransfer : b.centralPreviousDefect c i ≤
      a.centralPreviousDefect c i := by
    unfold centralPreviousDefect
    have hformula := beli2019Remark616_rightMixedPrefix_at
      a b c hab.defectCondition currentIdx hcurrentValue
        (-1) (i.val - 2)
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      (hformula.trans_le (min_le_left _ _))
  have hbetaOne : b.alphaValue ⟨i.val, by omega⟩ = 1 := by
    exact beli2019Remark613_typeI_targetRightAlpha_eq_one
      a b D C hfirst hrightLast hab.defectCondition i.val
        (by omega) (by omega) hiOdd
  have hcurrentOne : b.centralCurrentDefect c i ≤
      ((1 : ℚ) : WithTop ℚ) := by
    unfold centralCurrentDefect
    have hcap := b.truncatedPrefixDefect_le_leftCap
      c (-1) (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by omega) hiNext] at hcap
    exact hcap.trans (by exact_mod_cast hbetaOne.le)
  have hsourceNonneg : (0 : WithTop ℚ) ≤
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    exact a.truncatedPrefixDefect_nonneg
      c (-1) (i.val + 1) (i.val - 1)
  have hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i + ((1 : ℚ) : WithTop ℚ) := by
    calc
      b.centralCurrentDefect c i ≤ ((1 : ℚ) : WithTop ℚ) :=
        hcurrentOne
      _ ≤ a.centralCurrentDefect c i + ((1 : ℚ) : WithTop ℚ) := by
        simpa [add_comm] using
          add_le_add_right hsourceNonneg ((1 : ℚ) : WithTop ℚ)
  have hcurrentOrder := lemma79Central_typeIRightBoundary_currentOrder
    a b D C hfirst i hi hthroughLast
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
            ((1 : ℚ) : WithTop ℚ) := by
      calc
        b.centralPreviousDefect c i + b.centralCurrentDefect c i ≤
            a.centralPreviousDefect c i +
              (a.centralCurrentDefect c i + ((1 : ℚ) : WithTop ℚ)) :=
          add_le_add hpreviousTransfer hcurrentTransfer
        _ = (a.centralPreviousDefect c i + a.centralCurrentDefect c i) +
            ((1 : ℚ) : WithTop ℚ) := by ac_rfl
    have hshift :
        (((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) +
              ((1 : ℚ) : WithTop ℚ)) =
          ((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (b.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) := by
      norm_cast
      have hcurrentOrderQ : (a.order ⟨i.val, i.lt_large⟩ : ℚ) =
          (b.order ⟨i.val, i.lt_large⟩ : ℚ) + 1 := by
        exact_mod_cast hcurrentOrder
      linarith
    have hshifted :
        (((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) +
              ((1 : ℚ) : WithTop ℚ)) <
          (a.centralPreviousDefect c i + a.centralCurrentDefect c i) +
            ((1 : ℚ) : WithTop ℚ) := by
      calc
        _ = ((2 * (ramificationIndex K : ℚ) +
            (c.order ⟨i.val - 2, by omega⟩ : ℚ) -
            (b.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) := hshift
        _ < b.centralPreviousDefect c i + b.centralCurrentDefect c i := hsumBC
        _ ≤ _ := hsumTransfer
    exact (WithTop.add_lt_add_iff_right WithTop.coe_ne_top).mp hshifted

set_option maxHeartbeats 3000000 in
/-- Case 3 of Lemma 7.9(iii): the first Lemma 2.18 alternative at the
type-I right boundary yields the first Lemma 1.5 certificate. -/
theorem lemma79CentralCertificate_typeIRightBoundary
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
    (hi : i.val = C.rightSwitch + 1)
    (hthroughLast : i.val ≤ D.profile.last)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    Lemma79CentralCertificate a b c i := by
  have hpreviousAlpha :=
    b.representationAlpha_le_leftAlpha c hdefectBC i.previous
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ : WithTop ℚ) +
          (b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ : WithTop ℚ) := by
    calc
      _ < b.prefixAlphaCap i.val + b.representationAlpha c i.previous :=
        hprevious
      _ ≤ (b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : WithTop ℚ) +
          (b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ : WithTop ℚ) := by
        apply add_le_add
        · rw [b.prefixAlphaCap_of_internal (by omega) i.lt_large]
        · simpa only [CentralRepresentationIndex.previous,
            show i.val - 1 - 1 = i.val - 2 by omega]
            using hpreviousAlpha
      _ = _ := by ac_rfl
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ +
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
    exact_mod_cast hsumTop
  have htriggerAB := lemma79Central_typeIRightBoundary_triggerAB
    a b D C hfirst hab i hi hthroughLast hsum
  have htriggerAC := lemma79Central_typeIRightBoundary_triggerAC
    a b c D C hfirst hab hac horderBC hdefectBC i hi hthroughLast
      htriggerBC
  have hmiddle := hab.centralRepresentations i htriggerAB
  have hsource := hac.centralRepresentations i htriggerAC
  let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
    i.current i.lt_large.le
  have hcurrentValue : a.representationAlphaValue b currentIdx =
      b.alphaValue ⟨currentIdx.val - 1, by
        have := currentIdx.lt_large
        omega⟩ := by
    simpa only [currentIdx, CentralRepresentationIndex.current] using
      lemma79Central_typeIRightBoundary_currentValue_eq_targetAlpha
        a b D C hfirst hab i hi
  have hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [b.prefixAlphaCap_of_internal (by omega) i.lt_large]
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

end BONG.GoodBONG

end Bong
