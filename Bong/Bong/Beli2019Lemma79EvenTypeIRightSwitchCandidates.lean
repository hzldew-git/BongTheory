/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightComplete
import Bong.Bong.Beli2019Lemma69TypeIRightTargetValue
import Bong.Bong.Beli2019Lemma79EvenSecondaryArithmetic
import Bong.Bong.Beli2019Lemma79EvenTypeICentralCandidates

/-!
# Beli (2019), Lemma 7.9(ii), case 3: right type-I switch candidates

At `i = t' - 1`, the primary mixed prefix is controlled by the complete
right-target value in Lemma 6.9(ii).  For the secondary candidate, the
next target alpha is one and the target adjacent order sum is one larger.
These are the two exceptional comparisons in the final paragraph of the
even part of case 3.
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
-- The right-tail value theorem is instantiated at the following odd index.
/-- The primary candidate remains within two units at the canonical right
type-I switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_primary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
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
  have hnextOdd : Odd nextIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hnextLast : nextIdx.val < D.profile.last := by
    simp only [nextIdx]
    omega
  have hAlpha := beli2019Lemma69_ii_typeI_targetRightValue
    a b D C hfirst hrightLast hdefect nextIdx (by
      simp only [nextIdx]
      omega) hnextLast hnextOdd
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_two_of_order_eq_add_two
    a b c i horderShift hprefix

set_option maxHeartbeats 3000000 in
-- This is the exceptional `i = t' - 1` secondary-candidate arithmetic.
/-- The secondary candidate remains within two units at the canonical right
type-I switch. -/
theorem beli2019Lemma79_typeI_rightSwitch_even_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
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
  have hnextRaw := lemma69_v_typeI_next_source_target_order
    a b D C hfirst hrightLast
  have hnext : a.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val + 1) + 1 := by
    simpa only [hrightEq] using hnextRaw
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val +
        b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero i.val +
        a.orderSequence.entryOrZero (i.val + 1) + 1
    omega
  have halphaLe := beli2019Lemma69_i_typeI_nextTargetAlpha
    a b D C hfirst hrightLast hdefect
  have halphaEq := lemma69_v_typeI_nextTargetAlpha_eq_one_of_le_one
    a b D C hfirst hrightLast halphaLe
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hfarBound : i.val + 2 < n + 2 := by
    have hlastBound := D.profile.lastDifference.bound
    omega
  have htarget := b.truncatedPrefixDefect_le_leftCap
    c 1 (i.val + 2) (i.val - 2)
  rw [b.prefixAlphaCap_of_internal (by omega) hfarBound] at htarget
  have halphaEq' : b.alphaValue ⟨i.val + 1, by omega⟩ = 1 := by
    simpa only [hrightEq] using halphaEq
  have htargetOne : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤ ((1 : ℚ) : WithTop ℚ) := by
    exact htarget.trans (by exact_mod_cast halphaEq'.le)
  have hsource := a.truncatedPrefixDefect_nonneg
    c 1 (i.val + 2) (i.val - 2)
  exact representationSecondaryDefect_le_add_two_of_orderSum_eq_add_one
    a b c i hi hsum htargetOne hsource

end BONG.GoodBONG

end Bong
