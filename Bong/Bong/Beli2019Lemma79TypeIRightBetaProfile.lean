/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79TypeIThirdParity
import Bong.Bong.Beli2019Lemma79TypeIRightProfileAlpha

/-!
# Beli (2019), Lemma 7.9(ii): the type-I right-tail beta branch

The canonical right profile supplies the target-alpha recursion. In the
strict comparison-order subcase, Lemmas 6.6(i) and 7.2(i) force the third
prefix in the secondary candidate to have odd valuation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- The strict branch transports four dependent indices and two congruences.
/-- The `beta_i` branch of Lemma 7.9(ii), case 4, on the odd type-I right
tail. -/
theorem lemma79_typeI_beta_bound_from_rightProfile
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiPreviousAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hfarBound : i.val + 1 < n + 2 := by
    have hb := D.profile.lastDifference.bound
    omega
  have hprofile := lemma79_typeI_right_target_twoStep_and_alpha
    a b D C hfirst i hright hlast hodd
  by_cases hcurrent : b.order ⟨i.val - 1, hiPrevious⟩ ≤
      c.order ⟨i.val - 1, hiPrevious⟩
  · have hprimary := b.representationAlphaValue_le_primary_nextAlpha
      c i hfarBound
    have hcurrentQ :
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) ≤
        ((b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) := by
      exact_mod_cast (show b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, hiPrevious⟩ ≤
          b.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, hiPrevious⟩ by omega)
    have hbound : b.representationAlphaValue c i ≤
        b.alphaValue ⟨i.val - 1, hiPreviousAlpha⟩ := by
      linarith [hprimary, hcurrentQ, hprofile.2]
    exact WithTop.coe_le_coe.mpr hbound
  · have hcurrentStrict : c.order ⟨i.val - 1, hiPrevious⟩ <
        b.order ⟨i.val - 1, hiPrevious⟩ := lt_of_not_ge hcurrent
    have hiTwo : 1 < i.val := by
      rcases horder ⟨i.val - 1, hiPrevious⟩ with hdirect | hpair
      · exact False.elim ((not_le_of_gt hcurrentStrict) hdirect)
      · exact Nat.lt_of_sub_pos hpair.1
    rcases hodd with ⟨d, hd⟩
    have hpreviousEven : Even (i.val - 1) := ⟨d, by omega⟩
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hpreviousDistance : Even (i.val - 1 - D.anchor) := by
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have har := C.anchor_le_right
        omega⟩
    have htargetPreviousRaw := C.target_from_anchor (i.val - 1) (by
        have har := C.anchor_le_right
        omega)
      (by omega) hpreviousDistance
    let T := a.orderSequence.entryOrZero D.anchor + 1
    have htargetPrevious : b.orderSequence.entryOrZero (i.val - 1) =
        T + 1 := by
      dsimp only [T]
      have hgap := D.anchor_gap
      omega
    have hcurrentEntries : c.orderSequence.entryOrZero (i.val - 1) <
        b.orderSequence.entryOrZero (i.val - 1) := by
      rw [c.orderSequence.entryOrZero_of_lt (by omega),
        b.orderSequence.entryOrZero_of_lt (by omega)]
      exact hcurrentStrict
    have hcurrentReference : c.orderSequence.entryOrZero (i.val - 1) ≤
        T := by omega
    have hearlierMono := c.orderSequence.entryOrZero_le_of_evenGap
      (i.val - 3) (i.val - 1) (by omega) (by omega)
      (show Even ((i.val - 1) - (i.val - 3)) by
        exact ⟨1, by omega⟩)
    have hearlierReference : c.orderSequence.entryOrZero (i.val - 3) ≤
        T := hearlierMono.trans hcurrentReference
    have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
      c.toBONG hnorm
    have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
        c.orderSequence.entryOrZero 0 := by
      calc
        a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
          rw [a.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
        _ ≤ c.order 0 := hnormOrder
        _ = c.orderSequence.entryOrZero 0 := by
          rw [c.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
    have hsourceZero := C.source_to_anchor 0
      (Nat.zero_le D.anchor) ⟨0, by omega⟩
    have hreferenceFirst : T ≤ c.orderSequence.entryOrZero 0 := by
      dsimp only [T]
      rw [← hsourceZero]
      exact hfirstOrder
    have hcParityRaw :=
      c.prefixSum_modEq_mul_of_current_le_reference_le_first
        T (i.val - 3) (by omega) hreferenceFirst hearlierReference
    have hcParity : Int.ModEq 2
        (c.orderSequence.prefixSum (i.val - 2))
        (((i.val - 2 : Nat) : Int) * T) := by
      simpa only [show i.val - 3 + 1 = i.val - 2 by omega] using
        hcParityRaw
    have hleftRight := C.left_le_anchor.trans C.anchor_le_right
    have hbParityRaw := a.lemma72_typeI_target_after_of_canonical
      b D C hfirst (i.val + 2) (by omega) (by omega)
    have hbParity : Int.ModEq 2
        (b.orderSequence.prefixSum (i.val + 2))
        (((i.val + 2 : Nat) : Int) * (T + 1)) := by
      convert hbParityRaw using 1
      dsimp only [T]
      ring
    have hoddThird := b.lemma79_typeI_thirdPrefix_odd_of_modEq
      c i.val ⟨d, hd⟩ (by omega) (by omega) T hbParity hcParity
    exact b.lemma79_typeI_beta_bound c horder i
      ⟨hiTwo, hfarBound⟩ hprofile.2 hprofile.1 hoddThird

end BONG.GoodBONG

end Bong
