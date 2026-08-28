/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79RightTailLastGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: initial type-I gap-two data

In the remaining type-I branch the final changed target order is two above
the source order.  This forces the canonical right switch `t'` to be the
last changed coordinate.  We also record the exact endpoint orders and the
prefix parity formula used at the start of the paper's gap-two argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Structural and parity data at the start of the type-I gap-two branch. -/
structure CaseEightTypeIGapTwoInitialData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) where
  canonical : Lemma67TypeICanonicalData a b D
  rightSwitch_eq_last : canonical.rightSwitch = D.profile.last
  anchor_even : Even D.anchor
  last_distance_even : Even (D.profile.last - D.anchor)
  last_even : Even D.profile.last
  source_last : a.orderSequence.entryOrZero D.profile.last =
    a.orderSequence.entryOrZero D.anchor
  target_last : b.orderSequence.entryOrZero D.profile.last =
    a.orderSequence.entryOrZero D.anchor + 2
  target_prefix_last : Int.ModEq 2
    (b.orderSequence.prefixSum (D.profile.last + 1))
    (((D.profile.last + 1 : Nat) : Int) *
      (a.orderSequence.entryOrZero D.anchor + 1) + 1)

/-- In the type-I gap-two branch, the canonical right switch is the last
changed coordinate and the endpoint satisfies the paper's initial parity
formula. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2) :
    Nonempty (CaseEightTypeIGapTwoInitialData a b D) := by
  classical
  rcases a.lemma67TypeICanonicalData b D hfirst with ⟨C⟩
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    by_cases heq : D.anchor = D.profile.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      exact (D.profile.rightProfile hlt).1
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    refine ⟨d + e, ?_⟩
    have hanchorLast := D.profile.anchor_le_last
    omega
  have htargetLast : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    calc
      b.orderSequence.entryOrZero D.profile.last =
          b.orderSequence.entryOrZero D.anchor :=
        C.target_from_anchor D.profile.last D.profile.anchor_le_last
          le_rfl hlastDistance
      _ = a.orderSequence.entryOrZero D.anchor + 2 := D.anchor_gap
  have hrightLast : C.rightSwitch = D.profile.last := by
    apply le_antisymm C.right_le_last
    by_contra hnot
    have hrightLt : C.rightSwitch < D.profile.last := by omega
    have hsourceAfter := C.source_after_right D.profile.last
      hrightLt le_rfl hlastDistance
    omega
  have hsourceLast : a.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.anchor := by
    exact C.source_to_right D.profile.last D.profile.anchor_le_last
      (by rw [hrightLast]) hlastDistance
  have hprefixRaw := a.lemma72_typeI_target_after_of_canonical
    b D C hfirst (D.profile.last + 1) (by
      have hleft := C.left_le_anchor.trans D.profile.anchor_le_last
      omega) le_rfl
  have hprefixReference : Int.ModEq 2
      (((D.profile.last + 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 2))
      (((D.profile.last + 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 1) + 1) := by
    rcases hlastEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    have hdInt : (D.profile.last : Int) =
        (d : Int) + (d : Int) := by
      exact_mod_cast hd
    push_cast
    rw [hdInt]
    ring
  exact ⟨{
    canonical := C
    rightSwitch_eq_last := hrightLast
    anchor_even := hanchorEven
    last_distance_even := hlastDistance
    last_even := hlastEven
    source_last := hsourceLast
    target_last := htargetLast
    target_prefix_last := hprefixRaw.trans hprefixReference }⟩

end BONG.GoodBONG

end Bong
