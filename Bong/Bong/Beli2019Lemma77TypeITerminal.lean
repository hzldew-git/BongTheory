/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77TypeIRight

/-!
# Beli (2019), Lemma 7.7: the terminal type-I branch

At the last unequal even coordinate, the preceding odd source order is at
least three above the first source order. Two-step monotonicity transfers
that bound to the common suffix, whereas the current source order is only
one above the first order. Hence the coefficient in Lemma 7.7 is
nonpositive at the terminal coordinate as well.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The nonpositive coefficient and Lemma 7.7 at the last unequal type-I
coordinate, provided the following coordinate still lies in the BONG. -/
theorem lemma77_typeI_terminal_data
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hkNext : D.profile.last + 1 < n + 2) :
    (a.order ⟨D.profile.last, D.profile.lastDifference.bound⟩ -
        a.order ⟨D.profile.last + 1, hkNext⟩ + 2 ≤ 0) ∧
      (((((a.order ⟨D.profile.last, D.profile.lastDifference.bound⟩ -
            a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ)) :
          WithTop ℚ) ≤
        a.alternatingPrefixDefect (D.profile.last + 2) := by
  have hlastBound := D.profile.lastDifference.bound
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
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
  have hlastMinusTwoEven : Even (D.profile.last - 2) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourcePreviousLowerRaw :=
    beli2019Remark614_typeI_source_odd_ge_first_add_three
      a b D C hfirst hrightLast hdefect (D.profile.last - 2)
        hlastMinusTwoEven (by omega) (by omega)
  have hsourcePreviousLower :
      a.orderSequence.entryOrZero 0 + 3 ≤
        a.orderSequence.entryOrZero (D.profile.last - 1) := by
    simpa only [show D.profile.last - 2 + 1 =
        D.profile.last - 1 by omega] using hsourcePreviousLowerRaw
  have hsourceMono := a.orderSequence.twoStep (D.profile.last - 1) (by
    omega)
  have hsourcePreviousNext :
      a.orderSequence.entryOrZero (D.profile.last - 1) ≤
        a.orderSequence.entryOrZero (D.profile.last + 1) := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hkNext]
    simpa only [BeliOrderSequence.entry,
      show D.profile.last - 1 + 2 =
        D.profile.last + 1 by omega] using hsourceMono
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceLast := C.source_after_right D.profile.last hrightLast
    le_rfl hlastDistance
  have hsourceCurrentUpper :
      a.orderSequence.entryOrZero D.profile.last ≤
        a.orderSequence.entryOrZero 0 + 1 := by
    omega
  have hsourceNextLower :
      a.orderSequence.entryOrZero 0 + 3 ≤
        a.orderSequence.entryOrZero (D.profile.last + 1) :=
    hsourcePreviousLower.trans hsourcePreviousNext
  have hnonpositive :
      a.order ⟨D.profile.last, hlastBound⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ + 2 ≤ 0 := by
    rw [← a.orderSequence_entryOrZero_eq_order
        ⟨D.profile.last, hlastBound⟩,
      ← a.orderSequence_entryOrZero_eq_order
        ⟨D.profile.last + 1, hkNext⟩]
    change a.orderSequence.entryOrZero D.profile.last -
      a.orderSequence.entryOrZero (D.profile.last + 1) + 2 ≤ 0
    omega
  refine ⟨hnonpositive, ?_⟩
  exact a.beli2019Lemma77_of_nonpositive (D.profile.last + 2) (by omega)
    (by omega) (by
      simpa only [show D.profile.last + 2 - 2 = D.profile.last by omega,
        show D.profile.last + 2 - 1 = D.profile.last + 1 by omega] using
          hnonpositive)

/-- Lemma 7.7 at the last unequal zero-based type-I coordinate. -/
theorem beli2019Lemma77_typeI_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hkNext : D.profile.last + 1 < n + 2) :
    (((((a.order ⟨D.profile.last, D.profile.lastDifference.bound⟩ -
          a.order ⟨D.profile.last + 1, hkNext⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤
      a.alternatingPrefixDefect (D.profile.last + 2) := by
  exact (lemma77_typeI_terminal_data a b D C hfirst hrightLast hdefect
    hkNext).2

end BONG.GoodBONG

end Bong
