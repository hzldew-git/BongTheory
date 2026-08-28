/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark614TypeI
import Bong.Bong.Beli2019Lemma77

/-!
# Beli (2019), Lemma 7.7: the type-I right branch

Remark 6.14 puts each odd source order on the nonterminal right tail at least
three above the first source order.  The preceding even source order is at
most one above the first order.  Thus the numerical lower bound in Lemma 7.7
is nonpositive, so defect nonnegativity proves the right branch directly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The nonpositive coefficient and the resulting Lemma 7.7 bound on the
nonterminal type-I right tail. -/
theorem lemma77_typeI_right_data
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hkEven : Even k) (hright : C.rightSwitch ≤ k)
    (hlast : k < D.profile.last) :
    (a.order ⟨k, by
          have hlastBound := D.profile.lastDifference.bound
          omega⟩ -
        a.order ⟨k + 1, by
          have hlastBound := D.profile.lastDifference.bound
          omega⟩ + 2 ≤ 0) ∧
      (((((a.order ⟨k, by
              have hlastBound := D.profile.lastDifference.bound
              omega⟩ -
            a.order ⟨k + 1, by
              have hlastBound := D.profile.lastDifference.bound
              omega⟩ : Int) : ℚ) + 2 : ℚ)) : WithTop ℚ) ≤
        a.alternatingPrefixDefect (k + 2) := by
  have hlastBound := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hkDistance : Even (k - D.anchor) := by
    rcases hkEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hlastDistance : Even (D.profile.last - D.anchor) :=
    (D.profile.rightProfile
      (C.anchor_le_right.trans_lt hrightLast)).1
  have hlastEven : Even D.profile.last := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨e + d, by
      have hanchorLast := C.anchor_le_right.trans_lt hrightLast
      omega⟩
  have hkTwoLast : k + 2 ≤ D.profile.last := by
    rcases hkEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceCurrentUpper : a.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero 0 + 1 := by
    by_cases hcurrent : k ≤ C.rightSwitch
    · have hsourceCurrent := C.source_to_right k
        (C.anchor_le_right.trans hright) hcurrent hkDistance
      omega
    · have hsourceCurrent := C.source_after_right k
        (lt_of_not_ge hcurrent) hlast.le hkDistance
      omega
  have hsourceNextLower :=
    beli2019Remark614_typeI_source_odd_ge_first_add_three
      a b D C hfirst hrightLast hdefect k hkEven hright hlast
  have hnonpositive :
      a.order ⟨k, by omega⟩ - a.order ⟨k + 1, by omega⟩ + 2 ≤ 0 := by
    rw [← a.orderSequence_entryOrZero_eq_order ⟨k, by omega⟩,
      ← a.orderSequence_entryOrZero_eq_order ⟨k + 1, by omega⟩]
    change a.orderSequence.entryOrZero k -
      a.orderSequence.entryOrZero (k + 1) + 2 ≤ 0
    omega
  refine ⟨hnonpositive, ?_⟩
  exact a.beli2019Lemma77_of_nonpositive (k + 2) (by omega)
    (by omega) (by
      simpa only [show k + 2 - 2 = k by omega,
        show k + 2 - 1 = k + 1 by omega] using hnonpositive)

/-- Lemma 7.7 at every even zero-based type-I coordinate from the canonical
right switch up to, but not including, the last unequal order. -/
theorem beli2019Lemma77_typeI_right
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hkEven : Even k) (hright : C.rightSwitch ≤ k)
    (hlast : k < D.profile.last) :
    (((((a.order ⟨k, by
              have hlastBound := D.profile.lastDifference.bound
              omega⟩ -
            a.order ⟨k + 1, by
              have hlastBound := D.profile.lastDifference.bound
              omega⟩ : Int) : ℚ) + 2 : ℚ)) : WithTop ℚ) ≤
      a.alternatingPrefixDefect (k + 2) := by
  exact (lemma77_typeI_right_data a b D C hfirst hrightLast hdefect
    k hkEven hright hlast).2

end BONG.GoodBONG

end Bong
