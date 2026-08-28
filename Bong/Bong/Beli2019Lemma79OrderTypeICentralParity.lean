/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma65
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79ThirdPrefixParity

/-!
# Beli (2019), Lemma 7.9(i): type-I central prefix parity

At an even zero-based coordinate in the difficult type-I parity class, the
target order is two above the first source order.  If the direct comparison
with the third BONG fails, strict growth of the norm ideal pins both the first
and current third orders one unit above the first source order.  Lemmas 6.6
and 7.2(i) then show that the source and third prefixes differ by one modulo
two.  Their capped comparison defect is therefore zero, so condition 2.1(ii)
for the original pair gives a nonpositive representation invariant.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Every even target entry from the canonical left switch through the last
difference is two above the first source entry. -/
theorem lemma79_typeI_target_even_eq_first_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (k : Nat) (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hlast : k ≤ D.profile.last) :
    b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero 0 + 2 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  by_cases hkAnchor : k ≤ D.anchor
  · have htarget := C.target_from_left k hleft hkAnchor hkEven
    omega
  · have hanchorK : D.anchor ≤ k := (Nat.lt_of_not_ge hkAnchor).le
    have hdistance : Even (k - D.anchor) := by
      rcases hkEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have htarget := C.target_from_anchor k hanchorK hlast hdistance
    have hanchorGap := D.anchor_gap
    omega

/-- Failure of the direct comparison fixes the first and current third
orders at the unique value between the first source order and the current
type-I target order. -/
theorem lemma79_typeI_even_failure_orders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk) :
    b.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero 0 + 2 ∧
      c.orderSequence.entryOrZero 0 =
        a.orderSequence.entryOrZero 0 + 1 ∧
      c.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero 0 + 1 := by
  have htarget := lemma79_typeI_target_even_eq_first_add_two
    a b D C hfirst k hkEven hleft hlast
  have hcurrentUpper : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero 0 + 1 := by
    rw [b.orderSequence.entryOrZero_of_lt hk] at htarget
    rw [c.orderSequence.entryOrZero_of_lt hk]
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hmonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 k (Nat.zero_le k) hk hkEven
  exact ⟨htarget, by omega, by omega⟩

/-- In the difficult even type-I class, failure of the direct comparison
makes the source prefix congruent to one more than the third prefix. -/
theorem lemma79_typeI_even_prefix_modEq_add_one_of_not_le
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk) :
    Int.ModEq 2 (a.orderSequence.prefixSum (k + 1))
      (c.orderSequence.prefixSum (k + 1) + 1) := by
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot with
    ⟨_, hcFirst, hcCurrent⟩
  let R := a.orderSequence.entryOrZero D.anchor
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hcParity :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      (R + 1) k hk (by omega) (by omega)
  have hcPlus := hcParity.add
    (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  by_cases hright : k ≤ C.rightSwitch
  · have haParity := a.lemma72_typeI_source_before_of_canonical
      b D C hfirst (k + 1) (by omega)
    have hbridge : Int.ModEq 2
        (((k + 1 : Nat) : Int) * R)
        ((((k + 1 : Nat) : Int) * (R + 1)) + 1) := by
      rw [Int.modEq_iff_dvd]
      rcases hkEven with ⟨d, rfl⟩
      refine ⟨(d : Int) + 1, ?_⟩
      push_cast
      ring
    exact haParity.trans hbridge |>.trans (by
      simpa only [R, hsourceZero] using hcPlus.symm)
  · have hright' : C.rightSwitch + 1 ≤ k + 1 := by omega
    have haParity := a.lemma72_typeI_source_after_of_canonical
      b D C hfirst (k + 1) hright' (by omega)
    let X : Int := (((k + 1 : Nat) : Int) * (R + 1))
    have hbridge : Int.ModEq 2 (X - 1) (X + 1) := by
      rw [Int.modEq_iff_dvd]
      exact ⟨1, by ring⟩
    have haPlus : Int.ModEq 2
        (a.orderSequence.prefixSum (k + 1)) (X + 1) := by
      have haBase : Int.ModEq 2
          (a.orderSequence.prefixSum (k + 1)) (X - 1) := by
        simpa only [R, X] using haParity
      exact haBase.trans hbridge
    exact haPlus.trans (by
      simpa only [R, X, hsourceZero] using hcPlus.symm)

/-- The old defect condition therefore bounds the representation invariant
by zero at every nonterminal difficult even type-I coordinate. -/
theorem lemma79_typeI_even_alphaValue_le_zero_of_not_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hlast : k ≤ D.profile.last)
    (hnot : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk) :
    (a.representationAlphaValue c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } : WithTop ℚ) ≤ 0 := by
  let i : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  have hparity := lemma79_typeI_even_prefix_modEq_add_one_of_not_le
    a b c D C hfirst hnorm k hk hkEven hleft hlast hnot
  have hodd := a.comparisonPrefixProduct_order_odd_of_modEq_add_one
    c i (by simpa only [i] using hparity)
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order
    c i.val hodd
  have hbound := hdefect i
  rw [hzero] at hbound
  simpa only [i] using hbound

end BONG.GoodBONG

end Bong
