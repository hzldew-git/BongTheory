/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019BoundaryRounding

/-!
# Beli (2019), Lemma 6.9(v): type-I boundary reduction

The canonical interval has equal same-parity endpoint orders.  Lemma 6.6
therefore makes every internal adjacent gap even, and Corollary 2.8 makes the
relevant alpha values integral.  Combined with the half-unit rounding lemma,
the two direct boundary comparisons reduce to estimates on the neighboring
coordinates.
-/

namespace Bong

open Dyadic

universe u v

private theorem even_sub_of_int_modEq_two {a b : Int}
    (h : Int.ModEq 2 a b) : Even (a - b) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨z, hz⟩
  exact ⟨-z, by omega⟩

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

/-- Every adjacent order gap strictly inside the canonical type-I interval
is even, for both source and target. -/
theorem lemma69_v_typeI_interval_orderGap_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    Even (a.orderGap ⟨k, by
        have hrightLast := C.right_le_last
        have hlastBound := D.profile.lastDifference.bound
        omega⟩) ∧
      Even (b.orderGap ⟨k, by
        have hrightLast := C.right_le_last
        have hlastBound := D.profile.lastDifference.bound
        omega⟩) := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hintervalParity : Even (C.rightSwitch - C.leftSwitch) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    exact ⟨d - e, by
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega⟩
  have hrightBound : C.rightSwitch < n + 2 := by
    exact C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hleftBound : C.leftSwitch < n + 2 :=
    (C.left_le_anchor.trans C.anchor_le_right).trans_lt hrightBound
  let leftFin : Fin (n + 2) := ⟨C.leftSwitch, hleftBound⟩
  let rightFin : Fin (n + 2) := ⟨C.rightSwitch, hrightBound⟩
  have haLeft := C.source_to_anchor C.leftSwitch C.left_le_anchor C.left_even
  have haRight := C.source_to_right C.rightSwitch C.anchor_le_right
    le_rfl hrightDistance
  have haEndpoints : a.order leftFin = a.order rightFin := by
    rw [← a.orderSequence_entryOrZero_eq_order leftFin,
      ← a.orderSequence_entryOrZero_eq_order rightFin]
    simpa only [leftFin, rightFin] using haLeft.trans haRight.symm
  have hbLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hbRight := C.target_from_anchor C.rightSwitch C.anchor_le_right
    C.right_le_last hrightDistance
  have hbEndpoints : b.order leftFin = b.order rightFin := by
    rw [← b.orderSequence_entryOrZero_eq_order leftFin,
      ← b.orderSequence_entryOrZero_eq_order rightFin]
    simp only [leftFin, rightFin]
    have hgapAnchor := D.anchor_gap
    omega
  have haProfile := a.beli2019Lemma66_i leftFin rightFin (by
      change C.leftSwitch ≤ C.rightSwitch
      exact C.left_le_anchor.trans C.anchor_le_right)
    (by simpa only [leftFin, rightFin] using hintervalParity) haEndpoints
  have hbProfile := b.beli2019Lemma66_i leftFin rightFin (by
      change C.leftSwitch ≤ C.rightSwitch
      exact C.left_le_anchor.trans C.anchor_le_right)
    (by simpa only [leftFin, rightFin] using hintervalParity) hbEndpoints
  let current : Fin (n + 2) := ⟨k, by omega⟩
  let next : Fin (n + 2) := ⟨k + 1, by omega⟩
  have hleftCurrent : leftFin ≤ current := by
    change C.leftSwitch ≤ k
    exact hleft
  have hcurrentRight : current ≤ rightFin := by
    change k ≤ C.rightSwitch
    exact Nat.le_of_lt hright
  have hleftNext : leftFin ≤ next := by
    change C.leftSwitch ≤ k + 1
    omega
  have hnextRight : next ≤ rightFin := by
    change k + 1 ≤ C.rightSwitch
    omega
  have haMod := (haProfile.order_modEq next hleftNext hnextRight).trans
    (haProfile.order_modEq current hleftCurrent hcurrentRight).symm
  have hbMod := (hbProfile.order_modEq next hleftNext hnextRight).trans
    (hbProfile.order_modEq current hleftCurrent hcurrentRight).symm
  constructor
  · unfold orderGap
    change Even (a.order next - a.order current)
    exact even_sub_of_int_modEq_two haMod
  · unfold orderGap
    change Even (b.order next - b.order current)
    exact even_sub_of_int_modEq_two hbMod

/-- Even `W`-coordinates in the nonempty canonical type-I interval are
rational integers. -/
theorem lemma69_v_typeI_even_weight_integral
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    IsRationalInteger (a.weightSequence.entryOrZero (2 * k)) ∧
      IsRationalInteger (b.weightSequence.entryOrZero (2 * k)) := by
  have hgap := lemma69_v_typeI_interval_orderGap_even
    a b D C hfirst k hleft hright
  have hkBound : k < n + 1 := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    omega
  let kFin : Fin (n + 1) := ⟨k, hkBound⟩
  have haAlpha : IsRationalInteger (a.alphaValue kFin) := by
    apply a.beli2009Corollary28_i kFin
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr (by simpa only [kFin] using hgap.1)) hodd
  have hbAlpha : IsRationalInteger (b.alphaValue kFin) := by
    apply b.beli2009Corollary28_i kFin
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr (by simpa only [kFin] using hgap.2)) hodd
  have hcoordBound : 2 * k < 2 * (n + 1) := by omega
  constructor
  · rw [BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound]
    change IsRationalInteger (a.weightSequence.value ⟨2 * k, hcoordBound⟩)
    have hvalue := a.weightSequence_even kFin
    rw [show (⟨2 * k, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * kFin.1, by omega⟩ by apply Fin.ext; rfl, hvalue]
    exact haAlpha.intCast_add (a.order kFin.castSucc)
  · rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound]
    change IsRationalInteger (b.weightSequence.value ⟨2 * k, hcoordBound⟩)
    have hvalue := b.weightSequence_even kFin
    rw [show (⟨2 * k, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * kFin.1, by omega⟩ by apply Fin.ext; rfl, hvalue]
    exact hbAlpha.intCast_add (b.order kFin.castSucc)

/-- Odd `W`-coordinates in the nonempty canonical type-I interval are
rational integers. -/
theorem lemma69_v_typeI_odd_weight_integral
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    IsRationalInteger (a.weightSequence.entryOrZero (2 * k + 1)) ∧
      IsRationalInteger (b.weightSequence.entryOrZero (2 * k + 1)) := by
  have hgap := lemma69_v_typeI_interval_orderGap_even
    a b D C hfirst k hleft hright
  have hkBound : k < n + 1 := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    omega
  let kFin : Fin (n + 1) := ⟨k, hkBound⟩
  have haAlpha : IsRationalInteger (a.alphaValue kFin) := by
    apply a.beli2009Corollary28_i kFin
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr (by simpa only [kFin] using hgap.1)) hodd
  have hbAlpha : IsRationalInteger (b.alphaValue kFin) := by
    apply b.beli2009Corollary28_i kFin
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr (by simpa only [kFin] using hgap.2)) hodd
  have hcoordBound : 2 * k + 1 < 2 * (n + 1) := by omega
  constructor
  · rw [BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound]
    change IsRationalInteger (a.weightSequence.value ⟨2 * k + 1, hcoordBound⟩)
    have hvalue := a.weightSequence_odd kFin
    rw [show (⟨2 * k + 1, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * kFin.1 + 1, by omega⟩ by apply Fin.ext; rfl, hvalue]
    exact haAlpha.intCast_sub (a.order kFin.succ)
  · rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound]
    change IsRationalInteger (b.weightSequence.value ⟨2 * k + 1, hcoordBound⟩)
    have hvalue := b.weightSequence_odd kFin
    rw [show (⟨2 * k + 1, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * kFin.1 + 1, by omega⟩ by apply Fin.ext; rfl, hvalue]
    exact hbAlpha.intCast_sub (b.order kFin.succ)

/-- The left boundary comparison, reduced to the preceding-coordinate
one-half estimate in the noninitial case. -/
theorem lemma69_v_typeI_leftBoundary_of_previous
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hstrict : C.leftSwitch < C.rightSwitch)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hprevious : 0 < C.leftSwitch →
      b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
        a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2) :
    a.weightSequence.entryOrZero (2 * C.leftSwitch) ≤
      b.weightSequence.entryOrZero (2 * C.leftSwitch) := by
  by_cases hzero : C.leftSwitch = 0
  · simpa only [hzero, Nat.mul_zero] using
      hW.entryOrZero_zero_le (by omega)
  · have hleftPos : 0 < C.leftSwitch := Nat.pos_of_ne_zero hzero
    have hintegral := lemma69_v_typeI_even_weight_integral
      a b D C hfirst C.leftSwitch le_rfl hstrict
    apply hW.entryOrZero_le_of_previous_le_add_half
      (2 * C.leftSwitch) (by omega) (by
        have hrightLast := C.right_le_last
        have hlastBound := D.profile.lastDifference.bound
        omega) (by
          simpa only [show 2 * C.leftSwitch - 1 =
            2 * C.leftSwitch - 1 by rfl] using hprevious hleftPos)
      hintegral.1 hintegral.2

/-- The right boundary comparison, reduced to the following-coordinate
one-half estimate when the boundary is not the final coordinate. -/
theorem lemma69_v_typeI_rightBoundary_of_next
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hstrict : C.leftSwitch < C.rightSwitch)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hnext : C.rightSwitch < n + 1 →
      b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
        a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2) :
    a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
      b.weightSequence.entryOrZero (2 * C.rightSwitch - 1) := by
  have hrightBound : C.rightSwitch ≤ n + 1 := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    omega
  by_cases hfinal : C.rightSwitch = n + 1
  · have hlengthPos : 0 < 2 * (n + 1) := by omega
    have hlast := hW.entryOrZero_last_le hlengthPos
    simpa only [hfinal, show 2 * (n + 1) - 1 =
      2 * (n + 1) - 1 by rfl] using hlast
  · have hrightStrict : C.rightSwitch < n + 1 :=
      lt_of_le_of_ne hrightBound hfinal
    have hleftPrevious : C.leftSwitch ≤ C.rightSwitch - 1 := by omega
    have hintegral := lemma69_v_typeI_odd_weight_integral
      a b D C hfirst (C.rightSwitch - 1) hleftPrevious (by omega)
    apply hW.entryOrZero_le_of_next_le_add_half
      (2 * C.rightSwitch - 1) (by omega) (by
        simpa only [show 2 * C.rightSwitch - 1 + 1 =
          2 * C.rightSwitch by omega] using hnext hrightStrict)
      (by
        simpa only [show 2 * (C.rightSwitch - 1) + 1 =
          2 * C.rightSwitch - 1 by omega] using hintegral.1)
      (by
        simpa only [show 2 * (C.rightSwitch - 1) + 1 =
          2 * C.rightSwitch - 1 by omega] using hintegral.2)

/-- Lemma 7.7's type-I middle branch after reducing both boundary
comparisons to the two local one-half estimates in Lemma 6.9(v). -/
theorem beli2019Lemma77_typeI_of_neighborBounds
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hleftNeighbor : 0 < C.leftSwitch →
      b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
        a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2)
    (hrightNeighbor : C.rightSwitch < n + 1 →
      b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
        a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2)
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hiEven : Even i) (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 < C.rightSwitch) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  have hstrict : C.leftSwitch < C.rightSwitch := hleft.trans_lt hright
  apply a.beli2019Lemma77_typeI_of_weightBoundaries b D C hfirst hW
  · exact lemma69_v_typeI_leftBoundary_of_previous
      a b D C hfirst hstrict hW hleftNeighbor
  · exact lemma69_v_typeI_rightBoundary_of_next
      a b D C hfirst hstrict hW hrightNeighbor
  · exact hiTwo
  · exact hiBound
  · exact hiEven
  · exact hleft
  · exact hright

end BONG.GoodBONG

end Bong
