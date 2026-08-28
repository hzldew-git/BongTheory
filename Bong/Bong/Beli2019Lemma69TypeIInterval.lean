/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IntervalRigidity
import Bong.Bong.Beli2019Lemma69TypeIWeight

/-!
# Beli (2019), Lemma 6.9(v): interval-rigidity layer

The type-I block of the two `W`-sequences has even length.  Once the two
boundary coordinates satisfy the direct comparison and the block sums are
equal, the localized Lemma 5.5(iii) proves equality of every coordinate.
Its even coordinates give `R_i + alpha_i = S_i + beta_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- Lemma 6.9(v) after isolating its two boundary comparisons and the
telescoping equality of the type-I `W`-block. -/
theorem beli2019Lemma69_v_typeI_of_interval
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hleftBoundary :
      a.weightSequence.entryOrZero (2 * C.leftSwitch) ≤
        b.weightSequence.entryOrZero (2 * C.leftSwitch))
    (hrightBoundary :
      a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
        b.weightSequence.entryOrZero (2 * C.rightSwitch - 1))
    (hsum :
      a.weightSequence.segmentSum (2 * C.leftSwitch)
          (2 * C.rightSwitch) =
        b.weightSequence.segmentSum (2 * C.leftSwitch)
          (2 * C.rightSwitch))
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    a.alphaLeftEndpoint ⟨k, by
        have hr := C.right_le_last
        have hl := D.profile.lastDifference.bound
        omega⟩ =
      b.alphaLeftEndpoint ⟨k, by
        have hr := C.right_le_last
        have hl := D.profile.lastDifference.bound
        omega⟩ := by
  let start := 2 * C.leftSwitch
  let length := 2 * (C.rightSwitch - C.leftSwitch)
  have hswitch : C.leftSwitch < C.rightSwitch :=
    hleft.trans_lt hright
  have hbound : start + length ≤ 2 * (n + 1) := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    simp only [start, length]
    omega
  have hpos : 0 < length := by
    simp only [length]
    omega
  have hend : start + length = 2 * C.rightSwitch := by
    simp only [start, length]
    omega
  have hfirst : a.weightSequence.entryOrZero start ≤
      b.weightSequence.entryOrZero start := by
    simpa only [start] using hleftBoundary
  have hlast : a.weightSequence.entryOrZero (start + length - 1) ≤
      b.weightSequence.entryOrZero (start + length - 1) := by
    simpa only [hend] using hrightBoundary
  have hsum' : a.weightSequence.segmentSum start (start + length) =
      b.weightSequence.segmentSum start (start + length) := by
    simpa only [start, hend] using hsum
  let offset := 2 * (k - C.leftSwitch)
  have hoffset : offset < length := by
    simp only [offset, length]
    omega
  have hcoordinate := hW.entryOrZero_eq_of_segmentSum_eq
    start length hbound hpos hfirst hlast hsum' offset hoffset
  have hindex : start + offset = 2 * k := by
    simp only [start, offset]
    omega
  rw [hindex] at hcoordinate
  have hkBound : k < n + 1 := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    omega
  have hcoordBound : 2 * k < 2 * (n + 1) := by omega
  rw [BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound,
    BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound]
    at hcoordinate
  let kFin : Fin (n + 1) := ⟨k, hkBound⟩
  have hcoordinate' :
      a.weightSequence.value ⟨2 * kFin.1, by omega⟩ =
        b.weightSequence.value ⟨2 * kFin.1, by omega⟩ := by
    simpa only [BeliOrderSequence.entry, kFin] using hcoordinate
  rw [a.weightSequence_even kFin, b.weightSequence_even kFin]
    at hcoordinate'
  simpa only [alphaLeftEndpoint, kFin] using hcoordinate'

/-- The middle branch of Lemma 7.7, now reduced to the three explicit
sequence hypotheses used in the proof of Lemma 6.9(v). -/
theorem beli2019Lemma77_typeI_of_weightInterval
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hleftBoundary :
      a.weightSequence.entryOrZero (2 * C.leftSwitch) ≤
        b.weightSequence.entryOrZero (2 * C.leftSwitch))
    (hrightBoundary :
      a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
        b.weightSequence.entryOrZero (2 * C.rightSwitch - 1))
    (hsum :
      a.weightSequence.segmentSum (2 * C.leftSwitch)
          (2 * C.rightSwitch) =
        b.weightSequence.segmentSum (2 * C.leftSwitch)
          (2 * C.rightSwitch))
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hiEven : Even i) (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 < C.rightSwitch) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  have hweight := beli2019Lemma69_v_typeI_of_interval
    a b D C hW hleftBoundary hrightBoundary hsum (i - 2)
      hleft hright
  exact a.beli2019Lemma77_typeI_of_leftEndpoint_eq b D C hfirst i
    hiTwo hiBound hiEven hleft hright.le hweight

end BONG.GoodBONG

end Bong
