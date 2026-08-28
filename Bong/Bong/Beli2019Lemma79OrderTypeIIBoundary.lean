/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIRight

/-!
# Beli (2019), Lemma 7.9(i): the type-II right predecessor

The coordinate immediately before the type-II right transition is direct
when its zero-based index is even.  In the odd case, failure of the direct
comparison supplies the prefix parity for Lemma 6.5.  Both alternatives of
that lemma imply condition 2.1(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- The coordinate `firstTwo - 2`, corresponding to `i = t' - 1` in part
5 of the paper's proof of Lemma 7.9(i). -/
theorem beli2019Lemma79_i_typeII_rightPredecessor
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (htransition : k + 2 = D.outer.transition.firstTwo) :
    b.orderSequence.entry k (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega) ≤
      c.orderSequence.entry k (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega) ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k (by
              have hbound := D.outer.transition.firstTwo_le_rank
              omega) +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k (by
              have hbound := D.outer.transition.firstTwo_le_rank
              omega) := by
  have hbound := D.outer.transition.firstTwo_le_rank
  have hk : k < n + 2 := by omega
  have hkNext : k + 1 < n + 2 := by omega
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hleft : D.outer.transition.lastZero < k := by
    have hlong := D.long
    omega
  have hsourceCurrent := D.middle k hleft (by omega)
  have hcommonCurrent := D.outer.transition.middle k hleft (by omega)
  have hbCurrent : b.orderSequence.entryOrZero k = T := by
    simpa only [T] using hcommonCurrent.symm.trans hsourceCurrent
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
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftValue := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  have hreferenceFirst : T ≤ c.orderSequence.entryOrZero 0 := by
    simpa only [T, hleftValue] using hfirstOrder
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · left
    have hcMono := c.orderSequence.entryOrZero_le_of_evenGap
      0 k (Nat.zero_le k) hk hkEven
    rw [← b.orderSequence.entryOrZero_of_lt hk,
      ← c.orderSequence.entryOrZero_of_lt hk]
    omega
  · by_cases hdirect : b.orderSequence.entry k hk ≤
        c.orderSequence.entry k hk
    · exact Or.inl hdirect
    · have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
        have hbCurrentEntry : b.orderSequence.entry k hk = T := by
          simpa only [b.orderSequence.entryOrZero_of_lt hk] using hbCurrent
        rw [c.orderSequence.entryOrZero_of_lt hk]
        omega
      have hcParity :=
        c.prefixSum_modEq_mul_of_current_le_reference_le_first
          T k hk hreferenceFirst hcCurrent
      let P := a.beli2019Lemma72_ii b D hfirst
      have haParity := P.source_after (k + 1) (by omega) (by
        have hrightLast := D.outer.right_le_last
        omega)
      let X : Int := (((k + 1 : Nat) : Int) * T)
      have hshift : Int.ModEq 2 (X - 1) (X + 1) := by
        rw [Int.modEq_iff_dvd]
        exact ⟨1, by ring⟩
      have hcPlus := hcParity.add
        (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
      have hparity : Int.ModEq 2
          (a.orderSequence.prefixSum (k + 1))
          (c.orderSequence.prefixSum (k + 1) + 1) := by
        have haBase : Int.ModEq 2
            (a.orderSequence.prefixSum (k + 1)) (X - 1) := by
          simpa only [P, T, X] using haParity
        exact (haBase.trans hshift).trans (by
          simpa only [X] using hcPlus.symm)
      let i : RepresentationIndex (n + 2) (n + 2) := {
        val := k + 1
        pos := by omega
        lt_large := hkNext
        le_small := by omega }
      rcases a.beli2019Lemma65 c hdefect i (by
        simpa only [i] using hparity) with hnext | ⟨hi, hpair⟩
      · left
        have hsourceRight : a.orderSequence.entryOrZero (k + 1) = T := by
          have hindex : k + 1 = D.outer.transition.firstTwo - 1 := by
            omega
          rw [hindex, D.right_source]
        have hnextEntry : a.orderSequence.entryOrZero (k + 1) ≤
            c.orderSequence.entryOrZero k := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
            c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
          convert hnext using 1
          apply congrArg c.order
          apply Fin.ext
          simp only [i]
          omega
        rw [← b.orderSequence.entryOrZero_of_lt hk,
          ← c.orderSequence.entryOrZero_of_lt hk]
        omega
      · right
        have hk0 : 0 < k := by omega
        refine ⟨hk0, hkNext, ?_⟩
        have hkTwo : k + 2 < n + 2 := by
          simpa only [i] using hi.2
        have hpairEntry :
            a.orderSequence.entryOrZero (k + 1) +
                a.orderSequence.entryOrZero (k + 2) ≤
              c.orderSequence.entryOrZero (k - 1) +
                c.orderSequence.entryOrZero k := by
          rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
            a.orderSequence_entryOrZero_eq_order ⟨k + 2, hkTwo⟩,
            c.orderSequence_entryOrZero_eq_order ⟨k - 1, by omega⟩,
            c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
          convert hpair using 1
          congr 1
        have hrightIndex : D.outer.transition.firstTwo - 1 = k + 1 := by
          omega
        have hrightEven : Even
            ((k + 1) - (D.outer.transition.firstTwo - 1)) := by
          rw [hrightIndex]
          exact ⟨0, by omega⟩
        have hbSourceNext :=
          lemma79_typeII_rightEven_targetCurrent_le_sourceNext
            a b D (k + 1) hkTwo (by omega) (by
              simpa only [hrightIndex] using D.outer.right_le_last)
              hrightEven
        have hbSourceNext' : b.orderSequence.entryOrZero (k + 1) ≤
            a.orderSequence.entryOrZero (k + 2) := by
          convert hbSourceNext using 1
        have hsourceRight : a.orderSequence.entryOrZero (k + 1) = T := by
          rw [← hrightIndex, D.right_source]
        have htargetRight : b.orderSequence.entryOrZero (k + 1) = T + 1 := by
          rw [← hrightIndex, D.right_target]
        calc
          b.orderSequence.entry k hk +
              b.orderSequence.entry (k + 1) hkNext =
              b.orderSequence.entryOrZero k +
                b.orderSequence.entryOrZero (k + 1) := by
            rw [b.orderSequence.entryOrZero_of_lt hk,
              b.orderSequence.entryOrZero_of_lt hkNext]
          _ ≤ a.orderSequence.entryOrZero (k + 1) +
                a.orderSequence.entryOrZero (k + 2) := by omega
          _ ≤ c.orderSequence.entryOrZero (k - 1) +
                c.orderSequence.entryOrZero k := hpairEntry
          _ = c.orderSequence.entry (k - 1) (by omega) +
                c.orderSequence.entry k hk := by
            rw [c.orderSequence.entryOrZero_of_lt (by omega),
              c.orderSequence.entryOrZero_of_lt hk]

end BONG.GoodBONG

end Bong
