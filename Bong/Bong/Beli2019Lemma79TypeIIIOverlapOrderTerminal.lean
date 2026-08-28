/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIITerminal
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrder

/-!
# Beli (2019), Lemma 7.9(i): the overlapping type-III endpoint

At the final coordinate there is no following source coefficient, so the
ordinary Lemma 6.5 argument is unavailable.  In the central-gap-one branch,
Lemma 7.2(ii) says that the full source order sum is one below the constant
boundary model.  Failure of the desired terminal comparison gives the
unshifted model for the comparison BONG.  The two full value products belong
to the same quadratic space, hence have congruent valuations modulo two, and
these two conclusions are incompatible.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the right transition of an overlapping type-III profile, the target
boundary is one above the target value at the left transition. -/
theorem lemma79_typeIII_overlap_rightBoundary_eq_leftTarget_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    b.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) =
      b.orderSequence.entryOrZero D.outer.transition.lastZero + 1 := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero left
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftBound : left < n + 2 := by
    simp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hleftGapBound : left < n + 1 := by
    simp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let center : Fin (n + 1) := ⟨left, hleftGapBound⟩
  have hgapFormula : a.orderGap center =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
          simp only [right]
          have hbound := D.outer.transition.firstTwo_le_rank
          omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [center, Fin.val_succ]
    exact hrightEq.symm
  have hoverlap' : a.orderGap center = 1 := by
    simpa only [center, left] using hoverlap
  have hleftBoundary : T =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [T, left] using D.outer.transition.leftBoundary
  have hsourceRight : a.orderSequence.entryOrZero right = T := by
    rw [hgapFormula] at hoverlap'
    omega
  have hrightBoundary := D.outer.transition.rightBoundary
  simpa only [right, left, T, hsourceRight] using hrightBoundary

/-- The full-rank endpoint of condition 2.1(i) for the overlapping type-III
branch. -/
theorem beli2019Lemma79_i_typeIII_overlap_terminal
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hkTerminal : k + 1 = n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k (by omega) ≤
      c.orderSequence.entry k (by omega) := by
  have hk : k < n + 2 := by omega
  by_contra hnot
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hrightBoundary :=
    lemma79_typeIII_overlap_rightBoundary_eq_leftTarget_add_one
      a b D hoverlap
  have hbCurrent : b.orderSequence.entryOrZero k = T + 1 := by
    exact hcurrentBoundary.trans (by simpa only [T] using hrightBoundary)
  have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
    rw [b.orderSequence.entryOrZero_of_lt hk] at hbCurrent
    rw [c.orderSequence.entryOrZero_of_lt hk]
    omega
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
  have hcParity :=
    c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hk hreferenceFirst hcCurrent
  let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
  have haParity := P.source_after (k + 1) (by
    have hseparated := D.outer.transition.separated
    omega) (by omega)
  have hfullParity := a.fullPrefixSum_modEq c
  have hacParity : Int.ModEq 2
      (a.orderSequence.prefixSum (k + 1))
      (c.orderSequence.prefixSum (k + 1)) := by
    simpa only [hkTerminal] using hfullParity
  let X : Int := (((k + 1 : Nat) : Int) * T)
  have hcontradiction : Int.ModEq 2 (X - 1) X := by
    have ha : Int.ModEq 2
        (a.orderSequence.prefixSum (k + 1)) (X - 1) := by
      simpa only [P, T, X] using haParity
    have hc : Int.ModEq 2
        (c.orderSequence.prefixSum (k + 1)) X := by
      simpa only [X] using hcParity
    exact ha.symm.trans (hacParity.trans hc)
  rw [Int.modEq_iff_dvd] at hcontradiction
  rcases hcontradiction with ⟨d, hd⟩
  omega

end BONG.GoodBONG

end Bong
