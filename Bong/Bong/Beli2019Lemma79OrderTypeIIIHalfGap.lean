/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderCandidateExtraction

/-!
# Beli (2019), Lemma 7.9(i): excluding the type-III half-gap candidate

Lemma 7.8 gives `R - S + 2 < 2e`.  In the hard right-hand parity class,
the next source order is at least the left target boundary and direct
failure puts the third current order below the right target boundary.
Consequently the half-gap candidate is strictly larger than `R - S + 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the coordinate following the hard parity class, the target order is
at most the source order.  Before the last difference their gap is one;
after it the two entries agree. -/
theorem lemma79_typeIII_targetNext_le_sourceNext
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (k : Nat) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero (k + 1) ≤
      a.orderSequence.entryOrZero (k + 1) := by
  rcases heven with ⟨d, hd⟩
  by_cases hkLast : k < D.outer.last
  · have hnextOdd : Odd
        (k + 1 - (D.outer.transition.firstTwo - 1)) := ⟨d, by omega⟩
    have hnextValue := D.outer.source_rightOdd_eq_target_add_one
      D.no_gap_two (k + 1) (by omega) (by omega) hnextOdd
    omega
  · have hkEq : k = D.outer.last := by omega
    have heq := D.outer.lastDifference.after (k + 1)
      (by omega) hkNext
    omega

/-- Along the hard type-III parity class, the source order following the
current coordinate is at least the target order at the left transition. -/
theorem lemma79_typeIII_leftTarget_le_sourceNext
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (k : Nat) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero D.outer.transition.lastZero ≤
      a.orderSequence.entryOrZero (k + 1) := by
  let left := D.outer.transition.lastZero
  rcases heven with ⟨d, hd⟩
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hleftNextEven : Even (k + 1 - left) := ⟨d + 1, by omega⟩
  have htargetLower := b.orderSequence.entryOrZero_le_of_evenGap
    left (k + 1) (by omega) hkNext hleftNextEven
  have htargetSourceNext := a.lemma79_typeIII_targetNext_le_sourceNext
    b D k hkNext hright hlast ⟨d, hd⟩
  exact htargetLower.trans htargetSourceNext

/-- The half-gap candidate at the hard type-III boundary is strictly above
the mixed shift `R - S + 2`. -/
theorem lemma79_typeIII_mixedShift_lt_representationHalfGap
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ + 1)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k) :
    ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) <
      a.representationHalfGap c {
        val := k + 1
        pos := by omega
        lt_large := hkNext
        le_small := hkNext.le } := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let C : Int := b.orderSequence.entryOrZero left -
    a.orderSequence.entryOrZero (left + 1)
  have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
    simp only [left]
    rw [D.adjacent]
    omega
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k hright hlast heven
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentUpper : c.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (left + 1) := by
    rw [hcurrentBoundary, hrightBoundary, hrightIndex] at hcurrent
    omega
  have hsourceNext := a.lemma79_typeIII_leftTarget_le_sourceNext
    b D k hkNext hright hlast heven
  have hdiff : C ≤ a.orderSequence.entryOrZero (k + 1) -
      c.orderSequence.entryOrZero k := by
    dsimp only [C, left] at hcurrentUpper hsourceNext ⊢
    omega
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hgapEntries : a.orderGap center =
      a.orderSequence.entryOrZero (left + 1) -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    rfl
  have hleftBoundary : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hCFormula : C = 1 - a.orderGap center := by
    dsimp only [C]
    rw [hleftBoundary, hgapEntries]
    ring
  have hgap' : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 := by
    simpa only [center, left] using hgap
  have hCLt : C < 2 * (ramificationIndex K : Int) := by
    rw [hCFormula]
    omega
  have hdiffOrders : C ≤
      a.order ⟨k + 1, hkNext⟩ - c.order ⟨k, hk⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
      ← c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
    exact hdiff
  have hrat : (C : ℚ) <
      ((a.order ⟨k + 1, hkNext⟩ - c.order ⟨k, hk⟩ : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ) := by
    have hdiffQ : (C : ℚ) ≤
        ((a.order ⟨k + 1, hkNext⟩ - c.order ⟨k, hk⟩ : Int) : ℚ) := by
      exact_mod_cast hdiffOrders
    have hCLtQ : (C : ℚ) < 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hCLt
    linarith
  change (((C : ℚ)) : WithTop ℚ) <
    (((((a.order ⟨k + 1, hkNext⟩ - c.order ⟨k, hk⟩ : Int) : ℚ) /
      2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  exact_mod_cast hrat

end BONG.GoodBONG

end Bong
