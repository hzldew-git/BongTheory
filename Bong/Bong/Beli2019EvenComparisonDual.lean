/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EvenComparison
import Bong.Bong.Beli2019SequenceDual

/-!
# Even comparisons and reverse duality

For a sequence of even length, comparisons at its even coordinates together
with comparisons at the even coordinates of the reversed, negated, swapped
pair give Beli's comparison at every coordinate.
-/

namespace Bong

universe u v

/-- Beli's direct-or-pair comparison restricted to even coordinates. -/
def BeliEvenLE {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
    [IsOrderedAddMonoid Gamma] {n : Nat}
    (x y : BeliOrderSequence (2 * n) Gamma) : Prop :=
  ∀ k : Fin n,
    x.value ⟨2 * k.val, by omega⟩ ≤ y.value ⟨2 * k.val, by omega⟩ ∨
      ∃ hk : 0 < k.val,
        x.value ⟨2 * k.val, by omega⟩ +
            x.value ⟨2 * k.val + 1, by omega⟩ ≤
          y.value ⟨2 * k.val - 1, by omega⟩ +
            y.value ⟨2 * k.val, by omega⟩

namespace BeliEvenLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Even comparisons for a pair and its swapped reverse-negate pair assemble
to the full Beli order. -/
theorem to_beliOrderLE_of_reverseNegate {n : Nat}
    {x y : BeliOrderSequence (2 * n) Gamma}
    (hEven : BeliEvenLE x y)
    (hReverse : BeliEvenLE y.reverseNegate x.reverseNegate) :
    BeliOrderLE x y := by
  refine { rank := le_rfl, compare := ?_ }
  intro i hi
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · let k : Fin n := ⟨i / 2, by omega⟩
    have hki : 2 * k.val = i := by
      simp only [k]
      omega
    rcases hEven k with hdirect | ⟨hk, hpair⟩
    · left
      simpa only [BeliOrderSequence.entry, hki] using hdirect
    · right
      refine ⟨by omega, by omega, ?_⟩
      simpa only [BeliOrderSequence.entry, hki] using hpair
  · let r := 2 * n - 1 - i
    have hrlt : r < 2 * n := by
      dsimp only [r]
      omega
    have hrmod : r % 2 = 0 := by
      dsimp only [r]
      omega
    let k : Fin n := ⟨r / 2, by omega⟩
    have hkr : 2 * k.val = r := by
      simp only [k]
      omega
    rcases hReverse k with hdirect | ⟨hk, hpair⟩
    · left
      have hdirect' :
          y.reverseNegate.value ⟨r, hrlt⟩ ≤
            x.reverseNegate.value ⟨r, hrlt⟩ := by
        simpa only [hkr] using hdirect
      have hrev : Fin.rev ⟨r, hrlt⟩ = ⟨i, hi⟩ := by
        apply Fin.ext
        simp only [Fin.rev, Fin.val_mk, r]
        omega
      rw [BeliOrderSequence.reverseNegate_value,
        BeliOrderSequence.reverseNegate_value, hrev] at hdirect'
      simpa only [neg_le_neg_iff, BeliOrderSequence.entry] using hdirect'
    · have hrpos : 0 < r := by omega
      have hi0 : 0 < i := by omega
      have hiNext : i + 1 < 2 * n := by
        dsimp only [r] at hrpos
        omega
      have hrNext : r + 1 < 2 * n := by
        have := k.isLt
        omega
      have hrPrevious : r - 1 < 2 * n := by omega
      right
      refine ⟨hi0, hiNext, ?_⟩
      have hpair' :
          y.reverseNegate.value ⟨r, hrlt⟩ +
              y.reverseNegate.value ⟨r + 1, hrNext⟩ ≤
            x.reverseNegate.value ⟨r - 1, hrPrevious⟩ +
              x.reverseNegate.value ⟨r, hrlt⟩ := by
        simpa only [hkr] using hpair
      have hrev : Fin.rev ⟨r, hrlt⟩ = ⟨i, hi⟩ := by
        apply Fin.ext
        simp only [Fin.rev, Fin.val_mk, r]
        omega
      have hrevNext : Fin.rev ⟨r + 1, hrNext⟩ =
          ⟨i - 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.rev, Fin.val_mk, r]
        omega
      have hrevPrevious : Fin.rev ⟨r - 1, hrPrevious⟩ =
          ⟨i + 1, hiNext⟩ := by
        apply Fin.ext
        simp only [Fin.rev, Fin.val_mk, r]
        omega
      rw [BeliOrderSequence.reverseNegate_value,
        BeliOrderSequence.reverseNegate_value,
        BeliOrderSequence.reverseNegate_value,
        BeliOrderSequence.reverseNegate_value,
        hrev, hrevNext, hrevPrevious] at hpair'
      have hneg := neg_le_neg hpair'
      simpa only [neg_add_rev, neg_neg, BeliOrderSequence.entry] using hneg

end BeliEvenLE

namespace BONG.GoodBONG

open Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Conditions 2.1(i),(ii) give the even-coordinate comparison of the two
`W`-sequences. -/
theorem weightSequence_beliEvenLE
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    BeliEvenLE a.weightSequence b.weightSequence := by
  intro k
  exact a.weightSequence_compare_even b horder hdefect k

end BONG.GoodBONG

end Bong
