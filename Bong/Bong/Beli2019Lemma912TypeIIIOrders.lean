/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIIndexP
import Bong.Bong.Beli2019Lemma66

/-!
# Beli (2019), Lemma 9.12: the type-III order condition

The literal type-III image has orders `R₁, R₂ + 1, R₃ + 1` and
then the original tail.  In the residual branch the comparison order at the
second coordinate is exactly `R₂ + 1`.  Its third order is strictly above
its first: equality would make the comparison first gap even by Lemma 6.6,
whereas it is one more than the even source first gap.  These observations
transport condition 2.1(i) to the new index-`p` sublattice.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

private theorem even_sub_of_modEq_two {x y : Int}
    (h : Int.ModEq 2 x y) : Even (y - x) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨z, hz⟩
  exact ⟨z, by omega⟩

/-- In the residual type-III branch the third comparison order is strictly
larger than its first.  Equality would make the first comparison gap even,
whereas it is one more than the even first source gap. -/
theorem beli2019Lemma912_typeIII_comparisonThird_gt_first
    (source : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (hfirst : source.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1)
    (hfirstThird : source.order (0 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)))
    (hfirstGapEven : Even (source.orderGap (0 : Fin (T + 2)))) :
    c.order (0 : Fin (T + 3)) < c.order (2 : Fin (T + 3)) := by
  have hle : c.order (0 : Fin (T + 3)) ≤
      c.order (2 : Fin (T + 3)) := c.order_zero_le_two
  apply lt_of_le_of_ne hle
  intro heq
  let zero : Fin (T + 3) := ⟨0, by omega⟩
  let one : Fin (T + 3) := ⟨1, by omega⟩
  let two : Fin (T + 3) := ⟨2, by omega⟩
  have hzero : zero = (0 : Fin (T + 3)) := by
    apply Fin.ext
    simp only [zero, Fin.val_zero]
  have hone : one = (1 : Fin (T + 3)) := by
    apply Fin.ext
    change 1 = 1 % (T + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have htwo : two = (2 : Fin (T + 3)) := by
    apply Fin.ext
    change 2 = 2 % (T + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hparity := (c.beli2019Lemma66_i zero two
    (by change zero.val ≤ two.val; simp only [zero, two]; omega)
    (by refine ⟨1, ?_⟩; simp [zero, two])
    (by simpa only [hzero, htwo] using heq)).order_modEq one
      (by change zero.val ≤ one.val; simp only [zero, one]; omega)
      (by change one.val ≤ two.val; simp only [one, two]; omega)
  have hcomparisonGapEven : Even
      (c.order (1 : Fin (T + 3)) - c.order (0 : Fin (T + 3))) := by
    exact even_sub_of_modEq_two (by
      simpa only [hzero, hone] using hparity.symm)
  rcases hcomparisonGapEven with ⟨z, hz⟩
  rcases hfirstGapEven with ⟨k, hk⟩
  unfold orderGap at hk
  change source.order (1 : Fin (T + 3)) -
    source.order (0 : Fin (T + 3)) = k + k at hk
  rw [hsecond, ← hfirst] at hz
  omega

/-- Condition 2.1(i) is preserved by the type-III index-`p` construction.
The source is written in the `3 + T` convention used by the construction and
then cast to the `T + 3` convention used by representation conditions. -/
theorem beli2019Lemma912_typeIII_orderCondition
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (hfirstThird : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hac : (a.castLength hlength).RepresentationOrderCondition c le_rfl) :
    (I.bong.castLength hlength).RepresentationOrderCondition c le_rfl := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hcomparisonFirstThird :
      c.order (0 : Fin (T + 3)) < c.order (2 : Fin (T + 3)) := by
    exact beli2019Lemma912_typeIII_comparisonThird_gt_first
      source c hfirst hsecond hfirstThird hfirstGapEven
  have hright (i : Fin (T + 3)) (hi : 3 ≤ i.val) :
      target.order i = source.order i := by
    let j : Fin T := ⟨i.val - 3, by omega⟩
    let iRaw : Fin (3 + T) := ⟨i.val, by omega⟩
    have hij : Fin.natAdd 3 j = iRaw := by
      apply Fin.ext
      simp only [Fin.val_natAdd, j, iRaw]
      omega
    have hraw := beli2019Lemma912TypeIIIIndexPData_order_right a D I j
    rw [hij] at hraw
    simpa only [target, source, GoodBONG.order_castLength, iRaw] using hraw
  intro i
  by_cases hiZero : i.val = 0
  · left
    let iLarge : Fin (T + 3) := ⟨i.val, by omega⟩
    let zero : Fin (T + 3) := ⟨0, by omega⟩
    have hi : i = zero := by
      apply Fin.ext
      exact hiZero
    have hiLarge : iLarge = zero := by
      apply Fin.ext
      exact hiZero
    have htargetZero : target.order zero = source.order zero := by
      simp only [target, source, GoodBONG.order_castLength]
      convert beli2019Lemma912TypeIIIIndexPData_order_zero a D I using 1 <;>
        congr 1 <;> apply Fin.ext <;> simp
    have hzeroOut : zero = (0 : Fin (T + 3)) := by
      apply Fin.ext
      simp only [zero, Fin.val_zero]
    change target.order iLarge ≤ c.order i
    rw [hiLarge, hi, htargetZero, hzeroOut, hfirst]
  by_cases hiOne : i.val = 1
  · left
    let iLarge : Fin (T + 3) := ⟨i.val, by omega⟩
    let one : Fin (T + 3) := ⟨1, by omega⟩
    have hi : i = one := by
      apply Fin.ext
      exact hiOne
    have hiLarge : iLarge = one := by
      apply Fin.ext
      exact hiOne
    have htargetOne : target.order one = source.order one + 1 := by
      simp only [target, source, GoodBONG.order_castLength]
      have honeRaw : (⟨one.val, by omega⟩ : Fin (3 + T)) =
          (1 : Fin (3 + T)) := by
        apply Fin.ext
        change 1 = 1 % (3 + T)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      rw [honeRaw]
      exact beli2019Lemma912TypeIIIIndexPData_order_one a D I
    have honeOut : one = (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [one, Nat.mod_eq_of_lt]
    change target.order iLarge ≤ c.order i
    rw [hiLarge, hi, htargetOne, honeOut, ← hsecond]
  by_cases hiTwo : i.val = 2
  · left
    let iLarge : Fin (T + 3) := ⟨i.val, by omega⟩
    let two : Fin (T + 3) := ⟨2, by omega⟩
    have hi : i = two := by
      apply Fin.ext
      exact hiTwo
    have hiLarge : iLarge = two := by
      apply Fin.ext
      exact hiTwo
    have htargetTwo : target.order two = source.order two + 1 := by
      simp only [target, source, GoodBONG.order_castLength]
      have htwoRaw : (⟨two.val, by omega⟩ : Fin (3 + T)) =
          (2 : Fin (3 + T)) := by
        apply Fin.ext
        change 2 = 2 % (3 + T)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      rw [htwoRaw]
      exact beli2019Lemma912TypeIIIIndexPData_order_two a D I
    have htwoOut : two = (2 : Fin (T + 3)) := by
      apply Fin.ext
      simp [two, Nat.mod_eq_of_lt]
    change target.order iLarge ≤ c.order i
    rw [hiLarge, hi, htargetTwo, htwoOut, ← hfirstThird, hfirst]
    omega
  have hiThree : 3 ≤ i.val := by omega
  rcases hac i with hcurrent | ⟨hiPos, hiNext, hpair⟩
  · left
    rw [hright i hiThree]
    exact hcurrent
  · right
    refine ⟨hiPos, hiNext, ?_⟩
    let next : Fin (T + 3) := ⟨i.val + 1, hiNext⟩
    have hnextThree : 3 ≤ next.val := by
      simp only [next]
      omega
    rw [hright i hiThree, hright next hnextThree]
    simpa only [next] using hpair

end BONG.GoodBONG

end Bong
