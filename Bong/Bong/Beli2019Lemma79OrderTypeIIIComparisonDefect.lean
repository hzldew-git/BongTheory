/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Local
import Bong.Bong.Beli2019Lemma79OrderTypeIIIThirdDefect

/-!
# Beli (2019), Lemma 7.9(i): the type-III comparison prefix

The strict self-defect separation from the preceding file and the exact
source value from Lemma 7.8 determine the comparison-prefix defect by sharp
capped-defect multiplication.
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
  {L N : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Multiplying the scalar in a capped prefix defect by a square does not
change the defect. -/
theorem truncatedPrefixDefect_mul_square_scalar
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon squareRoot : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b (epsilon * squareRoot ^ 2) i j =
      a.truncatedPrefixDefect b epsilon i j := by
  unfold truncatedPrefixDefect
  rw [show (epsilon * squareRoot ^ 2) * a.prefixProduct i *
      b.prefixProduct j =
        (epsilon * a.prefixProduct i * b.prefixProduct j) *
          squareRoot ^ 2 by
        simp only [pow_two]
        ac_rfl,
    defectOrder_mul_square]

/-- If two self-prefix defects are strictly separated, their comparison
prefix has the smaller defect. -/
theorem comparisonPrefixDefect_eq_of_self_lt_self
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (epsilon : Kˣ) (i : Nat)
    (h : a.truncatedPrefixDefect a epsilon 0 i <
      b.truncatedPrefixDefect b epsilon 0 i) :
    a.truncatedPrefixDefect b 1 i i =
      a.truncatedPrefixDefect a epsilon 0 i := by
  have hsourceSymm : a.truncatedPrefixDefect a epsilon i 0 =
      a.truncatedPrefixDefect a epsilon 0 i := by
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero,
      mul_one, min_top_left, min_top_right]
  have htargetSelf : a.truncatedPrefixDefect b epsilon 0 i =
      b.truncatedPrefixDefect b epsilon 0 i :=
    a.truncatedPrefixDefect_zero_left_eq_self b epsilon i
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a b epsilon epsilon i 0 i (by
      rw [hsourceSymm, htargetSelf]
      exact h)
  calc
    a.truncatedPrefixDefect b 1 i i =
        a.truncatedPrefixDefect b (1 * epsilon ^ 2) i i :=
      (a.truncatedPrefixDefect_mul_square_scalar
        b 1 epsilon i i).symm
    _ = a.truncatedPrefixDefect b (epsilon * epsilon) i i := by
      rw [one_mul, pow_two]
    _ = a.truncatedPrefixDefect a epsilon i 0 := hsharp
    _ = a.truncatedPrefixDefect a epsilon 0 i := hsourceSymm

/-- In the normalized type-III branch, failure of the direct order comparison
forces the mixed prefix defect to equal `R - S + 2`.  Only the local source
part of Lemma 7.8 is needed, so no full-span hypothesis occurs here. -/
theorem lemma79_typeIII_comparisonPrefix_eq_mixedShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {P : Lattice K V}
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q N (n + 2))
    (c : GoodBONG q P (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q P < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlastK : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1)))
    (hcurrent : c.orderSequence.entryOrZero k <
      b.orderSequence.entryOrZero k) :
    a.truncatedPrefixDefect c 1 (k + 1) (k + 1) =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
    rcases hleftEven with ⟨d, hd⟩
    rw [hrightIndex]
    exact ⟨d, by omega⟩
  have hkOdd : Odd k := by
    rcases hrightOdd with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    exact ⟨d + e, by omega⟩
  have hiEven : Even (k + 1) := by
    rcases hkOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hiStart : D.outer.transition.lastZero + 2 ≤ k + 1 := by
    omega
  have hiLast : k + 1 ≤ D.outer.last + 1 := by omega
  have hsource := a.beli2019Lemma78_sourcePrefixDefect_local
    b D hfirst hdefect hnotOverlap hinitial
      (k + 1) hiStart hiLast hiEven
  have hthird := c.lemma79_typeIII_thirdPrefix_gt_mixedShift
    (a := a) (b := b) D hfirst hdefect hnotOverlap hnorm
    k hk hright hlastK heven hcurrent
  have hthird' : a.truncatedPrefixDefect a
      ((-1) ^ ((k + 1) / 2)) 0 (k + 1) <
        c.truncatedPrefixDefect c
          ((-1) ^ ((k + 1) / 2)) 0 (k + 1) := by
    rw [hsource]
    have hleftBound : D.outer.transition.lastZero < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    have hrightBound : D.outer.transition.lastZero + 1 < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    rw [b.orderSequence_entryOrZero_eq_order
      ⟨D.outer.transition.lastZero, hleftBound⟩,
      a.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero + 1, hrightBound⟩] at hthird
    exact hthird
  exact a.comparisonPrefixDefect_eq_of_self_lt_self c
    ((-1) ^ ((k + 1) / 2)) (k + 1) hthird' |>.trans hsource

end BONG.GoodBONG

end Bong
