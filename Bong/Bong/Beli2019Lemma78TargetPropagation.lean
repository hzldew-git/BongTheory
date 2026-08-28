/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIIRightValue
import Bong.Bong.Beli2019FullRankDefect

/-!
# Beli (2019), Lemma 7.8: target prefix defects

Remark 6.16, the right-branch classification from Lemma 6.9(ii), and the
target-alpha lower bound identify every nonterminal target prefix defect.
At full rank the comparison defect is infinite, so the same conclusion
follows without an endpoint alpha cap.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At common full rank, multiplying by the infinite comparison defect does
not change any self-prefix defect. -/
theorem truncatedPrefixDefect_self_full_eq
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (epsilon : Kˣ) :
    b.truncatedPrefixDefect b epsilon 0 (n + 1) =
      a.truncatedPrefixDefect a epsilon 0 (n + 1) := by
  have hcross := a.truncatedPrefixDefect_full_eq_top b
  by_cases hsourceTop :
      a.truncatedPrefixDefect a epsilon 0 (n + 1) = ⊤
  · have hdomination := a.truncatedPrefixDefect_domination
      a b epsilon 1 0 (n + 1) (n + 1)
    have hmixedTop : a.truncatedPrefixDefect b epsilon 0 (n + 1) = ⊤ := by
      have htopLe : (⊤ : WithTop ℚ) ≤
          a.truncatedPrefixDefect b epsilon 0 (n + 1) := by
        simpa only [hsourceTop, hcross, mul_one, min_self] using hdomination
      exact top_unique htopLe
    rw [hsourceTop]
    calc
      b.truncatedPrefixDefect b epsilon 0 (n + 1) =
          a.truncatedPrefixDefect b epsilon 0 (n + 1) :=
        (a.truncatedPrefixDefect_zero_left_eq_self
          b epsilon (n + 1)).symm
      _ = ⊤ := hmixedTop
  · have hsourceLt : a.truncatedPrefixDefect a epsilon 0 (n + 1) <
        a.truncatedPrefixDefect b 1 (n + 1) (n + 1) := by
      rw [hcross]
      exact WithTop.lt_top_iff_ne_top.mpr hsourceTop
    have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
      a b epsilon 1 0 (n + 1) (n + 1) hsourceLt
    calc
      b.truncatedPrefixDefect b epsilon 0 (n + 1) =
          a.truncatedPrefixDefect b epsilon 0 (n + 1) :=
        (a.truncatedPrefixDefect_zero_left_eq_self
          b epsilon (n + 1)).symm
      _ = a.truncatedPrefixDefect a epsilon 0 (n + 1) := by
        simpa only [mul_one] using hsharp

/-- Lemma 7.8 at a nonterminal target prefix. -/
theorem beli2019Lemma78_targetPrefixDefect_of_lt_rank
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i)
    (hiNonterminal : i < n + 2) :
    b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by omega, hiNonterminal, hiNonterminal.le⟩
  have hclassification :=
    a.beli2019Lemma69_ii_typeIII_targetRightValue
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      i hiStart hiEven hiNonterminal
  have hremark := a.beli2019Remark616_rightPrefix
    b hdefect idx (by simpa only [idx] using hclassification)
      ((-1) ^ (i / 2))
  have hsource := a.beli2019Lemma78_sourcePrefixDefect
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
    i hiStart hiLast hiEven
  have hbeta := a.lemma78_typeIII_targetAlpha_ge_mixedShift
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
    i hiStart hiLast hiEven hiNonterminal
  rw [hremark, hsource]
  apply min_eq_left
  exact_mod_cast hbeta

/-- Lemma 7.8 for every even target prefix, including the full-rank endpoint.
-/
theorem beli2019Lemma78_targetPrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i) :
    b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  by_cases hiNonterminal : i < n + 2
  · exact a.beli2019Lemma78_targetPrefixDefect_of_lt_rank
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      i hiStart hiLast hiEven hiNonterminal
  · have hiRank : i = n + 2 := by
      rw [hlast] at hiLast
      omega
    subst i
    have hsource := a.beli2019Lemma78_sourcePrefixDefect
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      (n + 2) hiStart hiLast hiEven
    rw [a.truncatedPrefixDefect_self_full_eq b ((-1) ^ ((n + 2) / 2))]
    exact hsource

/-- Complete fixed-index form of Beli (2019), Lemma 7.8. -/
theorem beli2019Lemma78_typeIII
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i) :
    a.truncatedPrefixDefect a ((-1) ^ (i / 2)) 0 i =
        ((((b.order ⟨D.outer.transition.lastZero, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ -
            a.order ⟨D.outer.transition.lastZero + 1, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ : Int) : ℚ)) : WithTop ℚ) ∧
      b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i =
        ((((b.order ⟨D.outer.transition.lastZero, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ -
            a.order ⟨D.outer.transition.lastZero + 1, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ : Int) : ℚ)) : WithTop ℚ) ∧
      a.alphaValue ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ = 1 ∧
      b.alphaValue ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ = 1 ∧
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ + 1 := by
  refine ⟨a.beli2019Lemma78_sourcePrefixDefect
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      i hiStart hiLast hiEven, ?_, ?_⟩
  · exact a.beli2019Lemma78_targetPrefixDefect
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      i hiStart hiLast hiEven
  · exact a.beli2019Lemma78_alphas_and_gap
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial

end BONG.GoodBONG

end Bong
