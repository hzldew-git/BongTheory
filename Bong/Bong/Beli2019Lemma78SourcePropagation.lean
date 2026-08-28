/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78TailBound

/-!
# Beli (2019), Lemma 7.8: propagation of source prefix defects

The first exact prefix defect is joined to every later source tail.  The tail
has strictly larger defect, so sharp capped-defect multiplication preserves
the first value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 7.8: every even source prefix strictly to the right of the
type-III center has the same capped defect. -/
theorem beli2019Lemma78_sourcePrefixDefect
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
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let left := D.outer.transition.lastZero
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hfirstDefect := a.beli2019Lemma78_firstSourcePrefixDefect
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  by_cases hiFirst : i = left + 2
  · subst i
    simpa only [left] using hfirstDefect
  · have hiTail : left + 4 ≤ i := by
      rcases hleftEven with ⟨d, hd⟩
      rcases hiEven with ⟨e, he⟩
      omega
    let firstSign : Kˣ := (-1) ^ ((left + 2) / 2)
    let tailSign : Kˣ := (-1) ^ ((i - (left + 2)) / 2)
    have htail := a.lemma78_typeIII_sourceTail_gt_mixedShift
      b D hfirst i (by simpa only [left] using hiTail) hiLast hiEven
    have hseparation :
        a.truncatedPrefixDefect a firstSign 0 (left + 2) <
          a.truncatedPrefixDefect a tailSign (left + 2) i := by
      rw [show a.truncatedPrefixDefect a firstSign 0 (left + 2) =
          ((((b.order ⟨left, by omega⟩ -
            a.order ⟨left + 1, by omega⟩ : Int) : ℚ)) : WithTop ℚ) by
        simpa only [firstSign, left] using hfirstDefect]
      simpa only [tailSign, left] using htail
    have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
      a a firstSign tailSign 0 (left + 2) i hseparation
    have hsign : firstSign * tailSign = (-1 : Kˣ) ^ (i / 2) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases hiEven with ⟨e, he⟩
      have hsum : (left + 2) / 2 + (i - (left + 2)) / 2 = i / 2 := by
        omega
      dsimp only [firstSign, tailSign]
      rw [← pow_add, hsum]
    calc
      a.truncatedPrefixDefect a ((-1) ^ (i / 2)) 0 i =
          a.truncatedPrefixDefect a (firstSign * tailSign) 0 i := by
        rw [hsign]
      _ = a.truncatedPrefixDefect a firstSign 0 (left + 2) := hsharp
      _ = _ := by simpa only [firstSign, left] using hfirstDefect

end BONG.GoodBONG

end Bong
