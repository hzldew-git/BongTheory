/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIProfile
import Bong.Bong.Beli2019Lemma78TargetPropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-III third prefix

Lemma 7.8 gives the exact alternating target-prefix defect `R - S + 2`.
If the shifted mixed prefix has larger defect, sharp multiplication cancels
the target prefix and identifies the preceding third self-prefix with the
same central value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the strict mixed-defect branch, the alternating third prefix ending
at `i - 1` has exact defect `R - S + 2`. -/
theorem beli2019Lemma79_typeIII_caseSix_thirdPrefixDefect_eq_mixedShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hmixed :
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ) <
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :
    c.truncatedPrefixDefect c ((-1) ^ ((i.val - 1) / 2)) 0
        (i.val - 1) =
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ) := by
  let central : Int :=
    b.orderSequence.entryOrZero D.outer.transition.lastZero -
      a.orderSequence.entryOrZero (D.outer.transition.lastZero + 1)
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  have hiEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hiStart : D.outer.transition.lastZero + 2 ≤ i.val + 1 := by
    rw [D.adjacent] at hright
    omega
  have hiLast : i.val + 1 ≤ D.outer.last + 1 := by omega
  have htargetRaw :=
    (a.beli2019Lemma78_typeIII b D hfirst hlast horder hdefect
      htotal hnotOverlap hinitial (i.val + 1) hiStart hiLast hiEven).2.1
  have hleftBound : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : D.outer.transition.lastZero + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have htarget : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
        ((central : ℚ) : WithTop ℚ) := by
    rw [← b.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero, hleftBound⟩,
      ← a.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero + 1, hrightBound⟩] at htargetRaw
    simpa only [central] using htargetRaw
  have hseparation : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) <
        b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    rw [htarget]
    simpa only [central] using hmixed
  have hsharp := b.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b c ((-1) ^ ((i.val + 1) / 2)) (-1)
      0 (i.val + 1) (i.val - 1) hseparation
  have hexponent : (i.val + 1) / 2 = (i.val - 1) / 2 + 1 := by
    omega
  have hscalar : ((-1 : Kˣ) ^ ((i.val + 1) / 2)) * (-1) =
      (-1) ^ ((i.val - 1) / 2) := by
    rw [hexponent, pow_succ]
    rw [mul_assoc]
    norm_num
  have hzeroLeft := b.truncatedPrefixDefect_zero_left_eq_self
    c ((-1) ^ ((i.val - 1) / 2)) (i.val - 1)
  rw [hscalar, hzeroLeft, htarget] at hsharp
  simpa only [central] using hsharp

end BONG.GoodBONG

end Bong
