/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddEquality

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete odd gap-two beta bound

At an odd current index, the comparison prefix either differs from the
central target defect, in which case sharp defect multiplication proves the
beta estimate, or it equals that defect.  In the latter case extended capped
domination proves the estimate directly or supplies a low witness.  Strict
low-witness domination is handled according as the last comparison alpha is
integral or nonintegral, while equality is excluded by Lemma 7.3(ii) and the
prefix congruences.  This completes lines 5948--5975 of the v2 paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- This branch assembly invokes both the extended-domination and parity chains.
/-- The complete beta estimate at an odd coordinate after a type-I gap-two
endpoint. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_odd_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (htarget : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
        ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
          b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  have hfirstLast : first <= caseEightLastAlphaIndex i := by
    change D.profile.last <= i.val - 1
    omega
  by_cases hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat)
  · rcases caseEight_gapTwo_odd_beta_bound_or_exists_lowWitness
        b c i first hfirstLast H hiOdd hcomparison with
      hdone | ⟨j, hjEven, hjBefore, hlow, hjPair, hjCoefficient⟩
    · exact hdone
    · rcases beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
          a b c D hfirst hgapTwo hlast hnorm j hjEven (by
            simpa only [first] using hlow) with
        ⟨_, hjOrder, htargetOrder, _⟩
      have hsource : b.order first.castSucc = c.order j.castSucc + 1 := by
        simp only [first] at hjOrder htargetOrder ⊢
        omega
      have hiTwo : 2 <= i.val := by omega
      by_cases hstrict :
          ((((c.order j.castSucc -
              c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
              WithTop Rat) <
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat)
      · by_cases hintegral : IsRationalInteger
            (c.alphaValue (evenTargetPreviousAlphaIndex i))
        · exact caseEight_gapTwo_even_beta_bound_of_strict_lowWitness_integral
            b c i first hfirstLast H hiTwo j hsource hstrict hintegral
        · exact caseEight_gapTwo_odd_beta_bound_of_strict_lowWitness_nonintegral
            b c i first hfirstLast H j hsource hstrict hintegral
      · have heq :
            ((((c.order j.castSucc -
                c.order (evenTargetPreviousIndex i) : Int) : Rat) +
              c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
                WithTop Rat) =
            ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
              b.alphaValue first : Rat) : WithTop Rat) :=
          le_antisymm hjCoefficient (le_of_not_gt hstrict)
        exact False.elim
          (beli2019Lemma79_typeI_caseEight_gapTwo_odd_domination_equality_false
            a b c D hfirst hgapTwo hlast hnorm i hafter H hiOdd hprefix
              (by simpa only [first] using hcomparison) j hjEven hjBefore
              (by simpa only [first] using hlow)
              (by simpa only [first] using hjPair)
              (by simpa only [first] using heq))
  · have hcomparisonOrder :=
      beli2019Lemma79_typeI_caseEight_gapTwo_odd_comparisonOrder_ge_boundary
        a b c D hfirst hgapTwo hlast hnorm i hafter H hiOdd hprefix
    exact caseEight_gapTwo_odd_beta_bound_of_comparisonPrefix_ne
      b c i first hfirstLast H hiOdd (by
        simpa only [first] using hcomparisonOrder)
      (by simpa only [first] using htarget) hcomparison

end BONG.GoodBONG

end Bong
