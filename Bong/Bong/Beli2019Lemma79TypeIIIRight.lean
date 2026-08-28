/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIRightSource
import Bong.Bong.Beli2019Lemma79RightProfileBeta
import Bong.Bong.Beli2019Lemma79TypeIIIRightComparison
import Bong.Bong.Beli2019Lemma79MixedAssembly

/-!
# Beli (2019), Lemma 7.9(ii): type-III case 7

This assembles both order subcases of the alternating right interval.  The
non-strict subcase uses the target-alpha recursion; in the strict subcase,
the source and target mixed-prefix defects coincide by Lemma 7.8 and the
domination argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- The strict branch combines two long dependent-prefix calculations.
/-- Lemma 7.9(ii), case 7, for a normalized full-span type-III pair. -/
theorem beli2019Lemma79_ii_typeIII_caseSeven
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  rcases hleftEven with ⟨e, he⟩
  rcases hodd with ⟨d, hd⟩
  have hiEven : Even i.val := by
    refine ⟨e + d + 1, ?_⟩
    rw [D.adjacent] at hd
    omega
  have hiStart : D.outer.transition.lastZero + 2 ≤ i.val := by
    rw [← D.adjacent]
    omega
  have hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
    simpa only using
      (a.beli2019Lemma69_ii_typeIII_targetRightValue
        b D hfirst hlast horderAB hdefectAB htotal hnotOverlap hinitial
          i.val hiStart hiEven i.lt_large)
  by_cases hcurrent : b.order ⟨i.val - 1, by omega⟩ ≤
      c.order ⟨i.val - 1, by omega⟩
  · apply lemma79_ii_of_rightMixedPrefix_branches
      a b c hdefectAB hdefectAC i hAlpha
    · intro _
      exact lemma79_typeIII_right_alpha_le_sourceAlpha
        a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
          hinitial i hright hbeforeLast ⟨d, hd⟩
    · intro _
      exact lemma79_rightProfile_beta_bound_of_target_le_comparison
        a b c D.outer i hright hbeforeLast ⟨d, hd⟩ hcurrent
  · have hstrict : c.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ := lt_of_not_ge hcurrent
    have heq :=
      lemma79_typeIII_right_comparisonPrefixes_eq_of_comparison_lt_target
        a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
          hinitial hnorm i hright hbeforeLast ⟨d, hd⟩ hstrict
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) :=
        lemma79_typeIII_right_alpha_le_sourceAlpha
          a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
            hinitial i hright hbeforeLast ⟨d, hd⟩
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ = b.truncatedPrefixDefect c 1 i.val i.val := heq.symm

end BONG.GoodBONG

end Bong
