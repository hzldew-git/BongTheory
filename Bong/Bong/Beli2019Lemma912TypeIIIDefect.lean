/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIOrders
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 9.12: type-III defect transfer after the third boundary

From the fourth coefficient onward the source and its type-III index-`p`
image have identical orders.  Lemma 6.3 therefore identifies their
representation invariant with the image alpha at every boundary `i ≥ 3`.
Remark 6.16 then expresses every image--comparison mixed defect as the
minimum of the source--comparison defect and that image alpha.

The final theorem isolates the two scalar inequalities that remain in the
paper: `B_i ≤ C_i` and `B_i ≤ beta_i`.  Once those are proved, condition
2.1(ii) follows immediately at every boundary `i ≥ 3`.
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

/-- On every boundary from `i = 3` onward, the representation alpha of the
source--image pair is the image alpha. -/
theorem beli2019Lemma912_typeIII_rightAlpha
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 ≤ i.val) :
    (a.castLength hlength).representationAlphaValue
        (I.bong.castLength hlength) i =
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hdefect : source.RepresentationDefectCondition target :=
    (I.sourceRepresentationConditions a D hlength).defectCondition
  apply source.beli2019Lemma63_sameRank_right_value target hdefect i
  intro k hik hk
  let idx : Fin (T + 3) := ⟨k, hk⟩
  rw [source.orderSequence_entryOrZero_eq_order idx,
    target.orderSequence_entryOrZero_eq_order idx]
  exact
    (beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength idx (by simp only [idx]; omega)).symm

/-- Remark 6.16 for the literal type-III image at every boundary `i ≥ 3`.
-/
theorem beli2019Lemma912_typeIII_mixedPrefixDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    {U : Type w} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U}
    (a : GoodBONG q L (3 + T)) (c : GoodBONG s N (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 ≤ i.val)
    (epsilon : Kˣ) (j : Nat) :
    (I.bong.castLength hlength).truncatedPrefixDefect c epsilon i.val j =
      min ((a.castLength hlength).truncatedPrefixDefect c epsilon i.val j)
        ((I.bong.castLength hlength).alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩ : WithTop ℚ) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hdefect : source.RepresentationDefectCondition target :=
    (I.sourceRepresentationConditions a D hlength).defectCondition
  apply source.beli2019Remark616_rightMixedPrefix_at target c hdefect i
  exact beli2019Lemma912_typeIII_rightAlpha a D I hlength i hi

/-- At every boundary `i ≥ 3`, the two scalar comparisons printed in the
proof of Lemma 9.12 imply condition 2.1(ii) for the type-III image. -/
theorem beli2019Lemma912_typeIII_defectAt_of_three_le
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    {U : Type w} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U}
    (a : GoodBONG q L (3 + T)) (c : GoodBONG s N (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 ≤ i.val)
    (hcomparison : (I.bong.castLength hlength).representationAlphaValue c i ≤
      (a.castLength hlength).representationAlphaValue c i)
    (htargetAlpha : (I.bong.castLength hlength).representationAlphaValue c i ≤
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have := i.lt_large; omega⟩) :
    ((I.bong.castLength hlength).representationAlphaValue c i : WithTop ℚ) ≤
      (I.bong.castLength hlength).truncatedPrefixDefect c 1 i.val i.val := by
  rw [beli2019Lemma912_typeIII_mixedPrefixDefect
    a c D I hlength i hi 1 i.val]
  apply le_min
  · exact (WithTop.coe_le_coe.mpr hcomparison).trans (hsource i)
  · exact WithTop.coe_le_coe.mpr htargetAlpha

end BONG.GoodBONG

end Bong
