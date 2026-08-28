/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIILowDefect

/-!
# Beli (2019), Lemma 9.12: the complete type-III defect condition

The first two boundaries were proved separately because they use the special
identities from Lemma 8.12 and the defect-one argument.  Every later boundary
was proved by splitting the third gap into the large, even-small, and
odd-small cases.  This file assembles those pointwise results into condition
2.1(ii) for the type-III image.
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

private theorem representationIndex_eq_of_val_eq_typeIII
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- Condition 2.1(ii) for the complete type-III image in Lemma 9.12. -/
theorem beli2019Lemma912_typeIII_defectCondition
    [PerfectResidueFieldLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    (comparisonParity : Beli2009AlphaParityLaws.{u, w} K)
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (horder : (I.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hsecondAlpha : (a.castLength hlength).alphaValue
      (1 : Fin (T + 2)) = 1)
    (hfirstAlpha : (a.castLength hlength).alphaValue
      (0 : Fin (T + 2)) = c.alphaValue (0 : Fin (T + 2)))
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hfirstGapLe : (a.castLength hlength).orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2)
    (hsourceSecondLower :
      (a.castLength hlength).order (0 : Fin (T + 3)) ≤
        (a.castLength hlength).order (1 : Fin (T + 3))) :
    (I.bong.castLength hlength).RepresentationDefectCondition c := by
  intro i
  by_cases hiOne : i.val = 1
  · let first := firstRepresentationIndex (T + 1) (T + 2)
    have hieq : i = first := by
      apply representationIndex_eq_of_val_eq_typeIII
      simpa only [first, firstRepresentationIndex] using hiOne
    subst i
    exact beli2019Lemma912_typeIII_defectAt_one
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
        a c D I hlength hsource hfirst houter hsecondAlpha
          hfirstGapEven hfirstGapLe
  · by_cases hiTwo : i.val = 2
    · let second := secondRepresentationIndex T (T + 1)
      have hieq : i = second := by
        apply representationIndex_eq_of_val_eq_typeIII
        simpa only [second, secondRepresentationIndex] using hiTwo
      subst i
      exact beli2019Lemma912_typeIII_defectAt_two
        (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
          comparisonAlpha comparisonParity a c D I hlength hfirst hsecond
            houter hsecondAlpha hfirstAlpha hfirstGapEven hfirstGapLe
    · have hiThree : 3 ≤ i.val := by
        have hiPositive := i.pos
        omega
      have hcomparison :=
        beli2019Lemma912_typeIII_representationAlphaValue_le_source
          (alpha := sourceAlpha) a c D I hlength i hiThree
      have htargetAlpha :=
        beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_three_le
          (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
            comparisonAlpha a c D I hlength hsource horder hfirst hsecond
              houter hfirstGapEven hsourceSecondLower i hiThree
      exact beli2019Lemma912_typeIII_defectAt_of_three_le
        (alpha := sourceAlpha) a c D I hlength hsource i hiThree
          hcomparison htargetAlpha

end BONG.GoodBONG

end Bong
