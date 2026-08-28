/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIILong

/-!
# Beli (2019), Lemma 9.12: the four type-III conditions

This file packages the separately proved order, defect, central, and long
clauses for the literal type-III index-`p` image.  It provides both the
original 2006 four-condition statement and the revised 2019 v2 statement
whose third clause is condition (iii').
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

/-- All four original representation conditions for the type-III image. -/
theorem beli2019Lemma912_typeIII_representationConditions
    [PerfectResidueFieldLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
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
    RepresentationConditions (I.bong.castLength hlength) c le_rfl := by
  have horder := beli2019Lemma912_typeIII_orderCondition
    a c D I hlength hfirst hsecond houter hfirstGapEven
      hsource.orderCondition
  have hdefect := beli2019Lemma912_typeIII_defectCondition
    (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
      comparisonAlpha comparisonParity a c D I hlength
        hsource.defectCondition horder hfirst hsecond houter hsecondAlpha
          hfirstAlpha hfirstGapEven hfirstGapLe hsourceSecondLower
  have hcentral :=
    beli2019Lemma912_typeIII_centralRepresentationConditions
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
        a c D I hlength hsource.orderCondition hsource.defectCondition
          hsource.centralRepresentations hfirst hsecond houter hsecondAlpha
            hfirstAlpha hfirstGapEven hfirstGapLe
  have hlong := beli2019Lemma912_typeIII_longRepresentationConditions
    a c D I hlength hsource.longRepresentations
  exact ⟨horder, hdefect, hcentral, hlong⟩

/-- The complete revised v2 representation conditions for the type-III
image, with condition (iii') in place of condition (iii). -/
theorem beli2019Lemma912_typeIII_representationConditionsPrime
    [PerfectResidueFieldLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : RepresentationConditions (a.castLength hlength) c le_rfl)
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
    RepresentationConditionsPrime (I.bong.castLength hlength) c le_rfl := by
  let target := I.bong.castLength hlength
  have hconditions : RepresentationConditions target c le_rfl :=
    beli2019Lemma912_typeIII_representationConditions
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
        (comparisonAlpha := comparisonAlpha)
        (comparisonParity := comparisonParity)
        a c D I hlength hsource hfirst hsecond houter hsecondAlpha
          hfirstAlpha hfirstGapEven hfirstGapLe hsourceSecondLower
  have htriggers := target.beli2019Lemma216
    (sourceLaws := sourceAlpha) (targetLaws := comparisonAlpha)
      c le_rfl hconditions.orderCondition hconditions.defectCondition
  exact (representationConditions_iff_prime target c le_rfl htriggers).mp
    hconditions

end BONG.GoodBONG

end Bong
