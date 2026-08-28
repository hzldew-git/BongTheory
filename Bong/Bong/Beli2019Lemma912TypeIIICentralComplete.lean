/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIICentralHigh
import Bong.Bong.Beli2019Lemma216Complete

/-!
# Beli (2019), Lemma 9.12: complete type-III condition (iii)

The first central boundary is impossible, the boundary at three is the
exceptional argument using Lemma 2.14, and every later boundary transfers
through the common tail.  This file assembles those three cases into
condition 2.1(iii), and then uses Lemma 2.16 to obtain the revised condition
2.1(iii').
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

private theorem centralRepresentationIndex_eq_of_val_eq_typeIII
    {largeRank smallRank : Nat}
    (i j : CentralRepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- Complete condition 2.1(iii) for the type-III image in Lemma 9.12. -/
theorem beli2019Lemma912_typeIII_centralRepresentationConditions
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsourceOrder : (a.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (hsourceDefect : (a.castLength hlength).RepresentationDefectCondition c)
    (hsourceCentral :
      (a.castLength hlength).CentralRepresentationConditions c)
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
      2 * (ramificationIndex K : Int) - 2) :
    (I.bong.castLength hlength).CentralRepresentationConditions c := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  rw [target.centralRepresentationConditions_iff_forall_alphaTrigger c]
  intro i htrigger
  by_cases hiTwo : i.val = 2
  · have hieq :
        i = beli2019Lemma912TypeIIISecondCentralIndex (T := T) := by
      apply centralRepresentationIndex_eq_of_val_eq_typeIII
      simpa only [beli2019Lemma912TypeIIISecondCentralIndex] using hiTwo
    subst i
    exact (beli2019Lemma912_typeIII_not_secondCentralAlphaTrigger
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
        a c D I hlength hfirst hsecond houter hsecondAlpha hfirstAlpha
          hfirstGapEven hfirstGapLe htrigger).elim
  · by_cases hiThree : i.val = 3
    · have hT : 0 < T := by
        have hiBound := i.lt_large
        omega
      have hieq :
          i = beli2019Lemma912TypeIIIThirdCentralIndex (T := T) hT := by
        apply centralRepresentationIndex_eq_of_val_eq_typeIII
        simpa only [beli2019Lemma912TypeIIIThirdCentralIndex] using hiThree
      subst i
      exact beli2019Lemma912_typeIII_thirdCentralRepresentation
        (sourceAlpha := sourceAlpha) a c D I hlength hT hsourceOrder
          hsourceDefect hsourceCentral htrigger
    · have hiFour : 4 ≤ i.val := by
        have hiPositive := i.one_lt
        omega
      have hsourceTrigger :=
        beli2019Lemma912_typeIII_centralAlphaTrigger_source_of_target_of_four_le
          (sourceAlpha := sourceAlpha) a c D I hlength i hiFour htrigger
      have hsourceRepresentation := hsourceCentral i hsourceTrigger
      have hprefix :=
        beli2019Lemma912_typeIII_sourcePrefix_represents_targetPrefix
          a D I hlength i.val (by omega) i.lt_large.le
      exact hsourceRepresentation.trans hprefix

/-- The revised v2 condition 2.1(iii') for the type-III image follows from
the complete original central condition and Lemma 2.16. -/
theorem beli2019Lemma912_typeIII_centralRepresentationConditionsPrime
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsourceOrder : (a.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (hsourceDefect : (a.castLength hlength).RepresentationDefectCondition c)
    (hsourceCentral :
      (a.castLength hlength).CentralRepresentationConditions c)
    (htargetOrder : (I.bong.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (htargetDefect :
      (I.bong.castLength hlength).RepresentationDefectCondition c)
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
      2 * (ramificationIndex K : Int) - 2) :
    (I.bong.castLength hlength).CentralRepresentationConditionsPrime c := by
  let target := I.bong.castLength hlength
  have hcentral : target.CentralRepresentationConditions c :=
    beli2019Lemma912_typeIII_centralRepresentationConditions
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
        a c D I hlength hsourceOrder hsourceDefect hsourceCentral hfirst
          hsecond houter hsecondAlpha hfirstAlpha hfirstGapEven hfirstGapLe
  have htriggers := target.beli2019Lemma216
    (sourceLaws := sourceAlpha) (targetLaws := comparisonAlpha)
      c le_rfl htargetOrder htargetDefect
  exact (target.centralRepresentationConditions_iff_prime c htriggers).mp
    hcentral

end BONG.GoodBONG

end Bong
