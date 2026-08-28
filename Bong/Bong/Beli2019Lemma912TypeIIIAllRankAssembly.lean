/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIINormalizationAllRanks
import Bong.Bong.Beli2019Lemma912TypeIIIAllRanks
import Bong.Bong.Beli2019Lemma912TypeIIIConditions

/-!
# Beli (2019), Lemma 9.12: all-rank type-III assembly

This file joins the rank-three normalization, the endpoint-aware Lemma 9.11
coefficient construction, and the already uniform proof of the four
representation conditions.  The result is stated with the exact scalar facts
used by the type-III branch, so no nonexistent fourth or fifth coordinate is
mentioned in ranks three and four.
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

/-- The normalized ternary pair satisfies the endpoint-aware hypotheses of
the all-rank coefficient construction. -/
theorem exists_beli2019Lemma912TypeIIIRealization_of_normalization_allRanks
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (T + 3))
    (S : Beli2019Lemma912TypeIIINormalizationDataAllRanks a)
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hsecondLower : a.order (0 : Fin (T + 3)) ≤
      a.order (1 : Fin (T + 3)))
    (hfourth : ∀ hT : 0 < T,
      a.order (1 : Fin (T + 3)) < a.order (⟨3, by omega⟩ : Fin (T + 3)))
    (hfifth : ∀ hT : 1 < T,
      a.order (0 : Fin (T + 3)) < a.order (⟨4, by omega⟩ : Fin (T + 3))) :
    let hforward : T + 3 = 3 + T := by omega
    let source := S.transformed.castLength hforward
    ∃ D : Beli2019Lemma911Data source.typeIIIPair,
      Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + T)
        (typeIIIValues source D)) := by
  let hforward : T + 3 = 3 + T := by omega
  let source := S.transformed.castLength hforward
  have hsourceOrderOriginal (i : Nat) (hi : i < 3 + T)
      (hout : i < T + 3) :
      source.order (⟨i, hi⟩ : Fin (3 + T)) =
        a.order (⟨i, hout⟩ : Fin (T + 3)) := by
    rw [show source = S.transformed.castLength hforward by rfl,
      GoodBONG.order_castLength]
    exact (S.sameOrders _).symm
  have horderZero : source.order (⟨0, by omega⟩ : Fin (3 + T)) =
      a.order (0 : Fin (T + 3)) := by
    simpa using hsourceOrderOriginal 0 (by omega) (by omega)
  have horderOne : source.order (⟨1, by omega⟩ : Fin (3 + T)) =
      a.order (1 : Fin (T + 3)) := by
    simpa using hsourceOrderOriginal 1 (by omega) (by omega)
  have horderTwo : source.order (⟨2, by omega⟩ : Fin (3 + T)) =
      a.order (2 : Fin (T + 3)) := by
    calc
      source.order (⟨2, by omega⟩ : Fin (3 + T)) =
          a.order (⟨2, by omega⟩ : Fin (T + 3)) :=
        hsourceOrderOriginal 2 (by omega) (by omega)
      _ = a.order (2 : Fin (T + 3)) := by
        congr 1
  have hboundary :
      (((source.order (⟨2, by omega⟩ : Fin (3 + T)) -
        source.order (⟨1, by omega⟩ : Fin (3 + T)) : Int) : ℚ) :
          WithTop ℚ) +
        defectOrder (-(source.valueUnit
            (⟨1, by omega⟩ : Fin (3 + T)) *
          source.valueUnit (⟨2, by omega⟩ : Fin (3 + T)))) = 1 := by
    have h := S.pairBoundary
    unfold orderGap adjacentDefect adjacentProduct at h
    have hcast : Fin.castSucc (1 : Fin (T + 2)) =
        (⟨1, by omega⟩ : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    have hsucc : Fin.succ (1 : Fin (T + 2)) =
        (⟨2, by omega⟩ : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc] at h
    simpa only [source, GoodBONG.order_castLength, valueUnit_castLength] using h
  have hzero : source.order (⟨0, by omega⟩ : Fin (3 + T)) ≤
      source.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 := by
    rw [horderZero, horderTwo]
    omega
  have hone : ∀ hT : 0 < T,
      source.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 ≤
        source.order (⟨3, by omega⟩ : Fin (3 + T)) := by
    intro hT
    rw [horderOne, hsourceOrderOriginal 3 (by omega) (by omega)]
    exact Int.add_one_le_iff.mpr (hfourth hT)
  have htwo : ∀ hT : 1 < T,
      source.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 ≤
        source.order (⟨4, by omega⟩ : Fin (3 + T)) := by
    intro hT
    rw [horderTwo, hsourceOrderOriginal 4 (by omega) (by omega)]
    rw [← houter]
    exact Int.add_one_le_iff.mpr (hfifth hT)
  have hleft : 0 ≤
      source.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 -
        source.order (⟨0, by omega⟩ : Fin (3 + T)) := by
    rw [horderOne, horderZero]
    omega
  have hright : ∀ hT : 0 < T,
      0 ≤ source.order (⟨3, by omega⟩ : Fin (3 + T)) -
        (source.order (⟨2, by omega⟩ : Fin (3 + T)) + 1) := by
    intro hT
    rw [hsourceOrderOriginal 3 (by omega) (by omega), horderTwo, ← houter]
    have := hfourth hT
    omega
  exact exists_beli2019Lemma912TypeIIIRealization_allRanks
    source hboundary hzero hone htwo hleft hright

set_option maxHeartbeats 8000000 in
-- The normalization, realization, and four-condition package elaborate together.
/-- A complete type-III index-`p` reduction in every rank at least three.
The fourth and fifth order hypotheses are conditional on the existence of
those coordinates. -/
theorem exists_beli2019Lemma912_typeIIIIndexPReduction_allRanks
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hgapEven : Even (a.orderGap (0 : Fin (T + 2))))
    (hgapLe : a.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2)
    (hsecondAlpha : a.alphaValue (1 : Fin (T + 2)) = 1)
    (hfirstAlpha : a.alphaValue (0 : Fin (T + 2)) =
      c.alphaValue (0 : Fin (T + 2)))
    (hfirst : a.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      a.order (1 : Fin (T + 3)) + 1)
    (hsecondLower : a.order (0 : Fin (T + 3)) ≤
      a.order (1 : Fin (T + 3)))
    (hfourth : ∀ hT : 0 < T,
      a.order (1 : Fin (T + 3)) < a.order (⟨3, by omega⟩ : Fin (T + 3)))
    (hfifth : ∀ hT : 1 < T,
      a.order (0 : Fin (T + 3)) < a.order (⟨4, by omega⟩ : Fin (T + 3)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (T + 2))) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (T + 2)) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceAlpha
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases exists_beli2019Lemma912TypeIIINormalizationData_allRanks
      a houter hgapEven hsecondAlpha with ⟨S⟩
  have htransformed :
      RepresentationConditions S.transformed c (Nat.le_refl (T + 2)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      S.transformed c c (Nat.le_refl (T + 2))).mp hsource
  rcases exists_beli2019Lemma912TypeIIIRealization_of_normalization_allRanks
      a S houter hsecondLower hfourth hfifth with ⟨D, ⟨C⟩⟩
  let hforward : T + 3 = 3 + T := by omega
  let hback : 3 + T = T + 3 := by omega
  let source := S.transformed.castLength hforward
  rcases exists_beli2019Lemma912TypeIIIIndexPData
      (structural := structural) source D C with ⟨I⟩
  have hsourceBack : source.castLength hback = S.transformed := by
    exact castLength_castLength S.transformed hforward hback
  have hsourceNorm :
      RepresentationConditions (source.castLength hback) c le_rfl := by
    rw [hsourceBack]
    exact htransformed
  have hfirstTransformed : S.transformed.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)) :=
    (S.sameOrders (0 : Fin (T + 3))).symm.trans hfirst
  have hsecondTransformed : c.order (1 : Fin (T + 3)) =
      S.transformed.order (1 : Fin (T + 3)) + 1 := by
    calc
      c.order (1 : Fin (T + 3)) = a.order (1 : Fin (T + 3)) + 1 := hsecond
      _ = S.transformed.order (1 : Fin (T + 3)) + 1 :=
        congrArg (fun z : Int => z + 1) (S.sameOrders _)
  have houterTransformed : S.transformed.order (0 : Fin (T + 3)) =
      S.transformed.order (2 : Fin (T + 3)) := by
    calc
      S.transformed.order (0 : Fin (T + 3)) = a.order 0 :=
        (S.sameOrders _).symm
      _ = a.order 2 := houter
      _ = S.transformed.order (2 : Fin (T + 3)) := S.sameOrders _
  have hsecondAlphaTransformed : S.transformed.alphaValue
      (1 : Fin (T + 2)) = 1 :=
    (S.sameAlphas (1 : Fin (T + 2))).symm.trans hsecondAlpha
  have hfirstAlphaTransformed : S.transformed.alphaValue
      (0 : Fin (T + 2)) = c.alphaValue (0 : Fin (T + 2)) :=
    (S.sameAlphas (0 : Fin (T + 2))).symm.trans hfirstAlpha
  have hgapEvenTransformed :
      Even (S.transformed.orderGap (0 : Fin (T + 2))) := by
    unfold orderGap at hgapEven ⊢
    rw [← S.sameOrders (Fin.castSucc (0 : Fin (T + 2))),
      ← S.sameOrders (Fin.succ (0 : Fin (T + 2)))]
    exact hgapEven
  have hgapLeTransformed : S.transformed.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap at hgapLe ⊢
    rw [← S.sameOrders (Fin.castSucc (0 : Fin (T + 2))),
      ← S.sameOrders (Fin.succ (0 : Fin (T + 2)))]
    exact hgapLe
  have hsecondLowerTransformed : S.transformed.order (0 : Fin (T + 3)) ≤
      S.transformed.order (1 : Fin (T + 3)) := by
    rw [← S.sameOrders (0 : Fin (T + 3)),
      ← S.sameOrders (1 : Fin (T + 3))]
    exact hsecondLower
  have htarget : RepresentationConditions (I.bong.castLength hback) c le_rfl := by
    apply beli2019Lemma912_typeIII_representationConditions
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
      (comparisonAlpha := comparisonAlpha)
      (comparisonParity := comparisonParity)
      source c D I hback hsourceNorm
    · rw [hsourceBack]
      exact hfirstTransformed
    · rw [hsourceBack]
      exact hsecondTransformed
    · rw [hsourceBack]
      exact houterTransformed
    · rw [hsourceBack]
      exact hsecondAlphaTransformed
    · rw [hsourceBack]
      exact hfirstAlphaTransformed
    · rw [hsourceBack]
      exact hgapEvenTransformed
    · rw [hsourceBack]
      exact hgapLeTransformed
    · rw [hsourceBack]
      exact hsecondLowerTransformed
  exact ⟨{
    index_eq := rfl
    lattice := I.lattice
    inclusion := I.inclusion
    targetBONG := I.bong.castLength hback
    conditions := htarget }⟩

end BONG.GoodBONG

end Bong
