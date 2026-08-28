/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankFourBelow

/-!
# Beli (2019), Lemma 8.14: the rank-four equality boundary

This file treats case (c) of the quaternary proof, where
`alpha_2 + alpha_3 = 2e`.  It first isolates the successful final-binary
transformation.  The accompanying Hilbert-symbol calculation shows that,
after the paper's preliminary normalization `d(-a_1a_2) > alpha_2`, this
transformation preserves the isotropy type of the initial ternary prefix.
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
  {L : Lattice K V} {M : Lattice K W}

/-- On the equality boundary the final binary segment may be transformed
whenever it is outside the exceptional alternative of Lemma 8.8. -/
theorem exists_rankFour_boundary_lastPairScaling_of_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hnotExceptional :
      let segment := a.toBONG.segmentWitness 2 2 (by omega)
      ¬(segment.toGoodBONG a.good).Beli2019Lemma88Exceptional) :
    Nonempty (Beli2019Lemma814LastPairScalingData a) := by
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have hlast := rankFour_boundary_lastBinaryAlpha_eq a hsum
  have halpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) :=
    rankFour_lastPairAlpha_eq_of_lastBinaryAlpha a segment hlast
  have hnot : ¬s.Beli2019Lemma88Exceptional := by
    simpa only [segment, s] using hnotExceptional
  rcases s.beli2019Lemma88_rankTwo_sufficiency hnot with ⟨T⟩
  exact rankFour_lastPairScalingData_of_transform a segment T halpha

/-- A final-pair scaling preserves the isotropy type of the initial
ternary prefix if the defect of its first adjacent product together with
the multiplier defect is strictly larger than `2e`. -/
theorem Beli2019Lemma814LastPairScalingData.firstThreeIsotropic_iff_of_defectSum
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a)
    (hdefectSum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.adjacentDefect (0 : Fin 3) +
          defectOrder (K := K) D.epsilon) :
    a.Lemma814FirstThreeIsotropic ↔
      D.transformed.Lemma814FirstThreeIsotropic := by
  let old := a.prefixValueUnits 3 (by omega)
  let changed := D.transformed.prefixValueUnits 3 (by omega)
  have hzero : changed (0 : Fin 3) = old (0 : Fin 3) := by
    change D.transformed.valueUnit (⟨0, by omega⟩ : Fin 4) =
      a.valueUnit (⟨0, by omega⟩ : Fin 4)
    have hindex : (⟨0, by omega⟩ : Fin 4) = (0 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact D.firstValue_eq
  have hone : changed (1 : Fin 3) = old (1 : Fin 3) := by
    change D.transformed.valueUnit (⟨1, by omega⟩ : Fin 4) =
      a.valueUnit (⟨1, by omega⟩ : Fin 4)
    have hindex : (⟨1, by omega⟩ : Fin 4) = (1 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact D.secondValue_eq
  have htwo : changed (2 : Fin 3) = D.epsilon * old (2 : Fin 3) := by
    change D.transformed.valueUnit (⟨2, by omega⟩ : Fin 4) =
      D.epsilon * a.valueUnit (⟨2, by omega⟩ : Fin 4)
    have hindex : (⟨2, by omega⟩ : Fin 4) = (2 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact D.thirdValue_eq
  have hfirst : -(old (0 : Fin 3) * old (1 : Fin 3)) =
      a.adjacentProduct (0 : Fin 3) := by
    rfl
  have hmultiplierHilbert :
      hilbertSymbol K (-(old (0 : Fin 3) * old (1 : Fin 3)))
        D.epsilon = 1 := by
    rw [hfirst]
    exact hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
      hdefectSum
  have hsecond :
      -(old (1 : Fin 3) * (D.epsilon * old (2 : Fin 3))) =
        D.epsilon * (-(old (1 : Fin 3) * old (2 : Fin 3))) := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  change
    DiagonalIsotropic (diagonalUnitCoefficients old) ↔
      DiagonalIsotropic (diagonalUnitCoefficients changed)
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    hzero, hone, htwo, hsecond, hilbertSymbol_mul_right,
    hmultiplierHilbert, one_mul]

/-- The preliminary strict inequality in case (c), together with
`alpha_2 + alpha_3 = 2e`, supplies the Hilbert-symbol bound used above. -/
theorem Beli2019Lemma814LastPairScalingData.firstThreeIsotropic_iff_of_boundary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)) :
    a.Lemma814FirstThreeIsotropic ↔
      D.transformed.Lemma814FirstThreeIsotropic := by
  apply D.firstThreeIsotropic_iff_of_defectSum
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    exact_mod_cast hsum.symm
  rw [hsumTop, D.epsilon_defect]
  exact (WithTop.add_lt_add_iff_right WithTop.coe_ne_top).mpr
    hfirstAdjacent

/-- If the old raw first-third defect equals `alpha_3`, then over residue
cardinality two a successful final-pair scaling raises that defect strictly,
as prescribed by Lemma 8.1(ii). -/
theorem Beli2019Lemma814LastPairScalingData.firstThreeRawDefect_lt_of_eq
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a)
    (b : GoodBONG r M 1)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1) * D.transformed.prefixProduct 3 * b.prefixProduct 1) := by
  let x : Kˣ := (-1) * a.prefixProduct 3 * b.prefixProduct 1
  have heq : quadraticDefect K D.epsilon = quadraticDefect K x :=
    quadraticDefect_eq_of_defectOrder_eq D.epsilon x
      (D.epsilon_defect.trans hraw.symm)
  have hfinite : quadraticDefect K D.epsilon ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe D.epsilon
      (a.alphaValue (2 : Fin 3)) D.epsilon_defect
  have hstrictRaw := beli2019Lemma81_ii_strict hresidueTwo D.epsilon
    x heq hfinite
  have hstrict := defectOrder_lt_of_quadraticDefect_lt
    D.epsilon (D.epsilon * x) hstrictRaw
  rw [← D.epsilon_defect]
  rw [D.prefixProduct_three_eq]
  have hproduct :
      (-1 : Kˣ) * (D.epsilon * a.prefixProduct 3) * b.prefixProduct 1 =
        D.epsilon * x := by
    dsimp only [x]
    ac_rfl
  rw [hproduct]
  exact hstrict

/-- If the initial ternary segment is exceptional on the equality
boundary, a successful final-pair scaling makes the transformed initial
ternary segment nonexceptional.  Exception (a) is moved to the equality
line while preserving anisotropy; exception (b) is moved strictly above
that line by Lemma 8.1(ii) while preserving isotropy. -/
theorem rankFour_boundary_notExceptional_firstThree_after_scaling
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (D : Beli2019Lemma814LastPairScalingData a)
    (oldSegment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (newSegment : BONG.SegmentWitness D.transformed.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (holdExceptional :
      (oldSegment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    ¬(newSegment.toGoodBONG D.transformed.good).Beli2019Lemma814Exceptional b := by
  let old := oldSegment.toGoodBONG a.good
  let changed := D.transformed
  let new := newSegment.toGoodBONG changed.good
  have holdPrefix := rankFour_boundary_prefixAlphas_eq
    a oldSegment houter hsum
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have hchangedOuter : changed.order (0 : Fin 4) =
      changed.order (2 : Fin 4) := by
    rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
    exact houter
  have hchangedSum : changed.alphaValue (1 : Fin 3) +
      changed.alphaValue (2 : Fin 3) =
        2 * (ramificationIndex K : ℚ) := by
    rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
    exact hsum
  have hnewPrefix := rankFour_boundary_prefixAlphas_eq
    changed newSegment hchangedOuter hchangedSum
  have holdSecond : old.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin 3) := by
    exact holdPrefix.2
  have hnewSecond : new.alphaValue (1 : Fin 2) =
      changed.alphaValue (1 : Fin 3) := by
    exact hnewPrefix.2
  have hisotropy : old.Lemma814FirstThreeIsotropic ↔
      new.Lemma814FirstThreeIsotropic := by
    exact (rankFour_firstThreeIsotropic_iff a oldSegment).trans <|
      (D.firstThreeIsotropic_iff_of_boundary hsum hfirstAdjacent).trans <|
        (rankFour_firstThreeIsotropic_iff changed newSegment).symm
  have hsumTop :
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    exact_mod_cast hsum.symm
  have holdRaw : old.lemma814FirstThirdCappedDefect b =
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    exact rankFour_firstThreeDefect_eq_raw a b oldSegment
  have hnewRaw : new.lemma814FirstThirdCappedDefect b =
      defectOrder (K := K)
        ((-1) * changed.prefixProduct 3 * b.prefixProduct 1) := by
    exact rankFour_firstThreeDefect_eq_raw changed b newSegment
  change old.Beli2019Lemma814Exceptional b at holdExceptional
  change ¬new.Beli2019Lemma814Exceptional b
  rcases holdExceptional with A | B | C
  · have hrawLt : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
      calc
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (2 : Fin 3) : WithTop ℚ) =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
          hsumTop.symm
        _ < (old.alphaValue (1 : Fin 2) : WithTop ℚ) +
              old.lemma814FirstThirdCappedDefect b := A.defectSum_strict
        _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
              defectOrder (K := K)
                ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
          rw [holdSecond, holdRaw]
    have hnewDefect : new.lemma814FirstThirdCappedDefect b =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      D.firstThreeDefect_eq b newSegment hrawLt
    intro E
    rcases E with A' | B' | C'
    · have hboundary :
          (new.alphaValue (1 : Fin 2) : WithTop ℚ) +
              new.lemma814FirstThirdCappedDefect b =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
        rw [hnewSecond, ← halphas (1 : Fin 3), hnewDefect, ← hsumTop]
      have hstrict := A'.defectSum_strict
      exact (not_lt_of_ge hboundary.le) hstrict
    · exact old.not_firstThreeIsotropic_of_anisotropic
        A.firstThree_anisotropic (hisotropy.mpr B'.firstThree_isotropic)
    · exact (by omega : ¬4 ≤ 3) C'.rank_four
  · have holdDefect : old.lemma814FirstThirdCappedDefect b =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
      apply WithTop.add_left_cancel WithTop.coe_ne_top
      calc
        (old.alphaValue (1 : Fin 2) : WithTop ℚ) +
            old.lemma814FirstThirdCappedDefect b =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
          B.defectSum_eq
        _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
              (a.alphaValue (2 : Fin 3) : WithTop ℚ) := hsumTop
        _ = (old.alphaValue (1 : Fin 2) : WithTop ℚ) +
              (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
          rw [holdSecond]
    have holdRawEq : defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      holdRaw.symm.trans holdDefect
    have hnewStrict : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        new.lemma814FirstThirdCappedDefect b := by
      rw [hnewRaw]
      exact D.firstThreeRawDefect_lt_of_eq b B.residueTwo holdRawEq
    have hnewIsotropic : new.Lemma814FirstThreeIsotropic :=
      hisotropy.mp B.firstThree_isotropic
    intro E
    rcases E with A' | B' | C'
    · exact new.not_firstThreeIsotropic_of_anisotropic
        A'.firstThree_anisotropic hnewIsotropic
    · have hnewDefect : new.lemma814FirstThirdCappedDefect b =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
        apply WithTop.add_left_cancel WithTop.coe_ne_top
        calc
          (new.alphaValue (1 : Fin 2) : WithTop ℚ) +
              new.lemma814FirstThirdCappedDefect b =
              ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
            B'.defectSum_eq
          _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
                (a.alphaValue (2 : Fin 3) : WithTop ℚ) := hsumTop
          _ = (new.alphaValue (1 : Fin 2) : WithTop ℚ) +
                (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
            rw [hnewSecond, ← halphas (1 : Fin 3)]
      exact (ne_of_lt hnewStrict) hnewDefect.symm
    · exact (by omega : ¬4 ≤ 3) C'.rank_four
  · exact ((by omega : ¬4 ≤ 3) C.rank_four).elim

/-- The successful-final-pair subcase of the quaternary equality boundary.
If the initial ternary segment is already safe, it is used directly.
Otherwise the final binary Lemma 8.8 transformation makes it safe, and the
rank-three theorem is lifted back into the original rank-four lattice. -/
theorem beli2019Lemma814_rankFour_boundary_of_lastPair_notExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hnotLast :
      let segment := a.toBONG.segmentWitness 2 2 (by omega)
      ¬(segment.toGoodBONG a.good).Beli2019Lemma88Exceptional) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let oldSegment := a.toBONG.segmentWitness
    (prefixPairLocalization (N := 2) (1 : Fin 3)).start
    (prefixPairLocalization (N := 2) (1 : Fin 3)).length
    (prefixPairLocalization (N := 2) (1 : Fin 3)).bound
  let old := oldSegment.toGoodBONG a.good
  have holdPrefix := rankFour_boundary_prefixAlphas_eq
    a oldSegment houter hsum
  by_cases hnotOld : ¬old.Beli2019Lemma814Exceptional b
  · have holdConditions := rankFour_firstThreeConditions_of_prefixAlphas
      a b oldSegment houter holdPrefix conditions hnotOld
    exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b oldSegment horder holdConditions hnotOld
  · have holdExceptional : old.Beli2019Lemma814Exceptional b :=
      Classical.byContradiction hnotOld
    rcases exists_rankFour_boundary_lastPairScaling_of_notExceptional
      a hsum hnotLast with ⟨D⟩
    let changed := D.transformed
    let newSegment := changed.toBONG.segmentWitness
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound
    let new := newSegment.toGoodBONG changed.good
    have hnotNew : ¬new.Beli2019Lemma814Exceptional b := by
      apply rankFour_boundary_notExceptional_firstThree_after_scaling
        a b D oldSegment newSegment houter hsum hfirstAdjacent
      exact holdExceptional
    have horders := a.order_invariant changed
    have halphas := a.alpha_invariant changed
    have hchangedOrder : changed.order (0 : Fin 4) =
        b.order (0 : Fin 1) := by
      rw [← horders (0 : Fin 4)]
      exact horder
    have hchangedOuter : changed.order (0 : Fin 4) =
        changed.order (2 : Fin 4) := by
      rw [← horders (0 : Fin 4), ← horders (2 : Fin 4)]
      exact houter
    have hchangedSum : changed.alphaValue (1 : Fin 3) +
        changed.alphaValue (2 : Fin 3) =
          2 * (ramificationIndex K : ℚ) := by
      rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
      exact hsum
    have hnewPrefix := rankFour_boundary_prefixAlphas_eq
      changed newSegment hchangedOuter hchangedSum
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classificationV)
      (classificationW := classificationW) changed b horder conditions
    have hnewConditions := rankFour_firstThreeConditions_of_prefixAlphas
      changed b newSegment hchangedOuter hnewPrefix hchangedConditions hnotNew
    exact changed.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b newSegment hchangedOrder hnewConditions hnotNew

/-- The raw adjacent defect of the canonical final binary segment is the
raw third adjacent defect of the ambient rank-four BONG. -/
theorem rankFour_lastPairAdjacentDefect_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 2 2 (by omega)) :
    (segment.toGoodBONG a.good).adjacentDefect (0 : Fin 1) =
      a.adjacentDefect (2 : Fin 3) := by
  unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
  change defectOrder (K := K)
      (-(segment.bong.valueUnit 0 * segment.bong.valueUnit 1)) =
    defectOrder (K := K)
      (-(a.toBONG.valueUnit 2 * a.toBONG.valueUnit 3))
  rw [segment.valueUnit_eq, segment.valueUnit_eq]
  congr 3

/-- Numerical information forced by the exceptional alternative of the
final binary segment on the equality boundary.  Since `alpha_3` occurs on
a valuation unit and rank two has no exception (c), only Lemma 8.8(b)
remains. -/
structure Beli2019Lemma814RankFourLastPairExceptionData
    (a : GoodBONG q L 4) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  thirdAlpha_eq_halfGap : a.alphaValue (2 : Fin 3) =
    a.halfGapValue (2 : Fin 3)
  lastAdjacentDefect_eq_secondAlpha :
    a.adjacentDefect (2 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ)

/-- Extract the preceding data from an exceptional final binary segment. -/
theorem rankFour_boundary_lastPairExceptionData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hExceptional :
      let segment := a.toBONG.segmentWitness 2 2 (by omega)
      (segment.toGoodBONG a.good).Beli2019Lemma88Exceptional) :
    Beli2019Lemma814RankFourLastPairExceptionData a := by
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have hlast := rankFour_boundary_lastBinaryAlpha_eq a hsum
  have halpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) :=
    rankFour_lastPairAlpha_eq_of_lastBinaryAlpha a segment hlast
  have hhalfGap : s.halfGapValue (0 : Fin 1) =
      a.halfGapValue (2 : Fin 3) :=
    rankFour_lastPairHalfGap_eq a segment
  have hthirdUnit : IsValuationUnitDefect (K := K)
      (a.alphaValue (2 : Fin 3)) :=
    (a.rankFour_boundaryAlphas_areValuationUnitDefects
      houter hsecondFourth hsum).2.2
  have hlocalThirdUnit : IsValuationUnitDefect (K := K)
      (s.alphaValue (0 : Fin 1)) := by
    rw [halpha]
    exact hthirdUnit
  have hE : s.Beli2019Lemma88Exceptional := by
    simpa only [segment, s] using hExceptional
  rcases hE with ⟨hhalf, hA | hB | hC⟩
  · exact (hA hlocalThirdUnit).elim
  · rcases hB with ⟨B⟩
    have hadjacentLocal :=
      s.adjacentDefect_zero_eq_complementary_of_lemma88ExceptionB B
    have hcomplement : s.lemma88ComplementaryDefect =
        a.alphaValue (1 : Fin 3) := by
      have hboundary := s.halfGap_add_lemma88ComplementaryDefect
      rw [← hhalf, halpha] at hboundary
      linarith
    have hadjacent : a.adjacentDefect (2 : Fin 3) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      rw [← rankFour_lastPairAdjacentDefect_eq a segment,
        hadjacentLocal]
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hcomplement
    exact {
      residueTwo := B.residueTwo
      thirdAlpha_eq_halfGap := by
        rw [← hhalfGap, ← halpha]
        exact hhalf
      lastAdjacentDefect_eq_secondAlpha := hadjacent
    }
  · rcases hC with ⟨C⟩
    exact ((by omega : ¬3 ≤ 2) C.rank_three).elim

/-- The preliminary strict first-adjacent inequality and the final-pair
exception force the raw quaternary determinant defect to be `alpha_2`.
Since the fourth prefix is terminal in rank four, the capped defect has the
same value. -/
theorem rankFour_firstFourDefect_eq_secondAlpha_of_lastPairException
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4)
    (D : Beli2019Lemma814RankFourLastPairExceptionData a)
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)) :
    a.lemma814FirstFourCappedDefect (by omega) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
  have hproduct : a.prefixProduct 4 =
      a.adjacentProduct (0 : Fin 3) *
        a.adjacentProduct (2 : Fin 3) := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 3 (by omega),
      a.toBONG.prefixProduct_succ 2 (by omega),
      a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega)]
    simp only [BONG.prefixProduct_zero, one_mul]
    unfold adjacentProduct GoodBONG.valueUnit
    have hzero : (⟨0, by omega⟩ : Fin 4) =
        Fin.castSucc (0 : Fin 3) := by
      apply Fin.ext
      rfl
    have hone : (⟨1, by omega⟩ : Fin 4) =
        Fin.succ (0 : Fin 3) := by
      apply Fin.ext
      rfl
    have htwo : (⟨2, by omega⟩ : Fin 4) =
        Fin.castSucc (2 : Fin 3) := by
      apply Fin.ext
      rfl
    have hthree : (⟨3, by omega⟩ : Fin 4) =
        Fin.succ (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hzero, hone, htwo, hthree]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg]
    ring
  have hstrict : defectOrder (K := K)
        (a.adjacentProduct (2 : Fin 3)) <
      defectOrder (K := K) (a.adjacentProduct (0 : Fin 3)) := by
    change a.adjacentDefect (2 : Fin 3) <
      a.adjacentDefect (0 : Fin 3)
    rw [D.lastAdjacentDefect_eq_secondAlpha]
    exact hfirstAdjacent
  have hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    rw [hproduct,
      defectOrder_mul_eq_right_of_lt_left (K := K) hstrict]
    exact D.lastAdjacentDefect_eq_secondAlpha
  have hmin := a.lemma814FirstFourCappedDefect_eq_min (by omega)
  have hcap : a.prefixAlphaCap 4 = ⊤ := a.prefixAlphaCap_last
  rw [hcap, min_top_right, hraw] at hmin
  exact hmin

/-- On the equality boundary, attainment of the third half-gap identifies
`alpha_2` with the complementary defect at the third gap. -/
theorem rankFour_secondAlpha_eq_complement_of_boundary
    (a : GoodBONG q L 4)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hthird : a.alphaValue (2 : Fin 3) =
      a.halfGapValue (2 : Fin 3)) :
    a.alphaValue (1 : Fin 3) =
      a.lemma814ThirdComplementaryDefect (by omega) := by
  have hcomplement :=
    a.lemma814ThirdComplementaryDefect_add_halfGap (by omega)
  change a.lemma814ThirdComplementaryDefect (by omega) +
      a.halfGapValue (2 : Fin 3) =
    2 * (ramificationIndex K : ℚ) at hcomplement
  rw [← hthird] at hcomplement
  linarith

/-- If the initial ternary segment is exceptional on the equality
boundary, the ambient capped first-third defect equals `alpha_3`. -/
theorem rankFour_boundary_firstThirdDefect_eq_thirdAlpha_of_firstThreeExceptional
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (E : (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    a.lemma814FirstThirdCappedDefect b =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  let s := segment.toGoodBONG a.good
  have halphas := rankFour_boundary_prefixAlphas_eq a segment houter hsum
  have hraw : s.lemma814FirstThirdCappedDefect b =
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    exact rankFour_firstThreeDefect_eq_raw a b segment
  have hdefect : a.lemma814FirstThirdCappedDefect b =
      min (defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1))
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
      b.prefixAlphaCap_last]
    have hindex : (⟨3 - 1, by omega⟩ : Fin 3) = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hindex]
    simp
  have hsumTop :
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    exact_mod_cast hsum.symm
  change s.Beli2019Lemma814Exceptional b at E
  rcases E with A | B | C
  · have hlocalGt : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        s.lemma814FirstThirdCappedDefect b := by
      apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
      calc
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (2 : Fin 3) : WithTop ℚ) =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
          hsumTop.symm
        _ < (s.alphaValue (1 : Fin 2) : WithTop ℚ) +
              s.lemma814FirstThirdCappedDefect b :=
          A.defectSum_strict
        _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
              s.lemma814FirstThirdCappedDefect b := by
          rw [halphas.2]
    have hrawGt : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [← hraw]
      exact hlocalGt
    rw [hdefect, min_eq_right hrawGt.le]
  · have hlocalEq : s.lemma814FirstThirdCappedDefect b =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
      apply WithTop.add_left_cancel WithTop.coe_ne_top
      calc
        (s.alphaValue (1 : Fin 2) : WithTop ℚ) +
            s.lemma814FirstThirdCappedDefect b =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
          B.defectSum_eq
        _ = (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
              (a.alphaValue (2 : Fin 3) : WithTop ℚ) := hsumTop
        _ = (s.alphaValue (1 : Fin 2) : WithTop ℚ) +
              (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by rw [halphas.2]
    have hrawEq : defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      hraw.symm.trans hlocalEq
    rw [hdefect, hrawEq, min_self]
  · exact ((by omega : ¬4 ≤ 3) C.rank_four).elim

/-- If both binary ends are exceptional on the equality boundary, then the
ternary complement of the prescribed line in the quaternary prefix is
anisotropic.  The two local ternary exceptions give the two possible Hasse
factors: one in case (a), and minus one in the residue-two case (b). -/
theorem rankFour_boundary_firstFourComplementAnisotropic_of_firstThreeExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (D : Beli2019Lemma814RankFourLastPairExceptionData a)
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (E : (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    a.Lemma814FirstFourComplementAnisotropic b (by omega) := by
  let s := segment.toGoodBONG a.good
  let head := a.prefixValueUnits 3 (by omega)
  let last := a.valueUnit (3 : Fin 4)
  rcases a.lemma814FirstFourUnitComplement_of_quaternaryLaws b (by omega) with
    ⟨complement, hcomplementRaw⟩
  have hprefix : a.prefixValueUnits 4 (by omega) =
      Fin.snoc head last := by
    dsimp only [head, last]
    convert a.prefixValueUnits_succ_eq_snoc 3 (by omega) using 1
    congr 1
  have hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) complement))
      (diagonalUnitCoefficients (Fin.snoc head last)) := by
    rw [← hprefix]
    exact hcomplementRaw
  have hheadDet : diagonalUnitDeterminant head = a.prefixProduct 3 := by
    simpa only [head] using
      a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)
  have hfullDet : diagonalUnitDeterminant (Fin.snoc head last) =
      a.prefixProduct 4 := by
    rw [← hprefix]
    exact a.diagonalUnitDeterminant_prefixValueUnits 4 (by omega)
  have hbProduct : b.prefixProduct 1 = b.valueUnit (0 : Fin 1) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    have h := b.toBONG.prefixProduct_succ 0 (by omega)
    rw [b.toBONG.prefixProduct_zero, one_mul] at h
    convert h using 1
    apply congrArg b.toBONG.valueUnit
    apply Fin.ext
    rfl
  have hfirstRaw : s.lemma814FirstThirdCappedDefect b =
      defectOrder (K := K)
        (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1))) := by
    calc
      _ = defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
        exact rankFour_firstThreeDefect_eq_raw a b segment
      _ = _ := by
        rw [hheadDet, ← hbProduct]
        congr 1
        simp
  have hfourRaw : defectOrder (K := K)
        (diagonalUnitDeterminant (Fin.snoc head last)) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    have hcapped :=
      rankFour_firstFourDefect_eq_secondAlpha_of_lastPairException
        a D hfirstAdjacent
    have hmin := a.lemma814FirstFourCappedDefect_eq_min (by omega)
    rw [a.prefixAlphaCap_last, min_top_right] at hmin
    rw [hfullDet]
    exact hmin.symm.trans hcapped
  have halphas := rankFour_boundary_prefixAlphas_eq a segment houter hsum
  change s.Beli2019Lemma814Exceptional b at E
  rcases E with A | B | C
  · have hfactorSumQ :
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
          defectOrder (K := K)
              (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1))) +
            defectOrder (K := K)
              (diagonalUnitDeterminant (Fin.snoc head last)) := by
      calc
        _ < (s.alphaValue (1 : Fin 2) : WithTop ℚ) +
              s.lemma814FirstThirdCappedDefect b := A.defectSum_strict
        _ = _ := by rw [halphas.2, hfirstRaw, ← hfourRaw, add_comm]
    have hfactorSum :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          defectOrder (K := K)
              (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1))) +
            defectOrder (K := K)
              (diagonalUnitDeterminant (Fin.snoc head last)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfactorSumQ
    have hfactor : hilbertSymbol K
        (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1)))
        (diagonalUnitDeterminant (Fin.snoc head last)) = 1 :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hfactorSum
    have hhead :
        DiagonalAnisotropic (diagonalUnitCoefficients head) := by
      have hambient : a.Lemma814FirstThreeAnisotropic := by
        apply (a.not_firstThreeIsotropic_iff_anisotropic).mp
        intro hisotropic
        have hlocal := (rankFour_firstThreeIsotropic_iff a segment).mpr
          hisotropic
        exact s.not_firstThreeIsotropic_of_anisotropic
          A.firstThree_anisotropic hlocal
      simpa only [DiagonalAnisotropic, head,
        diagonalUnitCoefficients_prefixValueUnits,
        Lemma814FirstThreeAnisotropic, lemma814FirstThreeValues] using hambient
    have hanisotropic := diagonalTernaryComplement_anisotropic_of_factor_one
      head last (b.valueUnit (0 : Fin 1)) complement hcomplement hfactor hhead
    exact a.lemma814FirstFourComplementAnisotropic_of_unit
      b (by omega) complement hcomplementRaw hanisotropic
  · have hfactorSumQ :
        defectOrder (K := K)
              (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1))) +
            defectOrder (K := K)
              (diagonalUnitDeterminant (Fin.snoc head last)) =
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
      calc
        _ = (s.alphaValue (1 : Fin 2) : WithTop ℚ) +
              s.lemma814FirstThirdCappedDefect b := by
          rw [halphas.2, hfirstRaw, ← hfourRaw, add_comm]
        _ = _ := B.defectSum_eq
    have hfactorSum :
        defectOrder (K := K)
              (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1))) +
            defectOrder (K := K)
              (diagonalUnitDeterminant (Fin.snoc head last)) =
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfactorSumQ
    have hfactorNe : hilbertSymbol K
        (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1)))
        (diagonalUnitDeterminant (Fin.snoc head last)) ≠ 1 :=
      hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
        D.residueTwo _ _ hfactorSum
    have hfactor : hilbertSymbol K
        (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1)))
        (diagonalUnitDeterminant (Fin.snoc head last)) = -1 := by
      rcases Int.units_eq_one_or (hilbertSymbol K
          (-(diagonalUnitDeterminant head * b.valueUnit (0 : Fin 1)))
          (diagonalUnitDeterminant (Fin.snoc head last))) with hone | hneg
      · exact (hfactorNe hone).elim
      · exact hneg
    have hhead : DiagonalIsotropic (diagonalUnitCoefficients head) := by
      have hambient : a.Lemma814FirstThreeIsotropic :=
        (rankFour_firstThreeIsotropic_iff a segment).mp
          B.firstThree_isotropic
      simpa only [DiagonalIsotropic, head,
        diagonalUnitCoefficients_prefixValueUnits,
        Lemma814FirstThreeIsotropic, lemma814FirstThreeValues] using hambient
    have hanisotropic :=
      diagonalTernaryComplement_anisotropic_of_factor_neg_one
        head last (b.valueUnit (0 : Fin 1)) complement hcomplement hfactor hhead
    exact a.lemma814FirstFourComplementAnisotropic_of_unit
      b (by omega) complement hcomplementRaw hanisotropic
  · exact ((by omega : ¬4 ≤ 3) C.rank_four).elim

/-- The numerical data of the exceptional final pair, together with an
exceptional initial ternary segment, assemble exactly exception (c) of
Lemma 8.14 in rank four. -/
theorem rankFour_boundary_exceptionC_of_lastPairExceptionData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (D : Beli2019Lemma814RankFourLastPairExceptionData a)
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (E : (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    a.Beli2019Lemma814ExceptionC b := by
  let hfour : 4 ≤ 4 := by omega
  refine {
    rank_four := hfour
    firstThirdOrders_eq := houter
    residueTwo := D.residueTwo
    secondFourthOrders_lt := hsecondFourth
    firstThirdDefect_eq_alpha := ?_
    thirdAlpha_eq_halfGap := D.thirdAlpha_eq_halfGap
    firstFourDefect_eq_secondAlpha := ?_
    secondAlpha_eq_complement := ?_
    firstFourComplement_anisotropic := ?_
    laterAlpha_strict := ?_ }
  · have h :=
      rankFour_boundary_firstThirdDefect_eq_thirdAlpha_of_firstThreeExceptional
        a b segment houter hsum E
    convert h using 1
    congr 1
  · simpa only using
      rankFour_firstFourDefect_eq_secondAlpha_of_lastPairException
        a D hfirstAdjacent
  · simpa only using
      rankFour_secondAlpha_eq_complement_of_boundary
        a hsum D.thirdAlpha_eq_halfGap
  · simpa only using
      rankFour_boundary_firstFourComplementAnisotropic_of_firstThreeExceptional
        a b segment houter hsum D hfirstAdjacent E
  · intro hfive
    exact ((by omega : ¬5 ≤ 4) hfive).elim

/-- Literal version of the preceding assembly theorem: exceptionality of the
canonical final binary segment supplies all of its required numerical data. -/
theorem rankFour_boundary_exceptionC_of_lastPairExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG
      (prefixPairLocalization (N := 2) (1 : Fin 3)).start
      (prefixPairLocalization (N := 2) (1 : Fin 3)).length
      (prefixPairLocalization (N := 2) (1 : Fin 3)).bound)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hLastExceptional :
      let lastSegment := a.toBONG.segmentWitness 2 2 (by omega)
      (lastSegment.toGoodBONG a.good).Beli2019Lemma88Exceptional)
    (E : (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    a.Beli2019Lemma814ExceptionC b := by
  have D := rankFour_boundary_lastPairExceptionData
    a houter hsecondFourth hsum hLastExceptional
  exact rankFour_boundary_exceptionC_of_lastPairExceptionData
    a b segment houter hsecondFourth hsum D hfirstAdjacent E

/-- The exceptional-final-pair subcase of the normalized quaternary boundary.
If the initial ternary segment is safe, the rank-three theorem applies.  If
it is exceptional, the preceding theorem produces the globally excluded
exception (c). -/
theorem beli2019Lemma814_rankFour_boundary_of_lastPairExceptional
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3))
    (hLastExceptional :
      let lastSegment := a.toBONG.segmentWitness 2 2 (by omega)
      (lastSegment.toGoodBONG a.good).Beli2019Lemma88Exceptional) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let segment := a.toBONG.segmentWitness
    (prefixPairLocalization (N := 2) (1 : Fin 3)).start
    (prefixPairLocalization (N := 2) (1 : Fin 3)).length
    (prefixPairLocalization (N := 2) (1 : Fin 3)).bound
  have halphas := rankFour_boundary_prefixAlphas_eq
    a segment houter hsum
  by_cases hnotLocal :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b
  · have hlocalConditions := rankFour_firstThreeConditions_of_prefixAlphas
      a b segment houter halphas conditions hnotLocal
    exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b segment horder hlocalConditions hnotLocal
  · have hlocalExceptional :
        (segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b :=
      Classical.byContradiction hnotLocal
    have C := rankFour_boundary_exceptionC_of_lastPairExceptional
      a b segment houter hsecondFourth hsum hfirstAdjacent
        hLastExceptional hlocalExceptional
    exact (hnotExceptional (Or.inr (Or.inr C))).elim

/-- Completion of the quaternary equality boundary after the paper's
preliminary normalization `alpha_2 < d(-a_1a_2)`. -/
theorem beli2019Lemma814_rankFour_boundary_of_firstAdjacent
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a original : GoodBONG q L 4) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) =
      2 * (ramificationIndex K : ℚ))
    (hfirstAdjacent : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (0 : Fin 3)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  let lastSegment := a.toBONG.segmentWitness 2 2 (by omega)
  by_cases hLastExceptional :
      (lastSegment.toGoodBONG a.good).Beli2019Lemma88Exceptional
  · apply beli2019Lemma814_rankFour_boundary_of_lastPairExceptional
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b horder conditions hnotExceptional houter hsecondFourth
        hsum hfirstAdjacent
    simpa only [lastSegment] using hLastExceptional
  · apply beli2019Lemma814_rankFour_boundary_of_lastPair_notExceptional
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      a original b horder conditions houter hsum hfirstAdjacent
    simpa only [lastSegment] using hLastExceptional

end BONG.GoodBONG

end Bong
