/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma93CaseTwo

/-!
# Beli (2019), Lemma 9.3 in rank three

In rank three the tail has rank two and hence only one comparison boundary.
Moreover the target prefix of length three is the full determinant, so the
extra `alpha_3` cap occurring from rank four onward is absent.  This gives a
short low-rank form of the two cases in the proof of Lemma 9.3.
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

private theorem representationIndex_eq_of_val_eq_rankThreeLemma93
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- In rank three, deleting equal heads removes the only nontrivial cap from
the first-three comparison defect. -/
theorem firstThirdDefect_eq_min_tail_betaOne_rankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hhead : a.value 0 = b.value 0) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      min (a.tail.truncatedPrefixDefect b.tail (-1) 2 0)
        (b.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  have hraw := a.defectOrder_shiftedPrefixes_eq_tail b hhead (-1) 2 0
    (by omega) (by omega)
  have hzero : (⟨1 - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  unfold truncatedPrefixDefect
  rw [hraw, a.prefixAlphaCap_last, a.tail.prefixAlphaCap_last,
    b.prefixAlphaCap_of_internal (by omega) (by omega),
    b.tail.prefixAlphaCap_zero, hzero]
  simp only [min_top_left, min_top_right]

/-- The strict Case-1 alternative makes the first-three capped defect equal
to the defect of the two projected tails. -/
theorem firstThirdDefect_eq_tail_of_lt_betaOne_rankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hhead : a.value 0 = b.value 0)
    (hlt : a.truncatedPrefixDefect b (-1) 3 1 <
      (b.alphaValue (0 : Fin 2) : WithTop ℚ)) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      a.tail.truncatedPrefixDefect b.tail (-1) 2 0 := by
  rw [a.firstThirdDefect_eq_min_tail_betaOne_rankThree b hhead] at hlt ⊢
  apply min_eq_left
  apply le_of_not_gt
  intro h
  rw [min_eq_right h.le] at hlt
  exact (lt_irrefl _ hlt)

/-- If the uncapped first-three defect is exactly the source first alpha,
then both the original capped defect and the projected-tail defect have that
same value. -/
theorem firstThirdDefect_eq_tail_of_raw_eq_betaOne_rankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hhead : a.value 0 = b.value 0)
    (hraw : defectOrder (K := K)
      ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
        (b.alphaValue (0 : Fin 2) : WithTop ℚ)) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      a.tail.truncatedPrefixDefect b.tail (-1) 2 0 := by
  have hshift := a.defectOrder_shiftedPrefixes_eq_tail b hhead (-1) 2 0
    (by omega) (by omega)
  have htail : a.tail.truncatedPrefixDefect b.tail (-1) 2 0 =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    unfold truncatedPrefixDefect
    rw [a.tail.prefixAlphaCap_last, b.tail.prefixAlphaCap_zero]
    simp only [min_top_right]
    rw [← hshift]
    simpa only [Nat.reduceAdd] using hraw
  rw [a.firstThirdDefect_eq_min_tail_betaOne_rankThree b hhead, htail]
  exact min_self _

/-- Equality at the unique rank-two tail boundary, packaged in the form
required by `Lemma93Input`. -/
theorem essentialAlpha_eq_rankThree_of_firstThirdDefect_eq_tail
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hhead : a.value 0 = b.value 0)
    (hdefect : a.truncatedPrefixDefect b (-1) 3 1 =
      a.tail.truncatedPrefixDefect b.tail (-1) 2 0) :
    ∀ i : RepresentationIndex 2 2,
      (a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i) →
      a.tail.representationAlpha b.tail i =
        a.representationAlpha b i.tailShift := by
  intro i _
  have hi : i = firstRepresentationIndex 0 1 := by
    apply representationIndex_eq_of_val_eq_rankThreeLemma93
    change i.val = 1
    have := i.pos
    have := i.lt_large
    omega
  subst i
  have hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3) := by
    unfold GoodBONG.order
    rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact hhead)
  exact representationAlpha_tail_first_eq_originalSecond_of_defect_eq
    a b hfirst hdefect

/-- The data common to both low-rank cases after Lemma 9.1 has matched the
two heads. -/
structure Beli2019Lemma93MatchedPairRankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M 3) where
  targetBONG : GoodBONG q L 3
  selectedConditions :
    RepresentationConditions targetBONG c (Nat.le_refl 2)
  headValue_eq : targetBONG.value 0 = c.value 0
  secondOrder_le : targetBONG.order (1 : Fin 3) ≤ c.order (1 : Fin 3)

/-- A matched ternary pair becomes the literal Lemma-9.3 recursive input as
soon as the equality at its unique tail boundary is known. -/
noncomputable def Beli2019Lemma93MatchedPairRankThree.toLemma93Input
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 2))
    (c : GoodBONG r M 3)
    (P : Beli2019Lemma93MatchedPairRankThree a c)
    (halpha : ∀ i : RepresentationIndex 2 2,
      (P.targetBONG.tail.IsCurrentEssential c.tail i ∨
        P.targetBONG.tail.IsNextEssential c.tail i) →
      P.targetBONG.tail.representationAlpha c.tail i =
        P.targetBONG.representationAlpha c i.tailShift) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl 2)
        ambient conditions) where
  tailIndex := 1
  targetIndex_eq := rfl
  sourceIndex_eq := rfl
  targetBONG := P.targetBONG
  sourceBONG := c
  selectedConditions := P.selectedConditions
  headValue_eq := P.headValue_eq
  secondOrder_le := P.secondOrder_le
  essentialAlpha_eq := halpha

/-- Lemma 9.1 constructs the common matched-head package after an arbitrary
change of the source good BONG. -/
theorem exists_beli2019Lemma93MatchedPair_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L 3) (b c : GoodBONG r M 3)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (ambient : q.Represents r)
    (_rootConditions : RepresentationConditions a b (Nat.le_refl 2))
    (selectedConditions : RepresentationConditions a c (Nat.le_refl 2))
    (hlemma91 : a.Lemma91Alternative c) :
    Nonempty (Beli2019Lemma93MatchedPairRankThree a c) := by
  rcases a.beli2019Lemma91_sameRank
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity)
      (targetLocalization := targetLocalization)
      (targetConstruction := targetConstruction)
      (targetSectionTwo := targetSectionTwo)
      (targetBinaryScaling := targetBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW)
      (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
      (deepWW := deepWW)
      c hfirst ambient selectedConditions hlemma91 with ⟨D⟩
  have transformedConditions : RepresentationConditions D.transformed c
      (Nat.le_refl 2) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      D.transformed c c (Nat.le_refl 2)).mp selectedConditions
  have hheadUnit : D.transformed.valueUnit (0 : Fin 3) =
      c.valueUnit (0 : Fin 3) :=
    D.firstValue_eq.trans c.firstUnarySegment_valueUnit_zero
  have hhead : D.transformed.value 0 = c.value 0 := by
    simpa only [coe_valueUnit] using congrArg Units.val hheadUnit
  have hfirst' : D.transformed.order (0 : Fin 3) =
      c.order (0 : Fin 3) := by
    unfold GoodBONG.order
    rw [D.transformed.toBONG.order_eq_ordUnit, c.toBONG.order_eq_ordUnit]
    simpa only [GoodBONG.valueUnit] using congrArg (ordUnit K) hheadUnit
  exact ⟨{
    targetBONG := D.transformed
    selectedConditions := transformedConditions
    headValue_eq := hhead
    secondOrder_le := D.transformed.secondOrder_le_of_firstOrder_eq c
      transformedConditions.orderCondition hfirst'
  }⟩

/-- Changing the target ternary good BONG does not change the uncapped
first-three comparison defect: its complete value product changes by a
square. -/
theorem firstThirdRawDefect_changeTarget_rankThree
    (a c : GoodBONG q L 3) (b : GoodBONG r M 3) :
    defectOrder (K := K) ((-1) * c.prefixProduct 3 * b.prefixProduct 1) =
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
  rcases BONG.exists_valueProduct_eq_mul_square a.toBONG c.toBONG with ⟨s, hs⟩
  have ha : a.prefixProduct 3 = a.toBONG.valueProduct :=
    a.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl
  have hc : c.prefixProduct 3 = c.toBONG.valueProduct :=
    c.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl
  have hproduct : (-1 : Kˣ) * c.prefixProduct 3 * b.prefixProduct 1 =
      ((-1) * a.prefixProduct 3 * b.prefixProduct 1) * s ^ 2 := by
    rw [ha, hc, hs]
    ac_rfl
  rw [hproduct, defectOrder_mul_square]

/-- The rank-three Case 2 condition.  The final `β₁ < α₃` clause from
the general statement is absent because the target prefix of length three is
the whole ternary determinant. -/
noncomputable def Beli2019Lemma93CaseTwoConditionRankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3) : Prop :=
  a.truncatedPrefixDefect b (-1) 3 1 =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ) ∧
  a.truncatedPrefixDefect b (-1) 3 1 <
    ((((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)

/-- In the ternary Case 2 branch the source first alpha lies strictly below
its half-gap, exactly as in the unrestricted proof of Lemma 9.3. -/
theorem sourceFirstAlpha_lt_halfGap_of_caseTwo_rankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (hcase : a.Beli2019Lemma93CaseTwoConditionRankThree b) :
    b.alphaValue (0 : Fin 2) < b.halfGapValue (0 : Fin 2) := by
  unfold Beli2019Lemma93CaseTwoConditionRankThree at hcase
  have hlow :
      (b.alphaValue (0 : Fin 2) : WithTop ℚ) <
        ((((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
    hcase.1 ▸ hcase.2
  have houter := a.order_zero_le_two
  have hlowQ : b.alphaValue (0 : Fin 2) <
      ((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) :=
    WithTop.coe_lt_coe.mp hlow
  unfold halfGapValue orderGap
  have houterQ : (a.order (0 : Fin 3) : ℚ) ≤
      (a.order (2 : Fin 3) : ℚ) := by
    exact_mod_cast houter
  have hzeroSucc : (0 : Fin 2).succ = (1 : Fin 3) := by
    apply Fin.ext
    simp
  have hzeroCast : (0 : Fin 2).castSucc = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [hzeroSucc, hzeroCast]
  push_cast at hlowQ ⊢
  rw [← hfirst]
  linarith

/-- A first-value transform multiplies the first ternary prefix product by
its chosen unit. -/
theorem Beli2019FirstValueTransform.prefixProduct_one_eq_rankThree
    {b : GoodBONG r M 3} (T : b.Beli2019FirstValueTransform) :
    T.transformed.prefixProduct 1 = T.epsilon * b.prefixProduct 1 := by
  unfold GoodBONG.prefixProduct
  rw [T.transformed.toBONG.prefixProduct_succ 0 (by omega),
    b.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  exact T.firstValue_eq

/-- The source choice used in the ternary Case 2 branch. -/
structure Beli2019Lemma93CaseTwoSourceHeadNormalizationRankThree
    (a : GoodBONG q L 3) (b : GoodBONG r M 3) where
  transformed : GoodBONG r M 3
  firstThirdRawDefect_eq :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * transformed.prefixProduct 1) =
      (b.alphaValue (0 : Fin 2) : WithTop ℚ)

/-- Lemma 8.8 provides the exact source-head normalization needed in the
ternary Case 2 branch. -/
theorem exists_caseTwoSourceHeadNormalization_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (hcase : a.Beli2019Lemma93CaseTwoConditionRankThree b) :
    Nonempty
      (Beli2019Lemma93CaseTwoSourceHeadNormalizationRankThree a b) := by
  let raw := defectOrder (K := K)
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
  have hrawLe : (b.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ raw := by
    have hle := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    exact hcase.1 ▸ hle
  by_cases hrawEq : raw = (b.alphaValue (0 : Fin 2) : WithTop ℚ)
  · exact ⟨{
      transformed := b
      firstThirdRawDefect_eq := hrawEq
    }⟩
  · have hstrictAlpha :=
      a.sourceFirstAlpha_lt_halfGap_of_caseTwo_rankThree b hfirst hcase
    have hnotExceptional : ¬b.Beli2019Lemma88Exceptional := by
      rintro ⟨hhalf, _⟩
      exact (ne_of_lt hstrictAlpha) hhalf
    rcases (b.beli2019Lemma88_i).mpr hnotExceptional with ⟨T⟩
    have hstrict : (b.alphaValue (0 : Fin 2) : WithTop ℚ) < raw :=
      lt_of_le_of_ne hrawLe (fun h => hrawEq h.symm)
    have hproduct :
        (-1 : Kˣ) * a.prefixProduct 3 * T.transformed.prefixProduct 1 =
          T.epsilon * ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [T.prefixProduct_one_eq_rankThree]
      ac_rfl
    refine ⟨{
      transformed := T.transformed
      firstThirdRawDefect_eq := ?_
    }⟩
    rw [hproduct,
      defectOrder_mul_eq_left_of_lt_right (K := K)
        (T.epsilon_defect ▸ hstrict), T.epsilon_defect]

/-- Lemma 9.1's alternative is invariant under changing the source ternary
good BONG.  The rank-three statement is separate because the general helper
is indexed from rank four. -/
theorem lemma91Alternative_changeSource_iff_rankThree
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L 3) (b c : GoodBONG r M 3) :
    a.Lemma91Alternative b ↔ a.Lemma91Alternative c := by
  have horders : b.SameOrders c := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant c
  have halphas : b.SameAlphas c := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant c
  have hdefect := a.truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a b c (-1) 3 1
  unfold Lemma91Alternative
  rw [horders (1 : Fin 3), halphas (0 : Fin 2), hdefect]

/-- The large-defect alternative gives equality at the unique ternary tail
boundary by combining the paper's reverse inequality with the universal
tail monotonicity inequality. -/
theorem essentialAlpha_eq_rankThree_of_largeDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hhead : a.value 0 = b.value 0)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (hdefect :
      ((((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) 3 1) :
    ∀ i : RepresentationIndex 2 2,
      (a.tail.IsCurrentEssential b.tail i ∨
        a.tail.IsNextEssential b.tail i) →
      a.tail.representationAlpha b.tail i =
        a.representationAlpha b i.tailShift := by
  intro i _
  have hi : i = firstRepresentationIndex 0 1 := by
    apply representationIndex_eq_of_val_eq_rankThreeLemma93
    change i.val = 1
    have := i.pos
    have := i.lt_large
    omega
  subst i
  apply a.representationAlpha_tail_eq_shift_of_tail_le_shift b hhead
  exact representationAlpha_tail_first_le_originalSecond_of_largeDefect
    a b hfirst hdefect

/-- Complete rank-three form of Beli (2019), Lemma 9.3.  The proof follows
the paper's three numerical alternatives, with the final alpha cap omitted
at the full ternary determinant. -/
theorem exists_beli2019Lemma93Input_rankThree
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 3)
    (hfirst : a.order (0 : Fin 3) = b.order (0 : Fin 3))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 2))
    (hlemma91 : a.Lemma91Alternative b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl 2)
        ambient conditions)) := by
  let d := a.truncatedPrefixDefect b (-1) 3 1
  let beta : WithTop ℚ := (b.alphaValue (0 : Fin 2) : WithTop ℚ)
  let threshold : WithTop ℚ :=
    ((((b.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hdBeta : d ≤ beta := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hzero : (⟨1 - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext
      rfl
    rw [hzero] at hcap
    exact hcap
  by_cases hstrict : d < beta
  · rcases a.exists_beli2019Lemma93MatchedPair_rankThree
        (targetLaws := targetLaws) (sourceLaws := sourceLaws)
        (targetParity := targetParity)
        (targetLocalization := targetLocalization)
        (targetConstruction := targetConstruction)
        (targetSectionTwo := targetSectionTwo)
        (classificationV := classificationV)
        (targetBinaryScaling := targetBinaryScaling)
        (targetQuaternaryScaling := targetQuaternaryScaling)
        (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
        (structuralV := structuralV) (structuralW := structuralW)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveW := sectionFiveW)
        (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
        (deepWW := deepWW)
        b b hfirst ambient conditions conditions hlemma91 with ⟨P⟩
    have hdefectInvariant := a.truncatedPrefixDefect_invariant
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      P.targetBONG b b (-1) 3 1
    have hstrictSelected :
        P.targetBONG.truncatedPrefixDefect b (-1) 3 1 <
          (b.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      rw [← hdefectInvariant]
      exact hstrict
    have hdefect :=
      P.targetBONG.firstThirdDefect_eq_tail_of_lt_betaOne_rankThree
        b P.headValue_eq hstrictSelected
    have halpha := by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact P.targetBONG.essentialAlpha_eq_rankThree_of_firstThirdDefect_eq_tail
        b P.headValue_eq hdefect
    exact ⟨P.toLemma93Input a b ambient conditions b halpha⟩
  · have hdbeta : d = beta :=
      le_antisymm hdBeta (le_of_not_gt hstrict)
    by_cases hlarge : threshold ≤ d
    · rcases a.exists_beli2019Lemma93MatchedPair_rankThree
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (targetParity := targetParity)
          (targetLocalization := targetLocalization)
          (targetConstruction := targetConstruction)
          (targetSectionTwo := targetSectionTwo)
          (classificationV := classificationV)
          (targetBinaryScaling := targetBinaryScaling)
          (targetQuaternaryScaling := targetQuaternaryScaling)
          (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
          (structuralV := structuralV) (structuralW := structuralW)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
          (sectionFiveW := sectionFiveW)
          (sectionFourW := sectionFourW)
          (sectionFourV := sectionFourV)
          (deepWW := deepWW)
          b b hfirst ambient conditions conditions hlemma91 with ⟨P⟩
      have htargetOrders : a.SameOrders P.targetBONG := by
        letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
        exact a.order_invariant P.targetBONG
      have hfirstSelected : P.targetBONG.order (0 : Fin 3) =
          b.order (0 : Fin 3) :=
        (htargetOrders (0 : Fin 3)).symm.trans hfirst
      have hdefectInvariant := a.truncatedPrefixDefect_invariant
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        P.targetBONG b b (-1) 3 1
      have hlargeSelected :
          ((((b.order (1 : Fin 3) -
              P.targetBONG.order (2 : Fin 3) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
          P.targetBONG.truncatedPrefixDefect b (-1) 3 1 := by
        rw [← htargetOrders (2 : Fin 3), ← hdefectInvariant]
        exact hlarge
      have halpha := by
        letI : Beli2006AlphaLaws.{u, v} K := targetLaws
        exact P.targetBONG.essentialAlpha_eq_rankThree_of_largeDefect
          b P.headValue_eq hfirstSelected hlargeSelected
      exact ⟨P.toLemma93Input a b ambient conditions b halpha⟩
    · have hcase : a.Beli2019Lemma93CaseTwoConditionRankThree b := by
        exact ⟨hdbeta, lt_of_not_ge hlarge⟩
      rcases a.exists_caseTwoSourceHeadNormalization_rankThree
          (sourceLaws := sourceLaws) (sourceParity := sourceParity)
          (sourceLocalization := sourceLocalization)
          (sourceConstruction := sourceConstruction)
          (sourceSectionTwo := sourceSectionTwo)
          (classificationW := classificationW)
          (sourceBinaryScaling := sourceBinaryScaling)
          (sourceQuaternaryScaling := sourceQuaternaryScaling)
          (sourceLemma49 := sourceLemma49) (sourceLemma47 := sourceLemma47)
          b hfirst hcase with ⟨H⟩
      have hsourceOrders : b.SameOrders H.transformed := by
        letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
        exact b.order_invariant H.transformed
      have hsourceAlphas : b.SameAlphas H.transformed := by
        letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
        exact b.alpha_invariant H.transformed
      have hfirstSelected : a.order (0 : Fin 3) =
          H.transformed.order (0 : Fin 3) :=
        hfirst.trans (hsourceOrders (0 : Fin 3))
      have selectedConditions :
          RepresentationConditions a H.transformed (Nat.le_refl 2) :=
        (a.representationConditions_changeBONG_iff
          (classificationV := classificationV)
          (classificationW := classificationW)
          a b H.transformed (Nat.le_refl 2)).mp conditions
      have hlemma91Selected : a.Lemma91Alternative H.transformed :=
        (a.lemma91Alternative_changeSource_iff_rankThree
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
          b H.transformed).mp hlemma91
      rcases a.exists_beli2019Lemma93MatchedPair_rankThree
          (targetLaws := targetLaws) (sourceLaws := sourceLaws)
          (targetParity := targetParity)
          (targetLocalization := targetLocalization)
          (targetConstruction := targetConstruction)
          (targetSectionTwo := targetSectionTwo)
          (classificationV := classificationV)
          (targetBinaryScaling := targetBinaryScaling)
          (targetQuaternaryScaling := targetQuaternaryScaling)
          (targetLemma49 := targetLemma49) (targetLemma47 := targetLemma47)
          (structuralV := structuralV) (structuralW := structuralW)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
          (sectionFiveW := sectionFiveW)
          (sectionFourW := sectionFourW)
          (sectionFourV := sectionFourV)
          (deepWW := deepWW)
          b H.transformed hfirstSelected ambient conditions
            selectedConditions hlemma91Selected with ⟨P⟩
      have hrawTarget := firstThirdRawDefect_changeTarget_rankThree
        a P.targetBONG H.transformed
      have hrawSelected : defectOrder (K := K)
          ((-1) * P.targetBONG.prefixProduct 3 *
            H.transformed.prefixProduct 1) =
          (H.transformed.alphaValue (0 : Fin 2) : WithTop ℚ) :=
        (hrawTarget.trans H.firstThirdRawDefect_eq).trans
          (congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsourceAlphas (0 : Fin 2)))
      have hdefect :=
        P.targetBONG.firstThirdDefect_eq_tail_of_raw_eq_betaOne_rankThree
          H.transformed P.headValue_eq hrawSelected
      have halpha := by
        letI : Beli2006AlphaLaws.{u, v} K := targetLaws
        exact P.targetBONG.essentialAlpha_eq_rankThree_of_firstThirdDefect_eq_tail
          H.transformed P.headValue_eq hdefect
      exact ⟨P.toLemma93Input a b ambient conditions H.transformed halpha⟩

end BONG.GoodBONG

end Bong
