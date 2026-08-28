/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankFourExceptions

/-!
# Beli (2019), Lemma 8.14: the rank-four strict-below branch

This file begins case (b) of the quaternary proof.  It closes the subcase in
which the uncapped first-third defect is already small enough, and records the
two numerical facts needed for the remaining last-pair replacement: the third
alpha is below both the uncapped defect and its half-gap.
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

/-- A ternary target is automatically outside all three exceptional cases
when its second alpha plus the full first-third defect is strictly below
`2e`. -/
theorem rankThree_notExceptional_of_defectSum_lt
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (hdefect :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)) :
    ¬a.Beli2019Lemma814Exceptional b := by
  rintro (A | B | C)
  · exact (not_lt_of_ge A.defectSum_strict.le) hdefect
  · rw [B.defectSum_eq] at hdefect
    exact (lt_irrefl _ hdefect)
  · exact (by omega : ¬4 ≤ 3) C.rank_four

/-- The cancellation step in case (b), stated using only the equality of
the second alpha on the initial ternary segment. -/
theorem rankFour_thirdAlpha_lt_firstThreeDefect_of_secondAlpha_eq
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (hsecond : (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin 3))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hlarge : (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
      (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) +
        (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b) :
    (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b := by
  have hsumTop :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast hsum
  have hadd :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b := by
    exact hsumTop.trans_le (by simpa only [hsecond] using hlarge)
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hadd

/-- In the high-local-defect subcase of case (b), the third global alpha is
strictly below the uncapped defect of the initial ternary segment. -/
theorem rankFour_thirdAlpha_lt_firstThreeDefect_of_alphaSum_lt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hlarge : (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
      (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) +
        (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b) :
    (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b := by
  have halphas := rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment houter hbinary
  have hsumTop :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast hsum
  have hadd :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b := by
    exact hsumTop.trans_le (by simpa only [halphas.2] using hlarge)
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hadd

/-- The strict inequality `alpha_2 + alpha_3 < 2e` places the third alpha
strictly below its half-gap. -/
theorem rankFour_thirdAlpha_lt_halfGap_of_alphaSum_lt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ)) :
    a.alphaValue (2 : Fin 3) < a.halfGapValue (2 : Fin 3) := by
  have hp1 := (a.alpha_p1 (1 : Fin 3) (by omega)).2
  have hp1' :
      -(a.order (3 : Fin 4) : ℚ) + a.alphaValue (2 : Fin 3) ≤
        -(a.order (2 : Fin 4) : ℚ) + a.alphaValue (1 : Fin 3) := by
    simpa [alphaRightEndpoint] using hp1
  unfold halfGapValue orderGap
  push_cast
  linarith

/-- If `alpha_1 ≥ alpha_3` and `R_2 < R_4`, the strict-below branch forces
the literal final binary alpha to equal the global third alpha. -/
theorem rankFour_lastBinaryAlpha_eq_of_alphaSum_lt_of_first_ge
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hfirstGe : a.alphaValue (2 : Fin 3) ≤ a.alphaValue (0 : Fin 3)) :
    a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  have hremark := a.beli2019Remark87 (0 : Fin 2) houter
  have hrelation :
      a.alphaValue (1 : Fin 3) =
        ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
          a.alphaValue (0 : Fin 3) := by
    simpa [remark87CurrentAlpha, remark87PreviousAlpha,
      remark87PreviousValue, remark87MiddleValue, remark87NextValue] using
        hremark.currentAlpha_eq
  have houterQ : (a.order (0 : Fin 4) : ℚ) =
      (a.order (2 : Fin 4) : ℚ) := by
    exact_mod_cast houter
  have hsecondFourthQ : (a.order (1 : Fin 4) : ℚ) <
      (a.order (3 : Fin 4) : ℚ) := by
    exact_mod_cast hsecondFourth
  have hneighborQ : a.alphaValue (2 : Fin 3) <
      a.alphaGapValue (2 : Fin 3) + a.alphaValue (1 : Fin 3) := by
    unfold alphaGapValue
    rw [hrelation]
    push_cast
    linarith
  apply rankFour_lastBinaryAlpha_eq_of_lt_neighbor a
  unfold neighborAlphaCandidate
  exact_mod_cast hneighborQ

/-- The alpha of the canonical final binary segment, stated with an
arbitrary equality identifying the literal last-binary alpha. -/
theorem rankFour_lastPairAlpha_eq_of_lastBinaryAlpha
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 2 2 (by omega))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    (segment.toGoodBONG a.good).alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) := by
  have hsegment :=
    a.adjacentBinaryAlpha_eq_segmentAlpha (2 : Fin 3) segment
  have hlastIndex : Fin.last 2 = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [lastBinaryAlpha, hlastIndex] at hlast
  exact_mod_cast hsegment.symm.trans hlast

/-- The final binary segment has the same half-gap as the final adjacent
pair of the ambient rank-four BONG. -/
theorem rankFour_lastPairHalfGap_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 2 2 (by omega)) :
    (segment.toGoodBONG a.good).halfGapValue (0 : Fin 1) =
      a.halfGapValue (2 : Fin 3) := by
  let p := suffixPairLocalization (N := 2) (2 : Fin 3)
  have hpivot : p.pivotFin = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have hlocal : p.localPivot = (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hcandidate := a.segment_halfGapCandidate_local p segment
  rw [hpivot, hlocal] at hcandidate
  unfold halfGapCandidate at hcandidate
  unfold halfGapValue
  exact_mod_cast hcandidate

/-- The first global alpha is the minimum of the alpha of the initial
ternary segment and the right-compression value supplied by the final
binary segment.  This is the exact finite-candidate decomposition behind
the paper's formula
`alpha_1 = min (hat alpha_1) (R_3 - R_1 + alpha_3)`. -/
theorem rankFour_firstAlpha_eq_min_firstThree_lastPairCompression
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (firstThree : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (lastPair : BONG.SegmentWitness a.toBONG 2 2 (by omega)) :
    (a.alphaValue (0 : Fin 3) : WithTop ℚ) =
      min
        ((firstThree.toGoodBONG a.good).alphaValue (0 : Fin 2) :
          WithTop ℚ)
        (a.rightCompressionValue
          (suffixPairLocalization (N := 2) (2 : Fin 3))
          (0 : Fin 3) lastPair : WithTop ℚ) := by
  let p := rankFourFirstThreeFirstAlphaLocalization
  let t := suffixPairLocalization (N := 2) (2 : Fin 3)
  let first := firstThree.toGoodBONG a.good
  have hpivot : p.pivotFin = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  have htpivot : t.pivotFin = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have hplocal : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hipivot : (0 : Fin 3) ≤ t.pivotFin := by
    rw [htpivot]
    omega
  have hglobalFirst := a.beli2009Lemma21_le_segmentAlpha p firstThree
  have hglobalLast := a.alpha_le_rightCompressionValue
    t (0 : Fin 3) hipivot lastPair
  rw [hpivot] at hglobalFirst
  rw [a.coe_alphaValue, first.coe_alphaValue]
  apply le_antisymm
  · exact le_min hglobalFirst hglobalLast
  · unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · have hlocal := first.alpha_le_halfGapCandidate p.localPivot
      have hsegment := a.segment_halfGapCandidate_local p firstThree
      dsimp [first, p, rankFourFirstThreeFirstAlphaLocalization] at hlocal
      dsimp [p, rankFourFirstThreeFirstAlphaLocalization] at hsegment
      rw [hsegment] at hlocal
      exact (min_le_left _ _).trans hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ (0 : Fin 3) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hstart : p.start ≤ j.1 := by
        dsimp [p, rankFourFirstThreeFirstAlphaLocalization]
        omega
      have hstop : j.1 < p.stop := by
        dsimp [p, rankFourFirstThreeFirstAlphaLocalization]
        omega
      have hjpivot : j ≤ p.pivotFin := by
        simpa only [hpivot] using hji
      have hlocalIndex :
          p.localAdjacent j hstart hstop ≤ p.localPivot := by
        change j.1 - p.start ≤ p.pivot - p.start
        change j.1 ≤ p.pivot at hjpivot
        omega
      have hlocal := first.alpha_le_leftDefectCandidate hlocalIndex
      have hsegment := a.segment_leftDefectCandidate_local
        p firstThree j hstart hstop hjpivot
      dsimp [first, p, rankFourFirstThreeFirstAlphaLocalization] at hlocal
      dsimp [p, rankFourFirstThreeFirstAlphaLocalization] at hsegment
      rw [hsegment] at hlocal
      exact (min_le_left _ _).trans hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : (0 : Fin 3) ≤ j := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      by_cases hinside : j.1 < p.stop
      · have hstart : p.start ≤ j.1 := by
          dsimp [p, rankFourFirstThreeFirstAlphaLocalization]
          omega
        have hpivotj : p.pivotFin ≤ j := by
          simpa only [hpivot] using hij
        have hlocalIndex : p.localPivot ≤
            p.localAdjacent j hstart hinside := by
          change p.pivot - p.start ≤ j.1 - p.start
          change p.pivot ≤ j.1 at hpivotj
          omega
        have hlocal := first.alpha_le_rightDefectCandidate hlocalIndex
        have hsegment := a.segment_rightDefectCandidate_local
          p firstThree j hstart hinside hpivotj
        dsimp [first, p, rankFourFirstThreeFirstAlphaLocalization] at hlocal
        dsimp [p, rankFourFirstThreeFirstAlphaLocalization] at hsegment
        rw [hsegment] at hlocal
        exact (min_le_left _ _).trans hlocal
      · have hpivotj : t.pivotFin ≤ j := by
          change 2 ≤ j.1
          dsimp [p, rankFourFirstThreeFirstAlphaLocalization] at hinside
          omega
        have hstop : j.1 < t.stop := by
          dsimp [t, suffixPairLocalization]
          exact j.isLt
        exact (min_le_right _ _).trans
          (a.rightCompressionValue_le_candidate t (0 : Fin 3) j
            hipivot hpivotj hstop lastPair)

/-- Under equal first and third orders, `alpha_1 < alpha_3` makes the first
two alphas of the initial ternary segment independent of the chosen good
BONG. -/
theorem rankFour_prefixAlphas_eq_of_first_lt_third
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (firstThree : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (lastPair : BONG.SegmentWitness a.toBONG 2 2 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hfirstLt : a.alphaValue (0 : Fin 3) <
      a.alphaValue (2 : Fin 3)) :
    (firstThree.toGoodBONG a.good).alphaValue (0 : Fin 2) =
        a.alphaValue (0 : Fin 3) ∧
      (firstThree.toGoodBONG a.good).alphaValue (1 : Fin 2) =
        a.alphaValue (1 : Fin 3) := by
  let first := firstThree.toGoodBONG a.good
  let t := suffixPairLocalization (N := 2) (2 : Fin 3)
  let last := lastPair.toGoodBONG a.good
  have hformula :=
    rankFour_firstAlpha_eq_min_firstThree_lastPairCompression
      a firstThree lastPair
  have htpivot : t.pivotFin = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  have htlocal : t.localPivot = (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hlastLowerRaw := a.beli2009Lemma21_le_segmentAlpha t lastPair
  have hlastLower : (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
      (last.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    rw [htpivot, htlocal] at hlastLowerRaw
    rw [a.coe_alphaValue, last.coe_alphaValue]
    exact hlastLowerRaw
  have hcompression :
      (a.rightCompressionValue t (0 : Fin 3) lastPair : WithTop ℚ) =
        (last.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    unfold rightCompressionValue
    rw [htpivot, htlocal]
    have hcastZero : (0 : Fin 3).castSucc = (0 : Fin 4) := by
      apply Fin.ext
      rfl
    have hcastTwo : (2 : Fin 3).castSucc = (2 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hcastZero, hcastTwo, houter]
    norm_num
    rfl
  have hfirstLtCompression :
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        (a.rightCompressionValue t (0 : Fin 3) lastPair : WithTop ℚ) := by
    rw [hcompression]
    have hfirstLtTop : (a.alphaValue (0 : Fin 3) : WithTop ℚ) <
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
      exact_mod_cast hfirstLt
    exact hfirstLtTop.trans_le hlastLower
  have hminLt :
      min ((first.alphaValue (0 : Fin 2) : WithTop ℚ))
          (a.rightCompressionValue t (0 : Fin 3) lastPair : WithTop ℚ) <
        (a.rightCompressionValue t (0 : Fin 3) lastPair : WithTop ℚ) := by
    rw [← hformula]
    exact hfirstLtCompression
  have hlocalLt : (first.alphaValue (0 : Fin 2) : WithTop ℚ) <
      (a.rightCompressionValue t (0 : Fin 3) lastPair : WithTop ℚ) :=
    (min_lt_iff.mp hminLt).resolve_right (lt_irrefl _)
  rw [min_eq_left hlocalLt.le] at hformula
  have hfirst : first.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin 3) := by
    exact_mod_cast hformula.symm
  have horder0 : first.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change firstThree.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder1 : first.order (1 : Fin 3) = a.order (1 : Fin 4) := by
    change firstThree.bong.order 1 = a.toBONG.order 1
    simp [BONG.SegmentWitness.sourceIndex]
  have horder2 : first.order (2 : Fin 3) = a.order (2 : Fin 4) := by
    change firstThree.bong.order 2 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hlocalOuter : first.order (0 : Fin 3) =
      first.order (2 : Fin 3) := by
    rw [horder0, horder2, houter]
  have hglobalRelation :=
    (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
  have hlocalRelation :=
    (first.beli2019Remark87 (0 : Fin 1) hlocalOuter).currentAlpha_eq
  change a.alphaValue (1 : Fin 3) =
      ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hglobalRelation
  change first.alphaValue (1 : Fin 2) =
      ((first.order (0 : Fin 3) - first.order (1 : Fin 3) : Int) : ℚ) +
        first.alphaValue (0 : Fin 2) at hlocalRelation
  rw [hfirst, horder0, horder1] at hlocalRelation
  exact ⟨hfirst, hlocalRelation.trans hglobalRelation.symm⟩

/-- Data produced by applying Lemma 8.8 to the final binary segment and
then inserting that segment back into a rank-four BONG. -/
structure Beli2019Lemma814LastPairScalingData
    (a : GoodBONG q L 4) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (a.alphaValue (2 : Fin 3) : WithTop ℚ)
  transformed : GoodBONG q L 4
  firstValue_eq : transformed.valueUnit (0 : Fin 4) =
    a.valueUnit (0 : Fin 4)
  secondValue_eq : transformed.valueUnit (1 : Fin 4) =
    a.valueUnit (1 : Fin 4)
  thirdValue_eq : transformed.valueUnit (2 : Fin 4) =
    epsilon * a.valueUnit (2 : Fin 4)

/-- Insert an already constructed Lemma 8.8 transformation of the final
binary segment into the ambient rank-four BONG.  Separating this geometric
step from the existence proof lets the equality-boundary argument inspect
the exceptional alternative for the final pair before deciding whether a
transformation is available. -/
theorem rankFour_lastPairScalingData_of_transform
    [GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 2 2 (by omega))
    (T : (segment.toGoodBONG a.good).Beli2019FirstValueTransform)
    (halpha : (segment.toGoodBONG a.good).alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3)) :
    Nonempty (Beli2019Lemma814LastPairScalingData a) := by
  let s := segment.toGoodBONG a.good
  rcases a.toBONG.beliLemma49_ii a.good segment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L 4 :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin 4) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin 4) =
      T.transformed.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change replacement.bong.value 2 = T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    have hinside := replacement.inside_eq (0 : Fin 2)
    simpa using congrArg q.quadratic hinside
  have hsegmentFirst : s.valueUnit (0 : Fin 2) =
      a.valueUnit (2 : Fin 4) := by
    change segment.bong.valueUnit 0 = a.toBONG.valueUnit 2
    simp [BONG.SegmentWitness.sourceIndex]
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans
      (congrArg (fun x : ℚ => (x : WithTop ℚ)) halpha)
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin 4) (by omega)
    secondValue_eq := beforeValue_eq (1 : Fin 4) (by omega)
    thirdValue_eq := hthirdLocal.trans <| T.firstValue_eq.trans <|
      congrArg (T.epsilon * ·) hsegmentFirst
  }⟩

/-- Lemma 8.8 on the final binary pair, followed by Lemma 4.9(ii), gives a
rank-four coordinate change that fixes the first two values and multiplies
the third value by a unit of defect `alpha_3`. -/
theorem exists_rankFour_lastPairScaling
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L 4)
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hstrict : a.alphaValue (2 : Fin 3) <
      a.halfGapValue (2 : Fin 3)) :
    Nonempty (Beli2019Lemma814LastPairScalingData a) := by
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have halpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin 3) :=
    rankFour_lastPairAlpha_eq_of_lastBinaryAlpha a segment hlast
  have hhalf : s.halfGapValue (0 : Fin 1) =
      a.halfGapValue (2 : Fin 3) :=
    rankFour_lastPairHalfGap_eq a segment
  have hlocalStrict : s.alphaValue (0 : Fin 1) <
      s.halfGapValue (0 : Fin 1) := by
    rw [halpha, hhalf]
    exact hstrict
  have hnotExceptional : ¬s.Beli2019Lemma88Exceptional := by
    rintro ⟨hattains, _⟩
    exact (ne_of_lt hlocalStrict) hattains
  rcases s.beli2019Lemma88_rankTwo_sufficiency hnotExceptional with ⟨T⟩
  exact rankFour_lastPairScalingData_of_transform a segment T halpha

/-- A last-pair scaling leaves the literal first-binary alpha unchanged. -/
theorem Beli2019Lemma814LastPairScalingData.firstBinaryAlpha_eq
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a) :
    D.transformed.firstBinaryAlpha = a.firstBinaryAlpha := by
  have horders := a.order_invariant D.transformed
  have hhalf : D.transformed.halfGapCandidate (0 : Fin 3) =
      a.halfGapCandidate (0 : Fin 3) := by
    unfold halfGapCandidate
    rw [← horders (Fin.castSucc (0 : Fin 3)),
      ← horders (Fin.succ (0 : Fin 3))]
  have hadjacent : D.transformed.adjacentDefect (0 : Fin 3) =
      a.adjacentDefect (0 : Fin 3) := by
    unfold adjacentDefect adjacentProduct
    have hfirst : D.transformed.valueUnit (Fin.castSucc (0 : Fin 3)) =
        a.valueUnit (Fin.castSucc (0 : Fin 3)) := by
      simpa using D.firstValue_eq
    have hsecond : D.transformed.valueUnit (Fin.succ (0 : Fin 3)) =
        a.valueUnit (Fin.succ (0 : Fin 3)) := by
      simpa using D.secondValue_eq
    rw [hfirst, hsecond]
  have hleft : D.transformed.leftDefectCandidate
      (0 : Fin 3) (0 : Fin 3) =
        a.leftDefectCandidate (0 : Fin 3) (0 : Fin 3) := by
    unfold leftDefectCandidate
    rw [← horders (Fin.castSucc (0 : Fin 3)),
      ← horders (Fin.succ (0 : Fin 3)), hadjacent]
  unfold firstBinaryAlpha
  rw [hhalf, hleft]

/-- The product of the first three values after a last-pair scaling is the
old product multiplied by the chosen unit. -/
theorem Beli2019Lemma814LastPairScalingData.prefixProduct_three_eq
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a) :
    D.transformed.prefixProduct 3 = D.epsilon * a.prefixProduct 3 := by
  unfold GoodBONG.prefixProduct
  rw [D.transformed.toBONG.prefixProduct_succ 2 (by omega),
    D.transformed.toBONG.prefixProduct_succ 1 (by omega),
    D.transformed.toBONG.prefixProduct_succ 0 (by omega),
    a.toBONG.prefixProduct_succ 2 (by omega),
    a.toBONG.prefixProduct_succ 1 (by omega),
    a.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  have hzero : (⟨0, by omega⟩ : Fin 4) = (0 : Fin 4) := by
    apply Fin.ext
    rfl
  have hone : (⟨1, by omega⟩ : Fin 4) = (1 : Fin 4) := by
    apply Fin.ext
    rfl
  have htwo : (⟨2, by omega⟩ : Fin 4) = (2 : Fin 4) := by
    apply Fin.ext
    rfl
  have hfirst : D.transformed.toBONG.valueUnit ⟨0, by omega⟩ =
      a.toBONG.valueUnit ⟨0, by omega⟩ := by
    change D.transformed.valueUnit ⟨0, by omega⟩ =
      a.valueUnit ⟨0, by omega⟩
    rw [hzero]
    exact D.firstValue_eq
  have hsecond : D.transformed.toBONG.valueUnit ⟨1, by omega⟩ =
      a.toBONG.valueUnit ⟨1, by omega⟩ := by
    change D.transformed.valueUnit ⟨1, by omega⟩ =
      a.valueUnit ⟨1, by omega⟩
    rw [hone]
    exact D.secondValue_eq
  have hthird : D.transformed.toBONG.valueUnit ⟨2, by omega⟩ =
      D.epsilon * a.toBONG.valueUnit ⟨2, by omega⟩ := by
    change D.transformed.valueUnit ⟨2, by omega⟩ =
      D.epsilon * a.valueUnit ⟨2, by omega⟩
    rw [htwo]
    exact D.thirdValue_eq
  rw [hfirst, hsecond, hthird]
  ac_rfl

/-- If the old uncapped first-third defect is strictly larger than
`alpha_3`, the last-pair scaling makes the new uncapped defect exactly
`alpha_3`. -/
theorem Beli2019Lemma814LastPairScalingData.firstThreeDefect_eq
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4}
    (D : Beli2019Lemma814LastPairScalingData a)
    (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness D.transformed.toBONG 0 3 (by omega))
    (hraw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    (segment.toGoodBONG D.transformed.good).lemma814FirstThirdCappedDefect b =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  rw [rankFour_firstThreeDefect_eq_raw D.transformed b segment,
    D.prefixProduct_three_eq]
  have hproduct :
      (-1 : Kˣ) * (D.epsilon * a.prefixProduct 3) * b.prefixProduct 1 =
        D.epsilon * ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    ac_rfl
  rw [hproduct]
  have hstrict : defectOrder (K := K) D.epsilon <
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    rw [D.epsilon_defect]
    exact hraw
  rw [defectOrder_mul_eq_left_of_lt_right (K := K) hstrict,
    D.epsilon_defect]

/-- Ambient Lemma 8.13 conditions descend to the initial ternary segment
whenever the two local alpha equalities are supplied explicitly. -/
theorem rankFour_firstThreeConditions_of_prefixAlphas
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (halphas :
      (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
          a.alphaValue (0 : Fin 3) ∧
        (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
          a.alphaValue (1 : Fin 3))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    (segment.toGoodBONG a.good).Lemma813Conditions b := by
  let s := segment.toGoodBONG a.good
  have horder0 : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder2 : s.order (2 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 2 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hlocalOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [horder0, horder2, houter]
  have hrepresentation : DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (s.prefixValues 3 (Nat.le_refl _)) := by
    rcases rankThree_representation_or_exceptionA s b hlocalOuter with
      hrep | A
    · exact hrep
    · exact (hnotExceptional (Or.inl A)).elim
  exact {
    defectEquality := by
      calc
        s.truncatedPrefixDefect b 1 1 1 =
            a.truncatedPrefixDefect b 1 1 1 :=
          rankFour_firstDefect_eq_segment a b segment halphas.1
        _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) :=
          conditions.defectEquality
        _ = (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
          exact_mod_cast halphas.1.symm
    binaryRankTwo := by
      intro hm
      omega
    binaryHigher := by
      intro _hm htrigger
      rcases htrigger with ⟨hlt, _⟩
      rw [hlocalOuter] at hlt
      exact (lt_irrefl _ hlt).elim
    ternaryRankThree := by
      intro _hm _horders
      exact hrepresentation
    ternaryHigher := by
      intro hm
      omega
  }

/-- A strict local defect sum, together with explicit prefix-alpha
localization, is the common terminal reduction for both subbranches of
case (b). -/
theorem beli2019Lemma814_rankFour_of_localDefectSum_lt_of_prefixAlphas
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
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (horder : a.order (0 : Fin 4) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (halphas :
      (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
          a.alphaValue (0 : Fin 3) ∧
        (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
          a.alphaValue (1 : Fin 3))
    (hlocal :
      ((segment.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have hnotLocal := rankThree_notExceptional_of_defectSum_lt
    (segment.toGoodBONG a.good) b hlocal
  have hconditions := rankFour_firstThreeConditions_of_prefixAlphas
    a b segment houter halphas conditions hnotLocal
  exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b segment horder hconditions hnotLocal

/-- The no-change subcase of Beli's quaternary case (b).  Once reduction
(I) has been made, a strict local defect sum makes the initial ternary
segment safe, so the completed rank-three theorem lifts immediately. -/
theorem beli2019Lemma814_rankFour_alphaSum_lt_of_localDefectSum_lt
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
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hlocal :
      let segment := a.toBONG.segmentWitness 0 3 (by omega)
      ((segment.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  let segment := a.toBONG.segmentWitness 0 3 (by omega)
  have hnotLocal := rankThree_notExceptional_of_defectSum_lt
    (segment.toGoodBONG a.good) b (by simpa only [segment] using hlocal)
  have hconditions := rankFour_firstThreeConditions
    a b segment houter hbinary conditions hnotLocal
  exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b segment horder hconditions hnotLocal

/-- Beli (2019), Lemma 8.14, quaternary case (b), in the subbranch
`alpha_1 ≥ alpha_3`.  If the local defect is already small, the initial
ternary segment is used directly.  Otherwise Lemma 8.8 scales the final
binary pair; the new initial ternary defect becomes exactly `alpha_3`, and
the same rank-three reduction applies. -/
theorem beli2019Lemma814_rankFour_alphaSum_lt_of_first_ge
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
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4))
    (hfirstGe : a.alphaValue (2 : Fin 3) ≤
      a.alphaValue (0 : Fin 3)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let oldSegment := a.toBONG.segmentWitness 0 3 (by omega)
  by_cases hlocal :
      ((oldSegment.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (oldSegment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  · exact a.beli2019Lemma814_rankFour_alphaSum_lt_of_localDefectSum_lt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions houter hbinary (by
        simpa only [oldSegment] using hlocal)
  · have hlarge :
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
          (oldSegment.toGoodBONG a.good).alphaValue (1 : Fin 2) +
            (oldSegment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b :=
      le_of_not_gt hlocal
    have hrawLocal :=
      rankFour_thirdAlpha_lt_firstThreeDefect_of_alphaSum_lt
        a b oldSegment houter hbinary hsum hlarge
    have hraw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [← rankFour_firstThreeDefect_eq_raw a b oldSegment]
      exact hrawLocal
    have hlast := rankFour_lastBinaryAlpha_eq_of_alphaSum_lt_of_first_ge
      a houter hsecondFourth hfirstGe
    have hstrict := rankFour_thirdAlpha_lt_halfGap_of_alphaSum_lt a hsum
    rcases exists_rankFour_lastPairScaling
      (classificationV := classificationV) a hlast hstrict with ⟨D⟩
    let changed := D.transformed
    let newSegment := changed.toBONG.segmentWitness 0 3 (by omega)
    have hnewDefect :
        (newSegment.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      D.firstThreeDefect_eq b newSegment hraw
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
    have hchangedBinary : changed.firstBinaryAlpha =
        (changed.alphaValue (0 : Fin 3) : WithTop ℚ) := by
      calc
        changed.firstBinaryAlpha = a.firstBinaryAlpha := D.firstBinaryAlpha_eq
        _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) := hbinary
        _ = (changed.alphaValue (0 : Fin 3) : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (halphas (0 : Fin 3))
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classificationV)
      (classificationW := classificationW) changed b horder conditions
    have hprefix := rankFour_prefixAlphas_eq_of_firstBinaryAlpha
      changed newSegment hchangedOuter hchangedBinary
    have hnewLocal :
        ((newSegment.toGoodBONG changed.good).alphaValue (1 : Fin 2) :
            WithTop ℚ) +
            (newSegment.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b <
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      rw [hprefix.2, hnewDefect, ← halphas (1 : Fin 3)]
      exact_mod_cast hsum
    exact changed.beli2019Lemma814_rankFour_alphaSum_lt_of_localDefectSum_lt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b hchangedOrder hchangedConditions hchangedOuter hchangedBinary
      (by simpa only [newSegment] using hnewLocal)

/-- The terminal form of the `alpha_1 < alpha_3` subbranch once the final
literal binary segment realizes the third global alpha. -/
theorem beli2019Lemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
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
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hfirstLt : a.alphaValue (0 : Fin 3) <
      a.alphaValue (2 : Fin 3))
    (hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let oldFirst := a.toBONG.segmentWitness 0 3 (by omega)
  let oldLast := a.toBONG.segmentWitness 2 2 (by omega)
  have holdPrefix := rankFour_prefixAlphas_eq_of_first_lt_third
    a oldFirst oldLast houter hfirstLt
  by_cases hlocal :
      ((oldFirst.toGoodBONG a.good).alphaValue (1 : Fin 2) : WithTop ℚ) +
          (oldFirst.toGoodBONG a.good).lemma814FirstThirdCappedDefect b <
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  · exact a.beli2019Lemma814_rankFour_of_localDefectSum_lt_of_prefixAlphas
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b oldFirst horder conditions houter holdPrefix hlocal
  · have hlarge :
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) ≤
          (oldFirst.toGoodBONG a.good).alphaValue (1 : Fin 2) +
            (oldFirst.toGoodBONG a.good).lemma814FirstThirdCappedDefect b :=
      le_of_not_gt hlocal
    have hrawLocal :=
      rankFour_thirdAlpha_lt_firstThreeDefect_of_secondAlpha_eq
        a b oldFirst holdPrefix.2 hsum hlarge
    have hraw : (a.alphaValue (2 : Fin 3) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [← rankFour_firstThreeDefect_eq_raw a b oldFirst]
      exact hrawLocal
    have hstrict := rankFour_thirdAlpha_lt_halfGap_of_alphaSum_lt a hsum
    rcases exists_rankFour_lastPairScaling
      (classificationV := classificationV) a hlast hstrict with ⟨D⟩
    let changed := D.transformed
    let newFirst := changed.toBONG.segmentWitness 0 3 (by omega)
    let newLast := changed.toBONG.segmentWitness 2 2 (by omega)
    have hnewDefect :
        (newFirst.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b =
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) :=
      D.firstThreeDefect_eq b newFirst hraw
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
    have hchangedFirstLt : changed.alphaValue (0 : Fin 3) <
        changed.alphaValue (2 : Fin 3) := by
      rw [← halphas (0 : Fin 3), ← halphas (2 : Fin 3)]
      exact hfirstLt
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classificationV)
      (classificationW := classificationW) changed b horder conditions
    have hnewPrefix := rankFour_prefixAlphas_eq_of_first_lt_third
      changed newFirst newLast hchangedOuter hchangedFirstLt
    have hnewLocal :
        ((newFirst.toGoodBONG changed.good).alphaValue (1 : Fin 2) :
            WithTop ℚ) +
            (newFirst.toGoodBONG changed.good).lemma814FirstThirdCappedDefect b <
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      rw [hnewPrefix.2, hnewDefect, ← halphas (1 : Fin 3)]
      exact_mod_cast hsum
    exact changed.beli2019Lemma814_rankFour_of_localDefectSum_lt_of_prefixAlphas
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b newFirst hchangedOrder hchangedConditions hchangedOuter
      hnewPrefix hnewLocal

/-- Beli (2019), Lemma 8.14, complete quaternary case (b) when
`alpha_1 < alpha_3`.  Corollary 8.11 first normalizes the last binary pair
if necessary; the preceding BONG-independent localization theorem preserves
the initial ternary reduction. -/
theorem beli2019Lemma814_rankFour_alphaSum_lt_of_first_lt
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
    [BONGStructuralLaws.{u, v} K]
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
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hfirstLt : a.alphaValue (0 : Fin 3) <
      a.alphaValue (2 : Fin 3)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  by_cases hlast : a.lastBinaryAlpha =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ)
  · exact a.beli2019Lemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions houter hsum hfirstLt hlast
  · rcases a.beli2019Corollary811 (2 : Fin 3) with ⟨C⟩
    let changed := C.transformed
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
        changed.alphaValue (2 : Fin 3) <
          2 * (ramificationIndex K : ℚ) := by
      rw [← halphas (1 : Fin 3), ← halphas (2 : Fin 3)]
      exact hsum
    have hchangedFirstLt : changed.alphaValue (0 : Fin 3) <
        changed.alphaValue (2 : Fin 3) := by
      rw [← halphas (0 : Fin 3), ← halphas (2 : Fin 3)]
      exact hfirstLt
    have hchangedConditions := a.lemma813Conditions_changeTargetBONG
      (classificationV := classificationV)
      (classificationW := classificationW) changed b horder conditions
    have hlastIndex : Fin.last 2 = (2 : Fin 3) := by
      apply Fin.ext
      rfl
    have hchangedLast : changed.lastBinaryAlpha =
        (changed.alphaValue (2 : Fin 3) : WithTop ℚ) := by
      unfold lastBinaryAlpha
      rw [hlastIndex]
      exact C.adjacentBinaryAlpha_eq
    exact beli2019Lemma814_rankFour_alphaSum_lt_of_first_lt_of_lastBinaryAlpha
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      changed original b hchangedOrder hchangedConditions hchangedOuter hchangedSum
      hchangedFirstLt hchangedLast

/-- Beli (2019), Lemma 8.14, complete quaternary case (b):
`alpha_2 + alpha_3 < 2e`. -/
theorem beli2019Lemma814_rankFour_alphaSum_lt
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
    [BONGStructuralLaws.{u, v} K]
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
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) <
      2 * (ramificationIndex K : ℚ))
    (hsecondFourth : a.order (1 : Fin 4) < a.order (3 : Fin 4)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  by_cases hfirstGe : a.alphaValue (2 : Fin 3) ≤
      a.alphaValue (0 : Fin 3)
  · exact a.beli2019Lemma814_rankFour_alphaSum_lt_of_first_ge
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions houter hbinary hsum hsecondFourth hfirstGe
  · have hfirstLt : a.alphaValue (0 : Fin 3) <
        a.alphaValue (2 : Fin 3) := lt_of_not_ge hfirstGe
    exact a.beli2019Lemma814_rankFour_alphaSum_lt_of_first_lt
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      original b horder conditions houter hsum hfirstLt

end BONG.GoodBONG

end Bong
