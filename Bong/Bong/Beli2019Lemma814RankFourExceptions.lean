/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814RankFourLocalization
import Bong.Bong.DiagonalTernaryRepresentationObstruction

/-!
# Beli (2019), Lemma 8.14: rank-four prefix exceptions

This file formalizes case (a) of the quaternary proof.  It identifies the
uncapped first-third defect of the initial ternary segment, proves that
reduction (I) preserves the first two alphas on that segment, and lifts its
rank-three exceptional alternatives to the ambient rank-four BONG whenever
`alpha_2 + alpha_3 > 2e`.
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

/-- The full product of the initial ternary segment is the parent prefix
product through its third value. -/
theorem rankFour_firstThreePrefixProduct_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    (segment.toGoodBONG a.good).prefixProduct 3 = a.prefixProduct 3 := by
  unfold GoodBONG.prefixProduct
  change segment.bong.prefixProduct 3 = a.toBONG.prefixProduct 3
  rw [segment.bong.prefixProduct_succ 2 (by omega),
    segment.bong.prefixProduct_succ 1 (by omega),
    segment.bong.prefixProduct_succ 0 (by omega),
    a.toBONG.prefixProduct_succ 2 (by omega),
    a.toBONG.prefixProduct_succ 1 (by omega),
    a.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul, segment.valueUnit_eq]
  congr 1

/-- The bracketed first-third defect of a rank-three initial segment is
uncapped, because both prefix boundaries are endpoints. -/
theorem rankFour_firstThreeDefect_eq_raw
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    (segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b =
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [rankFour_firstThreePrefixProduct_eq a segment,
    (segment.toGoodBONG a.good).prefixAlphaCap_last,
    b.prefixAlphaCap_last]
  simp

/-- In ambient rank four, the first-third bracket is the minimum of the
uncapped ternary-segment defect and the third global alpha. -/
theorem rankFour_firstThirdCappedDefect_eq_min_segment
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    a.lemma814FirstThirdCappedDefect b =
      min ((segment.toGoodBONG a.good).lemma814FirstThirdCappedDefect b)
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
  rw [rankFour_firstThreeDefect_eq_raw a b segment]
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hindex : (⟨3 - 1, by omega⟩ : Fin 3) = (2 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [hindex]
  simp

/-- The initial ternary block, viewed as a localization at its first alpha. -/
def rankFourFirstThreeFirstAlphaLocalization : AlphaLocalizationIndex 3 where
  start := 0
  pivot := 0
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The literal first-binary alpha is unchanged when passing to the initial
ternary segment. -/
theorem rankFour_firstBinaryAlpha_eq_firstThree
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    (segment.toGoodBONG a.good).firstBinaryAlpha = a.firstBinaryAlpha := by
  let s := segment.toGoodBONG a.good
  have horder0 : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder1 : s.order (1 : Fin 3) = a.order (1 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 1
    simp [BONG.SegmentWitness.sourceIndex]
  have hadjacent : s.adjacentDefect (0 : Fin 2) =
      a.adjacentDefect (0 : Fin 3) := by
    unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
    change defectOrder (K := K)
        (-(segment.bong.valueUnit 0 * segment.bong.valueUnit 1)) =
      defectOrder (K := K)
        (-(a.toBONG.valueUnit 0 * a.toBONG.valueUnit 1))
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 4
  have hhalf : s.halfGapCandidate (0 : Fin 2) =
      a.halfGapCandidate (0 : Fin 3) := by
    unfold halfGapCandidate
    change
      (((((s.order (1 : Fin 3) - s.order (0 : Fin 3) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) =
        (((((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)
    rw [horder0, horder1]
  have hleft : s.leftDefectCandidate (0 : Fin 2) (0 : Fin 2) =
      a.leftDefectCandidate (0 : Fin 3) (0 : Fin 3) := by
    unfold leftDefectCandidate
    change
      (((((s.order (1 : Fin 3) - s.order (0 : Fin 3) : Int) : ℚ)) :
            WithTop ℚ) +
          s.adjacentDefect (0 : Fin 2)) =
        (((((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ)) :
            WithTop ℚ) +
          a.adjacentDefect (0 : Fin 3))
    rw [horder0, horder1, hadjacent]
  unfold firstBinaryAlpha
  rw [hhalf, hleft]

/-- Reduction (I), together with equal first and third orders, makes the
first two alphas of the ternary segment equal to the global alphas. -/
theorem rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ)) :
    (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
        a.alphaValue (0 : Fin 3) ∧
      (segment.toGoodBONG a.good).alphaValue (1 : Fin 2) =
        a.alphaValue (1 : Fin 3) := by
  let s := segment.toGoodBONG a.good
  let p := rankFourFirstThreeFirstAlphaLocalization
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p segment
  have hpivot : p.pivotFin = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocal :
      (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
        (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hlocalLeBinary :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ s.firstBinaryAlpha := by
    unfold firstBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate (0 : Fin 2)
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate (i := (0 : Fin 2))
        (j := (0 : Fin 2)) le_rfl
  have hlocalLeGlobal :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    rw [rankFour_firstBinaryAlpha_eq_firstThree a segment, hbinary] at hlocalLeBinary
    exact hlocalLeBinary
  have hfirst : s.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
    exact_mod_cast le_antisymm hlocalLeGlobal hglobalLeLocal
  have horder0 : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder1 : s.order (1 : Fin 3) = a.order (1 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 1
    simp [BONG.SegmentWitness.sourceIndex]
  have horder2 : s.order (2 : Fin 3) = a.order (2 : Fin 4) := by
    change segment.bong.order 2 = a.toBONG.order 2
    simp [BONG.SegmentWitness.sourceIndex]
  have hlocalOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [horder0, horder2, houter]
  have hglobalRelation :=
    (a.beli2019Remark87 (0 : Fin 2) houter).currentAlpha_eq
  have hlocalRelation :=
    (s.beli2019Remark87 (0 : Fin 1) hlocalOuter).currentAlpha_eq
  change a.alphaValue (1 : Fin 3) =
      ((a.order (0 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) at hglobalRelation
  change s.alphaValue (1 : Fin 2) =
      ((s.order (0 : Fin 3) - s.order (1 : Fin 3) : Int) : ℚ) +
        s.alphaValue (0 : Fin 2) at hlocalRelation
  rw [hfirst, horder0, horder1] at hlocalRelation
  exact ⟨hfirst, hlocalRelation.trans hglobalRelation.symm⟩

/-- The first half-gap is unchanged on the initial ternary segment. -/
theorem rankFour_firstThreeFirstHalfGap_eq
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    (segment.toGoodBONG a.good).halfGapValue (0 : Fin 2) =
      a.halfGapValue (0 : Fin 3) := by
  let s := segment.toGoodBONG a.good
  have horder0 : s.order (0 : Fin 3) = a.order (0 : Fin 4) := by
    change segment.bong.order 0 = a.toBONG.order 0
    simp [BONG.SegmentWitness.sourceIndex]
  have horder1 : s.order (1 : Fin 3) = a.order (1 : Fin 4) := by
    change segment.bong.order 1 = a.toBONG.order 1
    simp [BONG.SegmentWitness.sourceIndex]
  unfold halfGapValue orderGap
  change
    (((s.order (1 : Fin 3) - s.order (0 : Fin 3) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) =
      (((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ))
  rw [horder0, horder1]

/-- The initial ternary segment and the ambient first three values have the
same isotropy status. -/
theorem rankFour_firstThreeIsotropic_iff
    (a : GoodBONG q L 4)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega)) :
    (segment.toGoodBONG a.good).Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
  let s := segment.toGoodBONG a.good
  rw [s.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne,
    a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne]
  have hadjacent0 : s.adjacentProduct (0 : Fin 2) =
      a.adjacentProduct (0 : Fin 3) := by
    unfold adjacentProduct GoodBONG.valueUnit
    change -(segment.bong.valueUnit 0 * segment.bong.valueUnit 1) =
      -(a.toBONG.valueUnit 0 * a.toBONG.valueUnit 1)
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 2
  have hadjacent1 : s.adjacentProduct (1 : Fin 2) =
      a.adjacentProduct (1 : Fin 3) := by
    unfold adjacentProduct GoodBONG.valueUnit
    change -(segment.bong.valueUnit 1 * segment.bong.valueUnit 2) =
      -(a.toBONG.valueUnit 1 * a.toBONG.valueUnit 2)
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 2
  rw [hadjacent0, hadjacent1]

/-- A ternary diagonal space either represents the prescribed line or falls
into exception (a).  The nonrepresentation implication is the standard
dyadic ternary obstruction: the ternary form is anisotropic and its signed
determinant ratio is a square, so the full defect is infinite. -/
theorem rankThree_representation_or_exceptionA
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3)) :
    DiagonalRepresents
        (b.prefixValues 1 (Nat.le_refl _))
        (a.prefixValues 3 (Nat.le_refl _)) ∨
      a.Beli2019Lemma814ExceptionA b := by
  by_cases hrep : DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues 3 (Nat.le_refl _))
  · exact Or.inl hrep
  · right
    have hbValues : b.prefixValues 1 (Nat.le_refl _) =
        (fun _ : Fin 1 ↦ (b.valueUnit (0 : Fin 1) : K)) := by
      funext i
      rw [Fin.eq_zero i]
      rfl
    have haValues : a.prefixValues 3 (Nat.le_refl _) =
        diagonalUnitCoefficients a.valueUnit := by
      funext i
      rfl
    have hnot : ¬DiagonalRepresents
        (fun _ : Fin 1 ↦ (b.valueUnit (0 : Fin 1) : K))
        (diagonalUnitCoefficients a.valueUnit) := by
      simpa only [← hbValues, ← haValues] using hrep
    have obstruction :=
      DyadicTernaryRepresentationObstructionLaws.obstruction
        a.valueUnit (b.valueUnit (0 : Fin 1)) hnot
    have hanisotropic : a.Lemma814FirstThreeAnisotropic := by
      change DiagonalAnisotropic (a.prefixValues 3 (Nat.le_refl _))
      rw [haValues]
      exact obstruction.1
    have haProduct : a.prefixProduct 3 =
        diagonalUnitDeterminant a.valueUnit := by
      classical
      unfold GoodBONG.prefixProduct BONG.prefixProduct
        diagonalUnitDeterminant
      rw [show Finset.univ.filter (fun i : Fin 3 ↦ i.1 < 3) =
          Finset.univ by ext i; simp]
      unfold GoodBONG.valueUnit
      rfl
    have hbProduct : b.prefixProduct 1 = b.valueUnit (0 : Fin 1) := by
      unfold GoodBONG.prefixProduct GoodBONG.valueUnit
      rw [b.toBONG.prefixProduct_succ 0 (by omega),
        b.toBONG.prefixProduct_zero, one_mul]
      congr 1
    have hsquare : IsSquare
        ((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1) := by
      rw [haProduct, hbProduct]
      exact obstruction.2
    have hraw : defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1) = ⊤ :=
      defectOrder_eq_top_of_isSquare hsquare
    have hdefect : a.lemma814FirstThirdCappedDefect b = ⊤ := by
      unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
      rw [a.prefixAlphaCap_last, b.prefixAlphaCap_last, hraw]
      simp
    exact {
      firstThirdOrders_eq := houter
      defectSum_strict := by
        rw [hdefect, add_top]
        simpa only [WithTop.coe_mul] using
          (WithTop.coe_lt_top (2 * (ramificationIndex K : ℚ)))
      firstThree_anisotropic := hanisotropic
    }

/-- At the first unary boundary, the capped defect of the initial ternary
segment agrees with the ambient rank-four defect once their first alphas
are identified. -/
theorem rankFour_firstDefect_eq_segment
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (halpha : (segment.toGoodBONG a.good).alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin 3)) :
    (segment.toGoodBONG a.good).truncatedPrefixDefect b 1 1 1 =
      a.truncatedPrefixDefect b 1 1 1 := by
  let s := segment.toGoodBONG a.good
  have hproduct : s.prefixProduct 1 = a.prefixProduct 1 := by
    unfold GoodBONG.prefixProduct
    change segment.bong.prefixProduct 1 = a.toBONG.prefixProduct 1
    rw [segment.bong.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega)]
    simp only [BONG.prefixProduct_zero, one_mul, segment.valueUnit_eq]
    congr 1
  unfold truncatedPrefixDefect
  rw [hproduct, s.prefixAlphaCap_of_internal (by omega) (by omega),
    a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hlocal : (⟨1 - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hambient : (⟨1 - 1, by omega⟩ : Fin 3) = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [hlocal, hambient, halpha]

/-- Ambient Lemma 8.13 conditions descend to the initial ternary segment
after reduction (I), provided that the segment is nonexceptional.  The
binary trigger is impossible because its first and third orders agree; the
ternary representation follows from the preceding obstruction theorem. -/
theorem rankFour_firstThreeConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional :
      ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b) :
    (segment.toGoodBONG a.good).Lemma813Conditions b := by
  let s := segment.toGoodBONG a.good
  have halphas := rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment houter hbinary
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

/-- In the strict alpha-sum branch, exception (a) for the initial ternary
segment implies exception (a) for the ambient rank-four BONG. -/
theorem rankFour_exceptionA_of_firstThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3))
    (A : (segment.toGoodBONG a.good).Beli2019Lemma814ExceptionA b) :
    a.Beli2019Lemma814ExceptionA b := by
  let s := segment.toGoodBONG a.good
  have halphas := rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment houter hbinary
  have hdefect := rankFour_firstThirdCappedDefect_eq_min_segment a b segment
  have hsumTop :
      (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    exact_mod_cast hsum
  have hstrict :
      (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect b := by
    rw [hdefect]
    rw [add_min]
    apply lt_min
    · rw [← halphas.2]
      exact A.defectSum_strict
    · exact hsumTop
  have hanisotropic : a.Lemma814FirstThreeAnisotropic := by
    rw [← a.not_firstThreeIsotropic_iff_anisotropic]
    intro hisotropic
    have hlocalIso := (rankFour_firstThreeIsotropic_iff a segment).mpr hisotropic
    exact s.not_firstThreeIsotropic_of_anisotropic
      A.firstThree_anisotropic hlocalIso
  exact {
    firstThirdOrders_eq := houter
    defectSum_strict := hstrict
    firstThree_anisotropic := hanisotropic
  }

/-- In the strict alpha-sum branch, exception (b) for the initial ternary
segment implies exception (b) for the ambient rank-four BONG. -/
theorem rankFour_exceptionB_of_firstThree
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3))
    (B : (segment.toGoodBONG a.good).Beli2019Lemma814ExceptionB b) :
    a.Beli2019Lemma814ExceptionB b := by
  let s := segment.toGoodBONG a.good
  have halphas := rankFour_prefixAlphas_eq_of_firstBinaryAlpha
    a segment houter hbinary
  have hdefect := rankFour_firstThirdCappedDefect_eq_min_segment a b segment
  have hsumTop :
      (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    exact_mod_cast hsum
  have hlocalEq :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          s.lemma814FirstThirdCappedDefect b =
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    rw [← halphas.2]
    exact B.defectSum_eq
  have hdefectEq :
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect b =
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    rw [hdefect, add_min, hlocalEq, min_eq_left hsumTop.le]
  have hfirstStrict : a.alphaValue (0 : Fin 3) <
      a.halfGapValue (0 : Fin 3) := by
    rw [← halphas.1, ← rankFour_firstThreeFirstHalfGap_eq a segment]
    exact B.firstAlpha_strict
  have hisotropic : a.Lemma814FirstThreeIsotropic :=
    (rankFour_firstThreeIsotropic_iff a segment).mp B.firstThree_isotropic
  exact {
    firstThirdOrders_eq := houter
    residueTwo := B.residueTwo
    firstAlpha_strict := hfirstStrict
    defectSum_eq := hdefectEq
    firstThree_isotropic := hisotropic
    laterAlphaSum_strict := by
      intro _hfour
      exact hsum
  }

/-- Consequently, ambient nonexceptionality descends to the initial
ternary segment when `alpha_2 + alpha_3 > 2e`. -/
theorem rankFour_notExceptional_firstThree_of_alphaSum_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L 4) (b : GoodBONG r M 1)
    (segment : BONG.SegmentWitness a.toBONG 0 3 (by omega))
    (houter : a.order (0 : Fin 4) = a.order (2 : Fin 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    ¬(segment.toGoodBONG a.good).Beli2019Lemma814Exceptional b := by
  intro E
  rcases E with A | B | C
  · exact hnotExceptional (Or.inl
      (rankFour_exceptionA_of_firstThree a b segment houter hbinary hsum A))
  · exact hnotExceptional (Or.inr (Or.inl
      (rankFour_exceptionB_of_firstThree a b segment houter hbinary hsum B)))
  · exact (by omega : ¬4 ≤ 3) C.rank_four

/-- Beli (2019), Lemma 8.14, quaternary case (a): after reduction (I),
`alpha_2 + alpha_3 > 2e` makes the initial ternary segment safe, so the
completed rank-three theorem and Lemma 4.9(ii) produce the prescribed first
value in the ambient rank-four lattice. -/
theorem beli2019Lemma814_rankFour_alphaSum_gt
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
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  let segment := a.toBONG.segmentWitness 0 3 (by omega)
  have hnotLocal :=
    rankFour_notExceptional_firstThree_of_alphaSum_gt
      a b segment houter hbinary hsum hnotExceptional
  have hconditions := rankFour_firstThreeConditions
    a b segment houter hbinary conditions hnotLocal
  exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b segment horder hconditions hnotLocal

end BONG.GoodBONG
end Bong
