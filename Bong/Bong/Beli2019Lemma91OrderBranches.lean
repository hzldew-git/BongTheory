/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Complete

/-!
# Beli (2019), Lemma 9.1: the immediate order branches

Lemma 9.1 invokes Lemma 8.14 after excluding its three exceptional
alternatives.  This file proves the exclusions that follow from
`R₁ < R₃`, `R₂ = R₄`, and the first-three capped-defect equality,
together with the direct binary construction when `R₂ - R₁ = 2e`.
-/

namespace Bong

open Dyadic

universe u v w x

private theorem left_eq_of_min_eq_of_lt_right
    {T : Type*} [LinearOrder T] {left right value : T}
    (hmin : min left right = value) (hvalue : value < right) :
    left = value := by
  by_cases hle : left ≤ right
  · simpa only [min_eq_left hle] using hmin
  · have hright : right ≤ left := le_of_not_ge hle
    have heq : right = value := by
      simpa only [min_eq_right hright] using hmin
    exact (ne_of_lt hvalue heq.symm).elim

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- If `R₁ < R₃`, none of Lemma 8.14(a)--(c) can occur, since every
exceptional alternative requires `R₁ = R₃`. -/
theorem not_lemma814Exceptional_of_firstThird_lt
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirstThird : a.order (0 : Fin (N + 3)) <
      a.order (⟨2, by omega⟩ : Fin (N + 3))) :
    ¬a.Beli2019Lemma814Exceptional b := by
  rintro (A | B | C)
  · exact (ne_of_lt hfirstThird) A.firstThirdOrders_eq
  · exact (ne_of_lt hfirstThird) B.firstThirdOrders_eq
  · exact (ne_of_lt hfirstThird) C.firstThirdOrders_eq

set_option maxHeartbeats 1000000 in
/-- If `R₂ = R₄`, Remark 8.7 gives `α₂ + α₃ ≤ 2e`.  This contradicts
the strict inequality in exception (a), the explicit later-alpha inequality
in exception (b), and the strict order inequality in exception (c). -/
theorem not_lemma814Exceptional_of_secondFourth_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3)
    (hsecondFourth : a.order (1 : Fin (N + 3)) =
      a.order (⟨3, by omega⟩ : Fin (N + 3))) :
    ¬a.Beli2019Lemma814Exceptional b := by
  let p : Fin (N + 1) := ⟨1, by omega⟩
  have houter :
      a.order (remark87PreviousValue p) =
        a.order (remark87NextValue p) := by
    change a.order (⟨1, by omega⟩ : Fin (N + 3)) =
      a.order (⟨1 + 2, by omega⟩ : Fin (N + 3))
    convert hsecondFourth using 1 <;> congr
  have R := a.beli2019Remark87 p houter
  rintro (A | B | C)
  · have hdefect : a.lemma814FirstThirdCappedDefect b ≤
        (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
      have hcap := a.truncatedPrefixDefect_le_leftCap b (-1) 3 1
      rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      simpa only [lemma814FirstThirdCappedDefect] using hcap
    have hsum :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) ≤
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      change ((a.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
      exact WithTop.coe_le_coe.mpr R.alphaSum_le_twoE
    have hle :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect b ≤
          (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      calc
        _ = a.lemma814FirstThirdCappedDefect b +
              (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := add_comm _ _
        _ ≤ (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) +
              (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) :=
          add_le_add_left hdefect _
        _ = (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
              (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) :=
          add_comm _ _
        _ ≤ _ := hsum
    exact (not_lt_of_ge hle) A.defectSum_strict
  · exact (not_lt_of_ge R.alphaSum_le_twoE) (B.laterAlphaSum_strict hfour)
  · exact (ne_of_lt C.secondFourthOrders_lt) hsecondFourth

/-- If the unary capped first-three defect is the first alpha, none of the
three exceptional alternatives in Lemma 8.14 can occur.  This is the
arithmetic core of the fifth alternative in Lemma 9.1; the strict comparison
with the full source alpha is used earlier in the paper to obtain this unary
capped-defect equality. -/
theorem not_lemma814Exceptional_of_firstThirdDefect_eq_firstAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hdefect : a.lemma814FirstThirdCappedDefect b =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    ¬a.Beli2019Lemma814Exceptional b := by
  rintro (A | B | C)
  · have houter :
        a.order (remark87PreviousValue (0 : Fin (N + 1))) =
          a.order (remark87NextValue (0 : Fin (N + 1))) := by
      change a.order (0 : Fin (N + 3)) =
        a.order (2 : Fin (N + 3))
      exact A.firstThirdOrders_eq
    have R := a.beli2019Remark87 (0 : Fin (N + 1)) houter
    have hsum :
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
          ((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) := by
      change ((a.alphaValue (0 : Fin (N + 2)) +
        a.alphaValue (1 : Fin (N + 2)) : ℚ) : WithTop ℚ) ≤
          ((2 * (ramificationIndex K : ℚ)) : WithTop ℚ)
      exact WithTop.coe_le_coe.mpr R.alphaSum_le_twoE
    have hle :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect b ≤
          ((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) := by
      rw [hdefect]
      simpa only [add_comm] using hsum
    exact (not_lt_of_ge hle) A.defectSum_strict
  · have houter :
        a.order (remark87PreviousValue (0 : Fin (N + 1))) =
          a.order (remark87NextValue (0 : Fin (N + 1))) := by
      change a.order (0 : Fin (N + 3)) =
        a.order (2 : Fin (N + 3))
      exact B.firstThirdOrders_eq
    have R := a.beli2019Remark87 (0 : Fin (N + 1)) houter
    have hsumTop := B.defectSum_eq
    rw [hdefect] at hsumTop
    have hsum :
        a.alphaValue (0 : Fin (N + 2)) +
            a.alphaValue (1 : Fin (N + 2)) =
          2 * (ramificationIndex K : ℚ) := by
      apply WithTop.coe_eq_coe.mp
      change
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
          (((2 : ℚ) * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
      simpa only [add_comm] using hsumTop
    have hhalf := R.alphaSum_eq_twoE_iff.mp hsum
    change a.alphaValue (0 : Fin (N + 2)) =
      a.halfGapValue (0 : Fin (N + 2)) at hhalf
    exact (ne_of_lt B.firstAlpha_strict) hhalf
  · have houter :
        a.order (remark87PreviousValue (0 : Fin (N + 1))) =
          a.order (remark87NextValue (0 : Fin (N + 1))) := by
      change a.order (0 : Fin (N + 3)) =
        a.order (2 : Fin (N + 3))
      exact C.firstThirdOrders_eq
    have R := a.beli2019Remark87 (0 : Fin (N + 1)) houter
    have hthirdBound : 2 < N + 2 := by
      have hfour := C.rank_four
      omega
    let third : Fin (N + 2) := ⟨2, hthirdBound⟩
    have hCdefect : a.lemma814FirstThirdCappedDefect b =
        (a.alphaValue third : WithTop ℚ) :=
      C.firstThirdDefect_eq_alpha
    have hfirstThirdTop :
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) =
          (a.alphaValue third : WithTop ℚ) :=
      hdefect.symm.trans hCdefect
    have hfirstThird :
        a.alphaValue (0 : Fin (N + 2)) =
          a.alphaValue third :=
      WithTop.coe_eq_coe.mp hfirstThirdTop
    have hsecondThirdSum :
        a.alphaValue (1 : Fin (N + 2)) +
            a.alphaValue third =
          2 * (ramificationIndex K : ℚ) := by
      have hsecondComplement : a.alphaValue (1 : Fin (N + 2)) =
          (ramificationIndex K : ℚ) -
            (a.orderGap third : ℚ) / 2 := by
        simpa only [lemma814ThirdComplementaryDefect] using
          C.secondAlpha_eq_complement
      have hthirdFormula : a.alphaValue third =
          (a.orderGap third : ℚ) / 2 +
            (ramificationIndex K : ℚ) := by
        calc
          a.alphaValue third = a.halfGapValue third :=
            C.thirdAlpha_eq_halfGap
          _ = _ := rfl
      rw [hsecondComplement, hthirdFormula]
      ring
    have hfirstSecondSum :
        a.alphaValue (0 : Fin (N + 2)) +
            a.alphaValue (1 : Fin (N + 2)) =
          2 * (ramificationIndex K : ℚ) := by
      rw [hfirstThird, add_comm]
      exact hsecondThirdSum
    have hhalf := R.alphaSum_eq_twoE_iff.mp hfirstSecondSum
    change a.alphaValue (0 : Fin (N + 2)) =
      a.halfGapValue (0 : Fin (N + 2)) at hhalf
    exact (ne_of_lt
      (a.firstAlpha_lt_halfGap_of_lemma814ExceptionC b C)) hhalf

/-- Passing from the full source BONG to its unary first segment removes the
source alpha cap.  If the full capped defect is the target first alpha and is
strictly below the source first alpha, the unary capped defect is therefore
exactly the target first alpha. -/
theorem lemma814FirstThirdCappedDefect_eq_firstAlpha_of_fullSource
    {X : Type x} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {P : Lattice K X} {S : Nat}
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (b : GoodBONG s P 1)
    (hprefix : b.prefixProduct 1 = c.prefixProduct 1)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (hstrict : a.alphaValue (0 : Fin (N + 2)) <
      c.alphaValue (0 : Fin (S + 1))) :
    a.lemma814FirstThirdCappedDefect b =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
  have hfull' := hfull
  unfold truncatedPrefixDefect at hfull'
  rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hfull'
  have hsourceIndex : (⟨0, by omega⟩ : Fin (S + 1)) =
      (0 : Fin (S + 1)) := by
    apply Fin.ext
    rfl
  rw [hsourceIndex, ← min_assoc] at hfull'
  have hstrictTop :
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
    exact_mod_cast hstrict
  have hleft := left_eq_of_min_eq_of_lt_right hfull' hstrictTop
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [b.prefixAlphaCap_last, min_top_right, hprefix]
  exact hleft

/-- The canonical prefix witness generated by the first vector of a full
source good BONG. -/
noncomputable def firstUnaryPrefixWitness
    (c : GoodBONG r M (S + 2)) :=
  c.toBONG.prefixWitness 1 (by omega)

/-- The canonical rank-one segment generated by the first vector of a full
source good BONG. -/
noncomputable def firstUnarySegment
    (c : GoodBONG r M (S + 2)) :=
  c.firstUnaryPrefixWitness.toSegmentWitness.toGoodBONG c.good

/-- The canonical unary segment carries the same first value unit as the
full source BONG. -/
@[simp]
theorem firstUnarySegment_valueUnit_zero
    (c : GoodBONG r M (S + 2)) :
    c.firstUnarySegment.valueUnit (0 : Fin 1) =
      c.valueUnit (0 : Fin (S + 2)) := by
  let segment := c.firstUnaryPrefixWitness.toSegmentWitness
  change segment.bong.valueUnit (0 : Fin 1) =
    c.toBONG.valueUnit (0 : Fin (S + 2))
  rw [segment.valueUnit_eq]
  congr 1

/-- The canonical unary segment has the same first prefix product as the
full source BONG. -/
theorem firstUnarySegment_prefixProduct_one
    (c : GoodBONG r M (S + 2)) :
    c.firstUnarySegment.prefixProduct 1 = c.prefixProduct 1 := by
  let segment := c.firstUnaryPrefixWitness.toSegmentWitness
  change segment.bong.prefixProduct 1 = c.toBONG.prefixProduct 1
  rw [segment.bong.prefixProduct_succ 0 (by omega),
    c.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul, segment.valueUnit_eq]
  congr 1

/-- The first order of the canonical unary segment is the first order of the
full source BONG. -/
@[simp]
theorem firstUnarySegment_order_zero
    (c : GoodBONG r M (S + 2)) :
    c.firstUnarySegment.order (0 : Fin 1) =
      c.order (0 : Fin (S + 2)) := by
  let segment := c.firstUnaryPrefixWitness.toSegmentWitness
  change segment.bong.order (0 : Fin 1) =
    c.toBONG.order (0 : Fin (S + 2))
  rw [segment.order_eq]
  congr 1

/-- The fifth alternative of Lemma 9.1, stated with the full source BONG.
The strict full-source alpha comparison removes the source cap; the completed
Lemma 8.14 then supplies the prescribed first value. -/
theorem beli2019Lemma91_of_fullSource_firstThirdDefect
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
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (horder : a.order (0 : Fin (N + 3)) =
      c.firstUnarySegment.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions c.firstUnarySegment)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (hstrict : a.alphaValue (0 : Fin (N + 2)) <
      c.alphaValue (0 : Fin (S + 1))) :
    Nonempty
      (a.Beli2019PrescribedFirstValueTransform c.firstUnarySegment) := by
  have hdefect :=
    a.lemma814FirstThirdCappedDefect_eq_firstAlpha_of_fullSource
      c c.firstUnarySegment c.firstUnarySegment_prefixProduct_one
        hfull hstrict
  have hnotExceptional :=
    a.not_lemma814Exceptional_of_firstThirdDefect_eq_firstAlpha
      c.firstUnarySegment hdefect
  exact (a.beli2019Lemma814Explicit
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    c.firstUnarySegment horder conditions).mpr hnotExceptional

/-- When the first order gap is `2e`, the prescribed multiplier has defect
at least `2e`.  The first adjacent product has even order and hence positive
defect, so the defect-sum criterion makes their Hilbert symbol one. -/
theorem lemma814Epsilon_firstAdjacent_hilbert_one_of_firstGap_eq_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (hgap : a.orderGap (0 : Fin (N + 2)) =
      2 * (ramificationIndex K : Int)) :
    hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin (N + 2))) = 1 := by
  have halpha : a.alphaValue (0 : Fin (N + 2)) =
      2 * (ramificationIndex K : ℚ) :=
    (a.beli2009Corollary28_ii (0 : Fin (N + 2))).2.1.mpr hgap
  have hepsilonLower := a.alpha_le_lemma814EpsilonDefect b conditions
  have htwoELower :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (a.lemma814Epsilon b) := by
    have hcast :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
          (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
      rw [halpha]
      norm_cast
    rw [hcast]
    exact hepsilonLower
  have hadjacentOrder :
      ordUnit K (a.adjacentProduct (0 : Fin (N + 2))) =
        a.order (0 : Fin (N + 3)) + a.order (1 : Fin (N + 3)) := by
    have horderUnit (j : Fin (N + 3)) :
        ordUnit K (a.valueUnit j) = a.order j :=
      (a.toBONG.order_eq_ordUnit j).symm
    unfold adjacentProduct
    rw [ordUnit_neg, ordUnit_mul, horderUnit, horderUnit]
    congr 1
  have hadjacentEven :
      Even (ordUnit K (a.adjacentProduct (0 : Fin (N + 2)))) := by
    rw [hadjacentOrder]
    have hgap' := hgap
    unfold orderGap at hgap'
    change a.order (1 : Fin (N + 3)) -
      a.order (0 : Fin (N + 3)) =
        2 * (ramificationIndex K : Int) at hgap'
    refine ⟨a.order (0 : Fin (N + 3)) +
      (ramificationIndex K : Int), ?_⟩
    omega
  have hadjacentDefectNonzero :
      quadraticDefect K (a.adjacentProduct (0 : Fin (N + 2))) ≠ 0 :=
    BONG.quadraticDefect_ne_zero_of_even_ordUnit
      (a.adjacentProduct (0 : Fin (N + 2))) hadjacentEven
  have hadjacentDefectPositive :
      (0 : WithTop ℚ) <
        defectOrder (K := K) (a.adjacentProduct (0 : Fin (N + 2))) := by
    have horderDefectNonzero :
        defectOrder (K := K)
            (a.adjacentProduct (0 : Fin (N + 2))) ≠ 0 := by
      intro hzero
      exact hadjacentDefectNonzero
        (quadraticDefect_eq_zero_of_defectOrder_eq_zero
          (a.adjacentProduct (0 : Fin (N + 2))) hzero)
    exact lt_of_le_of_ne
      (defectOrder_nonneg (a.adjacentProduct (0 : Fin (N + 2))))
      horderDefectNonzero.symm
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  let twoE : WithTop ℚ :=
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
  let adjacentDefect : WithTop ℚ :=
    defectOrder (K := K) (a.adjacentProduct (0 : Fin (N + 2)))
  have hstrict : twoE < twoE + adjacentDefect := by
    by_cases htop : adjacentDefect = ⊤
    · simp [htop, twoE]
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      have hdPositive : (0 : ℚ) < d := by
        change (0 : WithTop ℚ) < adjacentDefect at hadjacentDefectPositive
        rw [← hd] at hadjacentDefectPositive
        exact_mod_cast hadjacentDefectPositive
      rw [← hd]
      dsimp only [twoE]
      change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (((2 * ramificationIndex K : Nat) : ℚ) + d : ℚ)
      exact_mod_cast (lt_add_of_pos_right
        ((2 * ramificationIndex K : Nat) : ℚ) hdPositive)
  have hmonotone := add_le_add_right htwoELower adjacentDefect
  exact hstrict.trans_le (by
    simpa only [twoE, adjacentDefect, add_comm] using hmonotone)

/-- The `R₂ - R₁ = 2e` branch of Lemma 9.1 is a direct binary
scaling: the first alpha attains its half-gap, and the preceding Hilbert
calculation places the prescribed multiplier in the first binary norm
group. -/
theorem beli2019Lemma91_of_firstGap_eq_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hgap : a.orderGap (0 : Fin (N + 2)) =
      2 * (ramificationIndex K : Int)) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have halpha : a.alphaValue (0 : Fin (N + 2)) =
      2 * (ramificationIndex K : ℚ) :=
    (a.beli2009Corollary28_ii (0 : Fin (N + 2))).2.1.mpr hgap
  have hhalf : a.AttainsHalfGap (0 : Fin (N + 2)) := by
    unfold AttainsHalfGap halfGapValue
    rw [halpha, hgap]
    push_cast
    ring
  have hbinary := a.firstBinaryAlpha_eq_alpha_of_halfGap hhalf
  have hhilbert :=
    a.lemma814Epsilon_firstAdjacent_hilbert_one_of_firstGap_eq_twoE
      b conditions hgap
  exact a.beli2019Lemma814_binaryBranch
    b horder conditions hbinary hhilbert

/-- The two immediate order cases in Lemma 9.1 produce a good BONG whose
first value is the prescribed unary value. -/
theorem beli2019Lemma91_of_firstThird_lt_or_secondFourth_eq
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
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hcase :
      a.order (0 : Fin (N + 3)) <
          a.order (⟨2, by omega⟩ : Fin (N + 3)) ∨
        ∃ hfour : 4 ≤ N + 3,
          a.order (1 : Fin (N + 3)) =
            a.order (⟨3, by omega⟩ : Fin (N + 3))) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hnotExceptional : ¬a.Beli2019Lemma814Exceptional b := by
    rcases hcase with hfirstThird | ⟨hfour, hsecondFourth⟩
    · exact a.not_lemma814Exceptional_of_firstThird_lt b hfirstThird
    · exact a.not_lemma814Exceptional_of_secondFourth_eq b hfour
        hsecondFourth
  exact (a.beli2019Lemma814Explicit
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    b horder conditions).mpr hnotExceptional

end BONG.GoodBONG

end Bong
