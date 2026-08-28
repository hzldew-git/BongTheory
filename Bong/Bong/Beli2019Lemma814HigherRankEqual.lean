/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankSegments

/-!
# Beli (2019), Lemma 8.14: the `R₃ = R₅` branch

The equality branch applies Corollary 8.9 to the initial five coefficients.
The final alpha is a valuation-unit defect, the numerical alternative (b)
collapses to equality, and Remark 8.7 makes the last ternary form isotropic,
excluding alternative (c).
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The first five ambient coefficients as a consecutive segment. -/
noncomputable def lemma814InitialFiveSegment
    (a : GoodBONG q L (N + 5)) :
    BONG.SegmentWitness a.toBONG 0 5 (by omega) :=
  a.toBONG.segmentWitness 0 5 (by omega)

/-- The first five ambient coefficients, regarded as a good BONG. -/
noncomputable def lemma814InitialFive
    (a : GoodBONG q L (N + 5)) :
    GoodBONG
      (q.restrict a.lemma814InitialFiveSegment.carrier
        a.lemma814InitialFiveSegment.nondegenerate)
      a.lemma814InitialFiveSegment.lattice 5 :=
  a.lemma814InitialFiveSegment.toGoodBONG a.good

/-- Values of the initial five segment are the first five ambient values. -/
theorem lemma814InitialFive_valueUnit_eq
    (a : GoodBONG q L (N + 5)) (i : Fin 5) :
    a.lemma814InitialFive.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let s := a.lemma814InitialFiveSegment
  change s.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    s.bong.valueUnit i = a.toBONG.valueUnit (s.sourceIndex i) :=
      s.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Orders of the initial five segment are the first five ambient orders. -/
theorem lemma814InitialFive_order_eq
    (a : GoodBONG q L (N + 5)) (i : Fin 5) :
    a.lemma814InitialFive.order i = a.order ⟨i.1, by omega⟩ := by
  let s := a.lemma814InitialFiveSegment
  change s.bong.order i = a.toBONG.order ⟨i.1, by omega⟩
  calc
    s.bong.order i = a.toBONG.order (s.sourceIndex i) := s.order_eq i
    _ = a.toBONG.order ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Prefix products through the initial five segment agree with the
ambient prefix products. -/
theorem lemma814InitialFive_prefixProduct_eq
    (a : GoodBONG q L (N + 5)) (k : Nat) (hk : k ≤ 5) :
    a.lemma814InitialFive.prefixProduct k = a.prefixProduct k := by
  induction k with
  | zero =>
      simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
  | succ k ih =>
      have hkFive : k < 5 := by omega
      have hkAmbient : k < N + 5 := by omega
      unfold GoodBONG.prefixProduct
      rw [a.lemma814InitialFive.toBONG.prefixProduct_succ k hkFive,
        a.toBONG.prefixProduct_succ k hkAmbient]
      have ih' := ih (by omega)
      change a.lemma814InitialFive.toBONG.prefixProduct k =
        a.toBONG.prefixProduct k at ih'
      rw [ih']
      congr 1
      exact a.lemma814InitialFive_valueUnit_eq ⟨k, hkFive⟩

/-- The initial five entries localized at one of their four alpha
indices. -/
def lemma814InitialFiveLocalization (i : Fin 4) :
    AlphaLocalizationIndex (N + 4) where
  start := 0
  pivot := i.1
  stop := 4
  start_le_pivot := by omega
  pivot_lt_stop := i.isLt
  stop_lt := by omega

/-- A half-gap alpha is unchanged on passage to the initial five
segment. -/
theorem lemma814InitialFive_alpha_eq_of_attainsHalfGap
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (i : Fin 4)
    (hhalf : a.AttainsHalfGap ⟨i.1, by omega⟩) :
    a.lemma814InitialFive.alphaValue i =
      a.alphaValue ⟨i.1, by omega⟩ := by
  let p := lemma814InitialFiveLocalization (N := N) i
  let s := a.lemma814InitialFiveSegment
  have h := a.segmentAlpha_eq_global_of_attainsHalfGap p s hhalf
  convert h using 1 <;> congr 1

/-- If `R₃ = R₅`, the fourth alpha also attains its half gap. -/
theorem lemma814FourthAlpha_eq_halfGap_of_third_eq_fifth
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) =
      a.halfGapValue (⟨3, by omega⟩ : Fin (N + 4)) := by
  have hthird := D.third_eq_halfGap
  have hsum := D.second_third_sum
  have hordersQ :
      (a.order (⟨2, by omega⟩ : Fin (N + 5)) : ℚ) =
        a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    exact_mod_cast hthirdFifth
  unfold halfGapValue orderGap at hthird ⊢
  change a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      ((a.order (⟨3, by omega⟩ : Fin (N + 5)) -
        a.order (⟨2, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hthird
  change a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) =
      ((a.order (⟨4, by omega⟩ : Fin (N + 5)) -
        a.order (⟨3, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)
  rw [D.fourth_eq_second]
  push_cast at hthird
  push_cast
  linarith

/-- The third local alpha is the third ambient alpha. -/
theorem lemma814InitialFive_thirdAlpha_eq
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega)) :
    a.lemma814InitialFive.alphaValue (2 : Fin 4) =
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) := by
  apply a.lemma814InitialFive_alpha_eq_of_attainsHalfGap
  exact D.third_eq_halfGap

/-- In the equality branch, the final local alpha is the fourth ambient
alpha and hence the second ambient alpha. -/
theorem lemma814InitialFive_finalAlpha_eq_secondAlpha
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    a.lemma814InitialFive.alphaValue (3 : Fin 4) =
      a.alphaValue (1 : Fin (N + 4)) := by
  calc
    a.lemma814InitialFive.alphaValue (3 : Fin 4) =
        a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) := by
      apply a.lemma814InitialFive_alpha_eq_of_attainsHalfGap
      exact a.lemma814FourthAlpha_eq_halfGap_of_third_eq_fifth
        D hthirdFifth
    _ = a.alphaValue (1 : Fin (N + 4)) := D.fourth_eq_second

/-- The final alpha of the initial five segment occurs as the defect of a
valuation unit. -/
theorem lemma814InitialFive_finalAlpha_isValuationUnitDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    IsValuationUnitDefect (K := K)
      (a.lemma814InitialFive.alphaValue (3 : Fin 4)) := by
  rw [a.lemma814InitialFive_finalAlpha_eq_secondAlpha D hthirdFifth]
  exact DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
    _ D.second_odd (a.beli2009Lemma27_i (1 : Fin (N + 4))).1
      D.second_lt_twoE

/-- In the equality branch, the complementary final-gap value of the
initial five segment is exactly the second ambient alpha. -/
theorem lemma814InitialFive_complementaryDefect_eq_thirdAlpha
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    a.lemma814InitialFive.lemma89ComplementaryDefect =
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) := by
  have hthird := D.third_eq_halfGap
  have hordersQ :
      (a.order (⟨2, by omega⟩ : Fin (N + 5)) : ℚ) =
        a.order (⟨4, by omega⟩ : Fin (N + 5)) := by
    exact_mod_cast hthirdFifth
  unfold halfGapValue orderGap at hthird
  unfold lemma89ComplementaryDefect orderGap
  rw [a.lemma814InitialFive_order_eq, a.lemma814InitialFive_order_eq]
  change (ramificationIndex K : ℚ) -
      ((a.order (⟨4, by omega⟩ : Fin (N + 5)) -
        a.order (⟨3, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 =
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 4))
  change a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
      ((a.order (⟨3, by omega⟩ : Fin (N + 5)) -
        a.order (⟨2, by omega⟩ : Fin (N + 5)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hthird
  push_cast at hthird ⊢
  linarith

/-- Corollary 8.9(a) is impossible for the initial five segment. -/
theorem lemma814InitialFive_not_corollary89ExceptionA
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [DyadicUnitDefectSpectrumLaws K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    ¬a.lemma814InitialFive.Beli2019Corollary89ExceptionA := by
  intro A
  exact A (a.lemma814InitialFive_finalAlpha_isValuationUnitDefect
    D hthirdFifth)

/-- Corollary 8.9(b) is impossible because its required strict inequality
becomes `α₃ < α₃`. -/
theorem lemma814InitialFive_not_corollary89ExceptionB
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    ¬a.lemma814InitialFive.Beli2019Corollary89ExceptionB := by
  intro B
  have hstrict := B.previousAlpha_strict (by omega)
  rw [a.lemma814InitialFive_complementaryDefect_eq_thirdAlpha
      D hthirdFifth] at hstrict
  change a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) <
    a.lemma814InitialFive.alphaValue (2 : Fin 4) at hstrict
  rw [a.lemma814InitialFive_thirdAlpha_eq D] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Remark 8.7 supplies the second adjacent-defect bound used for the
terminal ternary form. -/
theorem lemma814ThirdAlpha_le_fourthAdjacentDefect_of_third_eq_fifth
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    (a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) ≤
      a.adjacentDefect (⟨3, by omega⟩ : Fin (N + 4)) := by
  have houter :
      a.order (remark87PreviousValue
        (⟨2, by omega⟩ : Fin (N + 3))) =
      a.order (remark87NextValue
        (⟨2, by omega⟩ : Fin (N + 3))) := by
    convert hthirdFifth using 1 <;> congr 1
  have hremark := a.beli2019Remark87
    (⟨2, by omega⟩ : Fin (N + 3)) houter
  simpa only [remark87PreviousAlpha, remark87CurrentAlpha] using
    hremark.previousAlpha_le_currentRawDefect

/-- The two terminal adjacent defects have sum strictly larger than
`2e`. -/
theorem lemma814LastThreeAdjacentDefect_sum_gt_twoE
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      a.adjacentDefect (⟨3, by omega⟩ : Fin (N + 4)) +
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)) := by
  have hthirdBound :=
    a.lemma814ThirdAlpha_le_fourthAdjacentDefect_of_third_eq_fifth
      hthirdFifth
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
        (a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) := by
    exact_mod_cast D.second_third_sum.symm.trans (add_comm _ _)
  rw [hsumTop]
  have hstep :
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        (a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) : WithTop ℚ) +
          a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)) :=
    (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mpr hsecondStrict
  exact hstep.trans_le (add_le_add hthirdBound le_rfl)

/-- The terminal three unit coefficients of the initial five segment,
listed in the reverse order used by Corollary 8.9. -/
noncomputable def lemma814InitialFiveLastThreeUnits
    (a : GoodBONG q L (N + 5)) : Fin 3 → Kˣ :=
  fun i ↦ a.lemma814InitialFive.valueUnit
    (Fin.rev (⟨i.1, by omega⟩ : Fin 5))

/-- The first reversed adjacent product is the fourth ambient adjacent
product. -/
theorem lemma814InitialFiveLastThreeUnits_firstProduct_eq
    (a : GoodBONG q L (N + 5)) :
    -(a.lemma814InitialFiveLastThreeUnits (0 : Fin 3) *
        a.lemma814InitialFiveLastThreeUnits (1 : Fin 3)) =
      a.adjacentProduct (⟨3, by omega⟩ : Fin (N + 4)) := by
  apply Units.ext
  simp only [lemma814InitialFiveLastThreeUnits, Units.val_neg,
    Units.val_mul, a.lemma814InitialFive_valueUnit_eq]
  unfold adjacentProduct
  simp only [Units.val_neg, Units.val_mul]
  change -((a.valueUnit (⟨4, by omega⟩ : Fin (N + 5)) : K) *
      (a.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) : K)) =
    -((a.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) : K) *
      (a.valueUnit (⟨4, by omega⟩ : Fin (N + 5)) : K))
  ring

/-- The second reversed adjacent product is the third ambient adjacent
product. -/
theorem lemma814InitialFiveLastThreeUnits_secondProduct_eq
    (a : GoodBONG q L (N + 5)) :
    -(a.lemma814InitialFiveLastThreeUnits (1 : Fin 3) *
        a.lemma814InitialFiveLastThreeUnits (2 : Fin 3)) =
      a.adjacentProduct (⟨2, by omega⟩ : Fin (N + 4)) := by
  apply Units.ext
  simp only [lemma814InitialFiveLastThreeUnits, Units.val_neg,
    Units.val_mul, a.lemma814InitialFive_valueUnit_eq]
  unfold adjacentProduct
  simp only [Units.val_neg, Units.val_mul]
  change -((a.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) : K) *
      (a.valueUnit (⟨2, by omega⟩ : Fin (N + 5)) : K)) =
    -((a.valueUnit (⟨2, by omega⟩ : Fin (N + 5)) : K) *
      (a.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) : K))
  ring

/-- The terminal adjacent products have Hilbert symbol one. -/
theorem lemma814LastThreeAdjacentHilbert_eq_one
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    hilbertSymbol K
        (a.adjacentProduct (⟨3, by omega⟩ : Fin (N + 4)))
        (a.adjacentProduct (⟨2, by omega⟩ : Fin (N + 4))) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  simpa only [adjacentDefect] using
    a.lemma814LastThreeAdjacentDefect_sum_gt_twoE
      D hsecondStrict hthirdFifth

/-- The last three coefficients of the initial five segment form an
isotropic ternary diagonal form. -/
theorem lemma814InitialFive_lastThree_isotropic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5)))
    (hthree : 3 ≤ 5) :
    DiagonalIsotropic
      (a.lemma814InitialFive.lemma89LastThreeValues hthree) := by
  let c := a.lemma814InitialFiveLastThreeUnits
  have hhilbert :
      hilbertSymbol K (-(c (0 : Fin 3) * c (1 : Fin 3)))
        (-(c (1 : Fin 3) * c (2 : Fin 3))) = 1 := by
    rw [a.lemma814InitialFiveLastThreeUnits_firstProduct_eq,
      a.lemma814InitialFiveLastThreeUnits_secondProduct_eq]
    exact a.lemma814LastThreeAdjacentHilbert_eq_one
      D hsecondStrict hthirdFifth
  have hisotropic :
      DiagonalIsotropic (diagonalUnitCoefficients c) :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne c).mpr hhilbert
  convert hisotropic using 1
  funext i
  change a.lemma814InitialFive.value
      (Fin.rev ⟨i.1, i.2.trans_le hthree⟩) =
    (a.lemma814InitialFive.valueUnit
      (Fin.rev (⟨i.1, by omega⟩ : Fin 5)) : K)
  rw [a.lemma814InitialFive.coe_valueUnit]

/-- Corollary 8.9(c) is impossible because its terminal anisotropy clause
contradicts the preceding isotropy theorem. -/
theorem lemma814InitialFive_not_corollary89ExceptionC
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    ¬a.lemma814InitialFive.Beli2019Corollary89ExceptionC := by
  intro E
  rcases a.lemma814InitialFive_lastThree_isotropic D hsecondStrict
      hthirdFifth E.rank_three with ⟨x, hx, hzero⟩
  exact hx (E.lastThree_anisotropic x hzero)

/-- Corollary 8.9 therefore changes the fifth value of the initial
five-dimensional segment by a unit of defect `α₂`. -/
theorem exists_lemma814InitialFiveLastValueTransform
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
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty a.lemma814InitialFive.Beli2019LastValueTransform := by
  apply a.lemma814InitialFive.beli2019Corollary89
  rintro ⟨_hhalf, E⟩
  rcases E with A | B | C'
  · exact a.lemma814InitialFive_not_corollary89ExceptionA
      D hthirdFifth A
  · rcases B with ⟨B⟩
    exact a.lemma814InitialFive_not_corollary89ExceptionB
      D hthirdFifth B
  · rcases C' with ⟨C'⟩
    exact a.lemma814InitialFive_not_corollary89ExceptionC
      D hsecondStrict hthirdFifth C'

/-- The ambient change obtained by inserting the transformed initial five
segment.  The first-four determinant is recorded modulo an explicit
square. -/
structure Beli2019Lemma814InitialFiveScalingData
    (a : GoodBONG q L (N + 5)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)
  transformed : GoodBONG q L (N + 5)
  prefixProduct_four_eq_mul_inv_square : ∃ p : Kˣ,
    transformed.prefixProduct 4 =
      epsilon⁻¹ * a.prefixProduct 4 * p ^ 2

/-- Insert a chosen Corollary 8.9 transformation into the ambient BONG
and compute the resulting first-four determinant square class. -/
theorem lemma814InitialFiveScalingData_of_transform
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5)))
    (T : a.lemma814InitialFive.Beli2019LastValueTransform) :
    Nonempty a.Beli2019Lemma814InitialFiveScalingData := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814InitialFiveSegment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 5) :=
    ⟨replacement.bong, replacement.good⟩
  have hinsValue (i : Fin 5) :
      transformed.valueUnit ⟨i.1, by omega⟩ =
        T.transformed.valueUnit i := by
    apply Units.ext
    change replacement.bong.value ⟨i.1, by omega⟩ =
      T.transformed.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector ⟨i.1, by omega⟩) =
      q.quadratic (T.transformed.toBONG.ambientVector i : V)
    simpa only [Nat.zero_add] using congrArg q.quadratic
      (replacement.inside_eq i)
  have hprefix (k : Nat) (hk : k ≤ 5) :
      transformed.prefixProduct k = T.transformed.prefixProduct k := by
    induction k with
    | zero =>
        simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
    | succ k ih =>
        have hkFive : k < 5 := by omega
        have hkAmbient : k < N + 5 := by omega
        unfold GoodBONG.prefixProduct
        rw [transformed.toBONG.prefixProduct_succ k hkAmbient,
          T.transformed.toBONG.prefixProduct_succ k hkFive]
        have ih' := ih (by omega)
        change transformed.toBONG.prefixProduct k =
          T.transformed.toBONG.prefixProduct k at ih'
        rw [ih']
        congr 1
        exact hinsValue ⟨k, hkFive⟩
  rcases BONG.exists_valueProduct_eq_mul_square
      a.lemma814InitialFive.toBONG T.transformed.toBONG with ⟨p, hp⟩
  have hpPrefix : T.transformed.prefixProduct 5 =
      a.lemma814InitialFive.prefixProduct 5 * p ^ 2 := by
    rw [T.transformed.prefixProduct_eq_valueProduct_of_rank_le 5 le_rfl,
      a.lemma814InitialFive.prefixProduct_eq_valueProduct_of_rank_le 5 le_rfl]
    exact hp
  have hlast : T.transformed.valueUnit (4 : Fin 5) =
      T.epsilon * a.lemma814InitialFive.valueUnit (4 : Fin 5) := by
    convert T.lastValue_eq using 1 <;> congr 1
  change T.transformed.toBONG.valueUnit (4 : Fin 5) =
    T.epsilon * a.lemma814InitialFive.toBONG.valueUnit (4 : Fin 5) at hlast
  unfold GoodBONG.prefixProduct at hpPrefix
  rw [T.transformed.toBONG.prefixProduct_succ 4 (by omega),
    a.lemma814InitialFive.toBONG.prefixProduct_succ 4 (by omega)] at hpPrefix
  change T.transformed.toBONG.prefixProduct 4 *
      T.transformed.toBONG.valueUnit (4 : Fin 5) =
    a.lemma814InitialFive.toBONG.prefixProduct 4 *
      a.lemma814InitialFive.toBONG.valueUnit (4 : Fin 5) * p ^ 2 at hpPrefix
  rw [hlast] at hpPrefix
  change T.transformed.prefixProduct 4 *
      (T.epsilon * a.lemma814InitialFive.valueUnit (4 : Fin 5)) =
    a.lemma814InitialFive.prefixProduct 4 *
      a.lemma814InitialFive.valueUnit (4 : Fin 5) * p ^ 2 at hpPrefix
  have hlocalFour : T.transformed.prefixProduct 4 =
      T.epsilon⁻¹ * a.lemma814InitialFive.prefixProduct 4 * p ^ 2 := by
    calc
      T.transformed.prefixProduct 4 =
          (T.transformed.prefixProduct 4 *
              (T.epsilon * a.lemma814InitialFive.valueUnit (4 : Fin 5))) *
            (T.epsilon *
              a.lemma814InitialFive.valueUnit (4 : Fin 5))⁻¹ := by
        group
      _ = ((a.lemma814InitialFive.prefixProduct 4 *
              a.lemma814InitialFive.valueUnit (4 : Fin 5)) * p ^ 2) *
            (T.epsilon *
              a.lemma814InitialFive.valueUnit (4 : Fin 5))⁻¹ := by
        rw [hpPrefix]
      _ = T.epsilon⁻¹ *
          a.lemma814InitialFive.prefixProduct 4 * p ^ 2 := by
        rw [mul_inv_rev]
        calc
          (a.lemma814InitialFive.prefixProduct 4 *
                a.lemma814InitialFive.valueUnit (4 : Fin 5) * p ^ 2) *
              ((a.lemma814InitialFive.valueUnit (4 : Fin 5))⁻¹ *
                T.epsilon⁻¹) =
              (a.lemma814InitialFive.valueUnit (4 : Fin 5) *
                  (a.lemma814InitialFive.valueUnit (4 : Fin 5))⁻¹) *
                (T.epsilon⁻¹ *
                  a.lemma814InitialFive.prefixProduct 4 * p ^ 2) := by
            ac_rfl
          _ = T.epsilon⁻¹ *
              a.lemma814InitialFive.prefixProduct 4 * p ^ 2 := by
            simp only [mul_inv_cancel, one_mul]
  refine ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := T.epsilon_defect.trans <| congrArg
      (fun x : ℚ ↦ (x : WithTop ℚ)) <|
        a.lemma814InitialFive_finalAlpha_eq_secondAlpha D hthirdFifth
    transformed := transformed
    prefixProduct_four_eq_mul_inv_square := ⟨p, ?_⟩
  }⟩
  rw [hprefix 4 (by omega), hlocalFour,
    a.lemma814InitialFive_prefixProduct_eq 4 (by omega)]

/-- The complete initial-five scaling construction in the equality
branch. -/
theorem exists_lemma814InitialFiveScalingData
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
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hsecondStrict :
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) =
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty a.Beli2019Lemma814InitialFiveScalingData := by
  rcases a.exists_lemma814InitialFiveLastValueTransform
      D hsecondStrict hthirdFifth with ⟨T⟩
  exact a.lemma814InitialFiveScalingData_of_transform D hthirdFifth T

namespace Beli2019Lemma814InitialFiveScalingData

variable {a : GoodBONG q L (N + 5)}

/-- Equal finite defects of the inverse multiplier and the old
quaternary determinant are raised strictly by Lemma 8.1(ii). -/
theorem firstFourRawDefect_lt_of_eq
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    (D : a.Beli2019Lemma814InitialFiveScalingData)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)) :
    (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
      defectOrder (K := K) (D.transformed.prefixProduct 4) := by
  let x := a.prefixProduct 4
  let epsilonInv := D.epsilon⁻¹
  have hepsilonInv : defectOrder (K := K) epsilonInv =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) := by
    dsimp only [epsilonInv]
    rw [defectOrder_inv, D.epsilon_defect]
  have heq : quadraticDefect K epsilonInv = quadraticDefect K x :=
    quadraticDefect_eq_of_defectOrder_eq epsilonInv x
      (hepsilonInv.trans hraw.symm)
  have hfinite : quadraticDefect K epsilonInv ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe epsilonInv
      (a.alphaValue (1 : Fin (N + 4))) hepsilonInv
  have hstrictRaw := beli2019Lemma81_ii_strict hresidueTwo epsilonInv
    x heq hfinite
  have hstrict := defectOrder_lt_of_quadraticDefect_lt
    epsilonInv (epsilonInv * x) hstrictRaw
  rcases D.prefixProduct_four_eq_mul_inv_square with ⟨p, hp⟩
  rw [hp, defectOrder_mul_square]
  exact hepsilonInv ▸ hstrict

/-- After the initial-five scaling, the initial quaternary segment cannot
still satisfy exception (c). -/
theorem initialFour_not_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    (D : a.Beli2019Lemma814InitialFiveScalingData)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (b : GoodBONG r M 1)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)) :
    ¬Beli2019Lemma814ExceptionC
      (D.transformed.lemma814InitialFour (by omega)) b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classification
  have halphas := a.alpha_invariant D.transformed
  have hhalf := a.halfGapValue_invariant
    (classificationV := classification) D.transformed
      (⟨2, by omega⟩ : Fin (N + 4))
  have hthirdHalf : D.transformed.alphaValue
      (⟨2, by omega⟩ : Fin (N + 4)) =
        D.transformed.halfGapValue
          (⟨2, by omega⟩ : Fin (N + 4)) := by
    calc
      D.transformed.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        (halphas _).symm
      _ = a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        A.third_eq_halfGap
      _ = D.transformed.halfGapValue
          (⟨2, by omega⟩ : Fin (N + 4)) := hhalf
  have hbinary :=
    D.transformed.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (⟨2, by omega⟩ : Fin (N + 4)) hthirdHalf
  have hlocalAlphas :=
    D.transformed.lemma814InitialFour_alphas_eq (by omega) hbinary
  intro C
  have hrawTransformed :=
    lemma814FirstFourRawDefect_eq_secondAlpha_of_initialFour_exceptionC
      D.transformed b (by omega) hlocalAlphas C
  have hstrict := D.firstFourRawDefect_lt_of_eq hresidueTwo hraw
  have halphaOne := halphas (1 : Fin (N + 4))
  rw [← halphaOne] at hrawTransformed
  rw [hrawTransformed] at hstrict
  exact (lt_irrefl _ hstrict)

end Beli2019Lemma814InitialFiveScalingData

end BONG.GoodBONG

end Bong
