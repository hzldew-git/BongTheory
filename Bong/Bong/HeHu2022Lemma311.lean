/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma39
import Bong.Bong.HeHu2022Lemma310
import Bong.Bong.Beli2019Lemma86

/-!
# He--Hu (2024), Lemma 3.11

This file computes the complete `R_i` profiles of the explicit maximal-lattice
candidates in Table 2.  The proof follows the published proof literally:
the tail blocks come from Lemma 3.9, and Lemma 3.10 prepends the alternating
`0,-2e` hyperbolic pairs without changing any tail order.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A good BONG whose first order is nonnegative is integral. -/
theorem heHuIntegral_of_firstOrder_nonneg {n : Nat}
    (b : GoodBONG q L (n + 1)) (h : 0 ≤ b.order 0) :
    Lattice.IsIntegral q L :=
  (b.toBONG.beliUniversalLemma22).2 h

/-- The exact binary tail used in the nonexceptional unit rows of Table 2.
Its coefficient list is
`<a, -a*c*pi^(1-d)>`; taking `a=1` or `a=c#` gives the two columns. -/
noncomputable def heHuUnitDefectTailValues
    (a c : Kˣ) (d : Int) : Fin 2 → Kˣ :=
  ![a, -(a * c * uniformizerPowerUnit K (1 - d))]

@[simp]
theorem heHuUnitDefectTailValues_zero (a c : Kˣ) (d : Int) :
    heHuUnitDefectTailValues (K := K) a c d 0 = a := by
  rfl

@[simp]
theorem heHuUnitDefectTailValues_one (a c : Kˣ) (d : Int) :
    heHuUnitDefectTailValues (K := K) a c d 1 =
      -(a * c * uniformizerPowerUnit K (1 - d)) := by
  rfl

theorem heHuUnitDefectTail_parameter (a c : Kˣ) (d : Int) :
    heHuUnitDefectTailValues (K := K) a c d 1 /
        heHuUnitDefectTailValues (K := K) a c d 0 =
      -(c * uniformizerPowerUnit K (1 - d)) := by
  apply Units.ext
  simp [heHuUnitDefectTailValues]
  field_simp

theorem heHuUnitDefectTail_negativeParameter_defect
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int) (hdOdd : Odd d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    defectOrder (K := K)
        (-(heHuUnitDefectTailValues (K := K) a c d 1 /
          heHuUnitDefectTailValues (K := K) a c d 0)) =
      (((d : Int) : ℚ) : WithTop ℚ) := by
  rw [heHuUnitDefectTail_parameter]
  simp only [neg_neg]
  have heven : Even (1 - d) := odd_one.sub_odd hdOdd
  rcases isSquare_uniformizerPowerUnit_of_even (K := K) (1 - d) heven with
    ⟨s, hs⟩
  rw [hs, ← pow_two s, defectOrder_mul_square, hcDefect]

theorem heHuUnitDefectTail_admissible
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (_ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (_hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (heHuUnitDefectTailValues (K := K) a c d 1 /
        heHuUnitDefectTailValues (K := K) a c d 0) := by
  let t := heHuUnitDefectTailValues (K := K) a c d 1 /
    heHuUnitDefectTailValues (K := K) a c d 0
  have ht : t = -(c * uniformizerPowerUnit K (1 - d)) :=
    heHuUnitDefectTail_parameter a c d
  have hc0 := (isValuationUnit_iff_ordUnit_eq_zero K c).1 hc
  have hord : ordUnit K t = 1 - d := by
    rw [ht, ordUnit_neg, ordUnit_mul, hc0,
      ordUnit_uniformizerPowerUnit]
    omega
  have hdefect : defectOrder (K := K) (-t) =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    dsimp only [t]
    exact heHuUnitDefectTail_negativeParameter_defect
      a c d hdOdd hcDefect
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect t).2
  constructor
  · rw [hord]
    omega
  · apply
      Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    have hnegOrder : ordUnit K (-t) = ordUnit K t := by
      apply WithTop.coe_injective
      simp only [coe_ordUnit, Units.val_neg, ord_neg]
    rw [hnegOrder, hord, hdefect]
    exact_mod_cast (show (0 : ℚ) ≤ ((1 - d : Int) : ℚ) + d by
      push_cast
      norm_num)

/-- Exact good BONG for the generic binary tail in Table 2. -/
noncomputable def heHuUnitDefectTailGoodBONG
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    GoodBONG
      (binaryDiagonalModelSpace
        (heHuUnitDefectTailValues (K := K) a c d 0)
        (heHuUnitDefectTailValues (K := K) a c d 1)
        (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
          hcDefect))
      (binaryDiagonalModelLattice (K := K)) 2 :=
  binaryDiagonalExactGoodBONG
    (heHuUnitDefectTailValues (K := K) a c d 0)
    (heHuUnitDefectTailValues (K := K) a c d 1)
    (heHuUnitDefectTail_admissible a c d ha hc hdOdd hdNonneg hdLt
      hcDefect)

@[simp]
theorem heHuUnitDefectTailGoodBONG_order
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) (i : Fin 2) :
    (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt
      hcDefect).order i = ![0, 1 - d] i := by
  change (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt
    hcDefect).toBONG.order i = _
  rw [BONG.order_eq_ordUnit]
  change ordUnit K
    ((heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt
      hcDefect).valueUnit i) = _
  unfold heHuUnitDefectTailGoodBONG
  rw [binaryDiagonalExactGoodBONG_valueUnit]
  fin_cases i
  · change ordUnit K a = 0
    exact (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha
  · change ordUnit K (-(a * c * uniformizerPowerUnit K (1 - d))) =
      1 - d
    rw [ordUnit_neg, ordUnit_mul, ordUnit_mul,
      ordUnit_uniformizerPowerUnit,
      (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha,
      (isValuationUnit_iff_ordUnit_eq_zero K c).1 hc]
    omega

/-- A binary tail with the alternating endpoint orders produces an entirely
alternating tower. -/
theorem heHuLemma311_allAlternating_of_binaryTail
    (b : GoodBONG q L 2) (hIntegral : Lattice.IsIntegral q L)
    (hzero : b.order 0 = 0)
    (hone : b.order 1 = -(2 * (ramificationIndex K : Int)))
    (k : Nat) :
    ∀ t : Fin (k + 1),
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
  intro t
  by_cases ht : t.val < k
  · let s : Fin k := ⟨t.val, ht⟩
    simpa only [s] using
      Bong.heHu2022Lemma310HyperbolicOrders b hIntegral k s
  · have htk : t.val = k := by omega
    constructor
    · simpa [htk] using
        (Bong.heHu2022Lemma310TailOrders b hIntegral k (0 : Fin 2)).trans hzero
    · simpa [htk] using
        (Bong.heHu2022Lemma310TailOrders b hIntegral k (1 : Fin 2)).trans hone

/-- The prefix/tail form used in every non-pure row of Lemma 3.11. -/
theorem heHuLemma311_binaryTailProfile
    (b : GoodBONG q L 2) (hIntegral : Lattice.IsIntegral q L)
    (k : Nat) :
    (∀ t : Fin k,
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = b.order 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ = b.order 1 := by
  exact ⟨Bong.heHu2022Lemma310HyperbolicOrders b hIntegral k,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 0,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 1⟩

/-- Unary-tail form of Lemma 3.10, used for the first column in odd rank. -/
theorem heHuLemma311_unaryTailProfile
    (b : GoodBONG q L 1) (hIntegral : Lattice.IsIntegral q L)
    (k : Nat) :
    (∀ t : Fin k,
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * k, by omega⟩ = b.order 0 := by
  exact ⟨Bong.heHu2022Lemma310HyperbolicOrders b hIntegral k,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 0⟩

/-- Ternary-tail form of Lemma 3.10, used for the second column in odd
rank. -/
theorem heHuLemma311_ternaryTailProfile
    (b : GoodBONG q L 3) (hIntegral : Lattice.IsIntegral q L)
    (k : Nat) :
    (∀ t : Fin k,
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = b.order 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ = b.order 1 ∧
          (heHu2022Lemma310BONG b hIntegral k).order
            ⟨2 * k + 2, by omega⟩ = b.order 2 := by
  exact ⟨Bong.heHu2022Lemma310HyperbolicOrders b hIntegral k,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 0,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 1,
    Bong.heHu2022Lemma310TailOrders b hIntegral k 2⟩

/-- Four-dimensional tail form of Lemma 3.10, used for
`N_tilde_2^n(1)`. -/
theorem heHuLemma311_fourTailProfile
    (b : GoodBONG q L 4) (hIntegral : Lattice.IsIntegral q L)
    (k : Nat) :
    (∀ t : Fin k,
      (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      ∀ j : Fin 4,
        (heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + j.val, by omega⟩ = b.order j := by
  exact ⟨Bong.heHu2022Lemma310HyperbolicOrders b hIntegral k,
    Bong.heHu2022Lemma310TailOrders b hIntegral k⟩

@[simp]
theorem heHuOrder_orthogonalProductRight_of_orderBounds_left
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m n : Nat}
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (i : Fin n) :
    (b.orthogonalProductRight_of_orderBounds c horder hlastSecond).order
        (BONG.orthogonalProductLeftIndex (m + 1) i) = b.order i := by
  change
    (b.toBONG.orthogonalProductRight c.toBONG horder).order
        (BONG.orthogonalProductLeftIndex (m + 1) i) = b.order i
  exact BONG.order_orthogonalProductRight_left b.toBONG c.toBONG horder i

@[simp]
theorem heHuOrder_orthogonalProductRight_of_orderBounds_right
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} {m n : Nat}
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight_of_orderBounds c horder hlastSecond).order
        (BONG.orthogonalProductRightIndex n j) = c.order j := by
  change
    (b.toBONG.orthogonalProductRight c.toBONG horder).order
        (BONG.orthogonalProductRightIndex n j) = c.order j
  exact BONG.order_orthogonalProductRight_right b.toBONG c.toBONG horder j

/-! ## Lemma 3.11(i): even rank -/

/-- The Table 2 candidate `N_tilde_1^(2k+2)(1)=H^(k+1)`, equipped with
the good BONG used in Lemma 3.11. -/
noncomputable def heHuLemma311EvenFirstOneBONG (k : Nat) :=
  let b := Bong.heHuHyperbolicHeadGoodBONG (K := K)
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [Bong.heHuHyperbolicHeadGoodBONG_order_zero])
  Bong.heHu2022Lemma310BONG b hIntegral k

/-- Lemma 3.11(i), first-column `c=1` row. -/
theorem heHu2022Lemma311iFirstOne (k : Nat) :
    ∀ t : Fin (k + 1),
      (heHuLemma311EvenFirstOneBONG (K := K) k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHuLemma311EvenFirstOneBONG (K := K) k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
  unfold heHuLemma311EvenFirstOneBONG
  apply heHuLemma311_allAlternating_of_binaryTail
  · exact Bong.heHuHyperbolicHeadGoodBONG_order_zero (K := K)
  · exact Bong.heHuHyperbolicHeadGoodBONG_order_one (K := K)

/-- The Table 2 candidate
`N_tilde_1^(2k+2)(Delta)=H^k ⊥ 2^-1 A(2,2rho)`. -/
noncomputable def heHuLemma311EvenFirstDeltaBONG
    [DyadicDiscriminantClassLaws K] (k : Nat) :=
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuDiscriminantEndpointGoodBONG_order]
    norm_num)
  Bong.heHu2022Lemma310BONG b hIntegral k

/-- Lemma 3.11(i), first-column `c=Delta` row. -/
theorem heHu2022Lemma311iFirstDelta
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    ∀ t : Fin (k + 1),
      (heHuLemma311EvenFirstDeltaBONG (K := K) k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHuLemma311EvenFirstDeltaBONG (K := K) k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
  unfold heHuLemma311EvenFirstDeltaBONG
  apply heHuLemma311_allAlternating_of_binaryTail
  · simpa using
      heHuDiscriminantEndpointGoodBONG_order (K := K) 0 (0 : Fin 2)
  · simpa using
      heHuDiscriminantEndpointGoodBONG_order (K := K) 0 (1 : Fin 2)

/-- The products of the two binary endpoint tests differ by the
distinguished discriminant class times an explicit square. -/
theorem heHuEvenFirstEndpoint_prefixProducts_eq_discriminant_mul_square
    [laws : DyadicDiscriminantClassLaws K] :
    (Bong.heHuHyperbolicHeadGoodBONG (K := K)).prefixProduct 2 *
        (heHuDiscriminantEndpointGoodBONG (K := K) 0).prefixProduct 2 =
      laws.discriminantUnit *
        uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int))) ^ 2 := by
  unfold GoodBONG.prefixProduct
  rw [BONG.prefixProduct_succ _ 1 (by omega),
    BONG.prefixProduct_succ _ 0 (by omega),
    BONG.prefixProduct_succ _ 1 (by omega),
    BONG.prefixProduct_succ _ 0 (by omega),
    BONG.prefixProduct_zero, BONG.prefixProduct_zero]
  simp only [one_mul]
  change
    ((Bong.heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 0 *
        (Bong.heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 1) *
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0).valueUnit 0 *
        (heHuDiscriminantEndpointGoodBONG (K := K) 0).valueUnit 1) = _
  rw [Bong.heHuHyperbolicHeadGoodBONG_value_zero,
    Bong.heHuHyperbolicHeadGoodBONG_value_one,
    heHuDiscriminantEndpointGoodBONG_valueUnit,
    heHuDiscriminantEndpointGoodBONG_valueUnit]
  simp [heHuDiscriminantEndpointValues, pow_two]
  simp [uniformizerPowerUnit]
  ac_rfl

/-- The two binary endpoint tests have different determinant square
classes. -/
theorem heHuEvenFirstEndpoint_prefixProducts_not_isSquare
    [laws : DyadicDiscriminantClassLaws K] :
    ¬IsSquare
      ((Bong.heHuHyperbolicHeadGoodBONG (K := K)).prefixProduct 2 *
        (heHuDiscriminantEndpointGoodBONG (K := K) 0).prefixProduct 2) := by
  intro hsquare
  rw [heHuEvenFirstEndpoint_prefixProducts_eq_discriminant_mul_square]
      at hsquare
  let U := uniformizerPowerUnit K
    (-(2 * (ramificationIndex K : Int)))
  have hU2 : IsSquare (U ^ 2) := ⟨U, by simp only [pow_two]⟩
  have hdelta : IsSquare laws.discriminantUnit := by
    have hquotient := hsquare.div hU2
    have hcancel : (laws.discriminantUnit * U ^ 2) / U ^ 2 =
        laws.discriminantUnit := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero U]
    rw [hcancel] at hquotient
    exact hquotient
  have htop := quadraticDefect_eq_top_of_isSquare (K := K) hdelta
  rw [laws.discriminant_defect] at htop
  exact ENat.coe_ne_top (2 * ramificationIndex K) htop

/-- Prepending any number of hyperbolic planes preserves the separation of
the square and discriminant test classes. -/
theorem heHuLemma311EvenFirst_prefixProducts_not_isSquare
    [laws : DyadicDiscriminantClassLaws K] (k : Nat) :
    ¬IsSquare
      ((heHuLemma311EvenFirstOneBONG (K := K) k).prefixProduct
          (2 + 2 * k) *
        (heHuLemma311EvenFirstDeltaBONG (K := K) k).prefixProduct
          (2 + 2 * k)) := by
  unfold heHuLemma311EvenFirstOneBONG
    heHuLemma311EvenFirstDeltaBONG
  exact Bong.heHu2022Lemma310_fullProduct_notSquare_of_tailProduct_notSquare
    (Bong.heHuHyperbolicHeadGoodBONG (K := K))
    (heHuDiscriminantEndpointGoodBONG (K := K) 0)
    (heHuIntegral_of_firstOrder_nonneg
      (Bong.heHuHyperbolicHeadGoodBONG (K := K)) (by
        rw [Bong.heHuHyperbolicHeadGoodBONG_order_zero]))
    (heHuIntegral_of_firstOrder_nonneg
      (heHuDiscriminantEndpointGoodBONG (K := K) 0) (by
        rw [heHuDiscriminantEndpointGoodBONG_order]
        norm_num))
    k heHuEvenFirstEndpoint_prefixProducts_not_isSquare

/-- The Table 2 candidate
`N_tilde_2^(2k+2)(Delta)=H^k ⊥ 2^-1*pi*A(2,2rho)`. -/
noncomputable def heHuLemma311EvenSecondDeltaBONG
    [DyadicDiscriminantClassLaws K] (k : Nat) :=
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 1
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuDiscriminantEndpointGoodBONG_order]
    norm_num)
  Bong.heHu2022Lemma310BONG b hIntegral k

/-- Lemma 3.11(i), second-column `c=Delta` row. -/
theorem heHu2022Lemma311iSecondDelta
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    (∀ t : Fin k,
      (heHuLemma311EvenSecondDeltaBONG (K := K) k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (heHuLemma311EvenSecondDeltaBONG (K := K) k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (heHuLemma311EvenSecondDeltaBONG (K := K) k).order
          ⟨2 * k, by omega⟩ = 1 ∧
        (heHuLemma311EvenSecondDeltaBONG (K := K) k).order
          ⟨2 * k + 1, by omega⟩ =
            1 - 2 * (ramificationIndex K : Int) := by
  unfold heHuLemma311EvenSecondDeltaBONG
  have h := heHuLemma311_binaryTailProfile
    (heHuDiscriminantEndpointGoodBONG (K := K) 1)
    (heHuIntegral_of_firstOrder_nonneg
      (heHuDiscriminantEndpointGoodBONG (K := K) 1) (by
        rw [heHuDiscriminantEndpointGoodBONG_order]
        norm_num)) k
  simpa using h

/-- Lemma 3.11(i), generic binary row.  The two choices `a=1` and
`a=c#` are exactly the first and second columns of Table 2. -/
theorem heHu2022Lemma311iGeneric
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d)
    (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) (k : Nat) :
    let b := heHuUnitDefectTailGoodBONG
      a c d ha hc hdOdd hdNonneg hdLt hcDefect
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitDefectTailGoodBONG_order]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ = 1 - d := by
  dsimp only
  have h := heHuLemma311_binaryTailProfile
    (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt hcDefect)
    (heHuIntegral_of_firstOrder_nonneg
      (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt hcDefect)
      (by rw [heHuUnitDefectTailGoodBONG_order]; norm_num)) k
  refine ⟨h.1, ?_, ?_⟩
  · exact h.2.1.trans (by
      simpa using heHuUnitDefectTailGoodBONG_order
        a c d ha hc hdOdd hdNonneg hdLt hcDefect (0 : Fin 2))
  · exact h.2.2.trans (by
      simpa using heHuUnitDefectTailGoodBONG_order
        a c d ha hc hdOdd hdNonneg hdLt hcDefect (1 : Fin 2))

/-- Every order in the unscaled endpoint block is bounded by the head of
the once-scaled endpoint block. -/
theorem heHuLemma311EvenSecondOne_orderBound
    [DyadicDiscriminantClassLaws K] (i : Fin 2) :
    (heHuDiscriminantEndpointGoodBONG (K := K) 0).order i ≤
      (heHuDiscriminantEndpointGoodBONG (K := K) 1).order 0 := by
  rw [heHuDiscriminantEndpointGoodBONG_order,
    heHuDiscriminantEndpointGoodBONG_order]
  fin_cases i <;> simp <;> omega

/-- The remaining endpoint comparison at the join of the two binary
blocks. -/
theorem heHuLemma311EvenSecondOne_lastSecondBound
    [DyadicDiscriminantClassLaws K]
    (_hn : 0 < 2) (_hm : 1 < 2) :
    (heHuDiscriminantEndpointGoodBONG (K := K) 0).order
        ⟨1, by omega⟩ ≤
      (heHuDiscriminantEndpointGoodBONG (K := K) 1).order
        ⟨1, by omega⟩ := by
  rw [heHuDiscriminantEndpointGoodBONG_order,
    heHuDiscriminantEndpointGoodBONG_order]
  simp

/-- The four-dimensional anisotropic tail in the `N_tilde_2^(2k+4)(1)`
row: the two endpoint blocks occur in the published order. -/
noncomputable def heHuLemma311EvenSecondOneTail
    [DyadicDiscriminantClassLaws K] :=
  (heHuDiscriminantEndpointGoodBONG (K := K) 0)
    |>.orthogonalProductRight_of_orderBounds
      (heHuDiscriminantEndpointGoodBONG (K := K) 1)
      heHuLemma311EvenSecondOne_orderBound
      heHuLemma311EvenSecondOne_lastSecondBound

@[simp]
theorem heHuLemma311EvenSecondOneTail_order
    [DyadicDiscriminantClassLaws K] (i : Fin 4) :
    (heHuLemma311EvenSecondOneTail (K := K)).order i =
      ![0, -(2 * (ramificationIndex K : Int)), 1,
        1 - 2 * (ramificationIndex K : Int)] i := by
  unfold heHuLemma311EvenSecondOneTail
  fin_cases i
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).order
            (BONG.orthogonalProductLeftIndex 2 (0 : Fin 2)) = 0
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_order]
    simp
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).order
            (BONG.orthogonalProductLeftIndex 2 (1 : Fin 2)) =
              -(2 * (ramificationIndex K : Int))
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_order]
    simp
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).order
            (BONG.orthogonalProductRightIndex 2 (0 : Fin 2)) = 1
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_right,
      heHuDiscriminantEndpointGoodBONG_order]
    rfl
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (heHuDiscriminantEndpointGoodBONG (K := K) 1)
          heHuLemma311EvenSecondOne_orderBound
          heHuLemma311EvenSecondOne_lastSecondBound).order
            (BONG.orthogonalProductRightIndex 2 (1 : Fin 2)) =
              1 - 2 * (ramificationIndex K : Int)
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_right,
      heHuDiscriminantEndpointGoodBONG_order]
    rfl

/-- The complete `N_tilde_2^(2k+4)(1)` order profile. -/
theorem heHu2022Lemma311iSecondOne
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    let b := heHuLemma311EvenSecondOneTail (K := K)
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311EvenSecondOneTail_order]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      ∀ j : Fin 4,
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + j.val, by omega⟩ =
            ![0, -(2 * (ramificationIndex K : Int)), 1,
              1 - 2 * (ramificationIndex K : Int)] j := by
  dsimp only
  let b := heHuLemma311EvenSecondOneTail (K := K)
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuLemma311EvenSecondOneTail_order]
    norm_num)
  have h := heHuLemma311_fourTailProfile b hIntegral k
  refine ⟨h.1, ?_⟩
  intro j
  exact (h.2 j).trans (heHuLemma311EvenSecondOneTail_order j)

/-- Both even-rank `delta*pi` columns.  Set `a=1` for the first column and
`a=Delta` for the second one. -/
theorem heHu2022Lemma311iUnitUniformizer
    (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let b := heHuUnitUniformizerPairGoodBONG a δ ha hδ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ = 1 := by
  dsimp only
  have h := heHuLemma311_binaryTailProfile
    (heHuUnitUniformizerPairGoodBONG a δ ha hδ)
    (heHuIntegral_of_firstOrder_nonneg
      (heHuUnitUniformizerPairGoodBONG a δ ha hδ) (by
        rw [heHuUnitUniformizerPairGoodBONG_orders]
        norm_num)) k
  refine ⟨h.1, ?_, ?_⟩
  · exact h.2.1.trans (by
      simpa using heHuUnitUniformizerPairGoodBONG_orders
        a δ ha hδ (0 : Fin 2))
  · exact h.2.2.trans (by
      simpa using heHuUnitUniformizerPairGoodBONG_orders
        a δ ha hδ (1 : Fin 2))

/-! ## Lemma 3.11(ii): odd rank -/

/-- The first-column odd-rank unit row
`H^k orthogonalSum <delta>`. -/
theorem heHu2022Lemma311iiFirstUnit
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let b := BONG.unaryModelGoodBONG δ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ])
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * k, by omega⟩ = 0 := by
  dsimp only
  have h := heHuLemma311_unaryTailProfile
    (BONG.unaryModelGoodBONG δ)
    (heHuIntegral_of_firstOrder_nonneg
      (BONG.unaryModelGoodBONG δ) (by
        rw [BONG.unaryModelGoodBONG_order,
          (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ])) k
  refine ⟨h.1, h.2.trans ?_⟩
  rw [BONG.unaryModelGoodBONG_order,
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]

/-- The first-column odd-rank ramified row
`H^k orthogonalSum <delta*pi>`. -/
theorem heHu2022Lemma311iiFirstUnitUniformizer
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let a := δ * uniformizerPowerUnit K 1
    let b := BONG.unaryModelGoodBONG a
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
        ordUnit_uniformizerPowerUnit]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
        ⟨2 * k, by omega⟩ = 1 := by
  dsimp only
  have h := heHuLemma311_unaryTailProfile
    (BONG.unaryModelGoodBONG (δ * uniformizerPowerUnit K 1))
    (heHuIntegral_of_firstOrder_nonneg
      (BONG.unaryModelGoodBONG (δ * uniformizerPowerUnit K 1)) (by
        rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
          ordUnit_uniformizerPowerUnit]
        norm_num)) k
  refine ⟨h.1, h.2.trans ?_⟩
  rw [BONG.unaryModelGoodBONG_order, ordUnit_mul,
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
    ordUnit_uniformizerPowerUnit]
  norm_num

/-- The exact Lemma 3.9(iii) ternary tail selected for the
`N_tilde_2^(2k+3)(delta)` row. -/
noncomputable def heHuLemma311OddSecondUnitTail
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    GoodBONG
      (unaryBinaryModelSpace
        (heHuLemma39iiiSourceUnary (K := K) δ)
        (uniformizerPowerUnit K 1)
        (uniformizerPowerUnit K 1 *
          lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible
          (uniformizerPowerUnit K 1)))
      (unaryBinaryModelLattice (K := K)) 3 := by
  let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
  exact Classical.choose
    (show ∃ b : GoodBONG
        (unaryBinaryModelSpace
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (uniformizerPowerUnit K 1)
          (uniformizerPowerUnit K 1 *
            lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible
            (uniformizerPowerUnit K 1)))
        (unaryBinaryModelLattice (K := K)) 3,
        ∀ i, b.valueUnit i =
          heHuLemma39iiiValues (K := K) δ κ (heHuSharp κ hc) i from
      heHu2022Lemma39iii δ κ hδ hκ hκDefect)

@[simp]
theorem heHuLemma311OddSecondUnitTail_valueUnit
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (i : Fin 3) :
    (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect).valueUnit i =
      heHuLemma39iiiValues (K := K) δ κ
        (heHuSharp κ
          (heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect)) i := by
  unfold heHuLemma311OddSecondUnitTail
  exact Classical.choose_spec
    (heHu2022Lemma39iii δ κ hδ hκ hκDefect) i

section OddSecondUnit

variable [laws : DyadicDiscriminantClassLaws K]
  [QuadraticDefectLaws K]
  [DyadicUnramifiedNormLaws K]
  [HilbertSymbolLaws K]
  [DyadicDiagonalClassificationLaws K]
  [BONGStructuralLaws.{u, u} K]
  [Beli2009WeightIdealData.{u, u} K]
  [Beli2019UnaryBinaryJordanLaws.{u} K]
  [Beli2009JordanWeightOrderLaws.{u, u} K]
  [Beli2006AlphaLaws.{u, u} K]
  [BeliLemma43ConstructionLaws.{u, u} K]
  [Beli2006SectionTwoLaws.{u, u} K]
  [GoodBONGClassificationLaws.{u, u, u} K]

@[simp]
theorem heHuLemma311OddSecondUnitTail_order
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (i : Fin 3) :
    (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect).order i =
      ![0, 2 - 2 * (ramificationIndex K : Int), 0] i := by
  change
    (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect).toBONG.order i = _
  rw [BONG.order_eq_ordUnit]
  change ordUnit K
      ((heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect).valueUnit i) = _
  rw [heHuLemma311OddSecondUnitTail_valueUnit]
  apply heHuLemma39iiiValues_orders
  · exact hδ
  · exact hκ
  · exact (heHu2022Proposition32 κ
      (heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect)).1

/-- The complete `N_tilde_2^(2k+3)(delta)` profile, including the
exceptional penultimate order `2-2e`. -/
theorem heHu2022Lemma311iiSecondUnit
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (k : Nat) :
    let b := heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitTail_order]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ =
            2 - 2 * (ramificationIndex K : Int) ∧
          (Bong.heHu2022Lemma310BONG b hIntegral k).order
            ⟨2 * k + 2, by omega⟩ = 0 := by
  dsimp only
  have h := heHuLemma311_ternaryTailProfile
    (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect)
    (heHuIntegral_of_firstOrder_nonneg
      (heHuLemma311OddSecondUnitTail δ κ hδ hκ hκDefect) (by
        rw [heHuLemma311OddSecondUnitTail_order]
        norm_num)) k
  refine ⟨h.1, ?_, ?_, ?_⟩
  · exact h.2.1.trans (by
      simpa using heHuLemma311OddSecondUnitTail_order
        δ κ hδ hκ hκDefect (0 : Fin 3))
  · exact h.2.2.1.trans (by
      simpa using heHuLemma311OddSecondUnitTail_order
        δ κ hδ hκ hκDefect (1 : Fin 3))
  · exact h.2.2.2.trans (by
      simpa using heHuLemma311OddSecondUnitTail_order
        δ κ hδ hκ hκDefect (2 : Fin 3))

end OddSecondUnit

/-- The unary coefficient `Delta*delta*pi` at the end of the second
odd-rank ramified row. -/
noncomputable def heHuLemma311OddSecondUnitUniformizerValue
    [laws : DyadicDiscriminantClassLaws K] (δ : Kˣ) : Kˣ :=
  laws.discriminantUnit * δ * uniformizerPowerUnit K 1

@[simp]
theorem heHuLemma311OddSecondUnitUniformizerValue_order
    [laws : DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) :
    ordUnit K (heHuLemma311OddSecondUnitUniformizerValue δ) = 1 := by
  unfold heHuLemma311OddSecondUnitUniformizerValue
  rw [ordUnit_mul, ordUnit_mul, ordUnit_uniformizerPowerUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
  norm_num

theorem heHuLemma311OddSecondUnitUniformizer_orderBound
    [laws : DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (i : Fin 2) :
    (heHuDiscriminantEndpointGoodBONG (K := K) 0).order i ≤
      (BONG.unaryModelGoodBONG
        (heHuLemma311OddSecondUnitUniformizerValue δ)).order 0 := by
  rw [heHuDiscriminantEndpointGoodBONG_order,
    BONG.unaryModelGoodBONG_order,
    heHuLemma311OddSecondUnitUniformizerValue_order δ hδ]
  fin_cases i <;> simp <;> omega

theorem heHuLemma311OddSecondUnitUniformizer_lastSecondBound
    [laws : DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (_hδ : IsValuationUnit K (δ : K))
    (_hn : 0 < 2) (hm : 1 < 1) :
    (heHuDiscriminantEndpointGoodBONG (K := K) 0).order
        ⟨1, by omega⟩ ≤
      (BONG.unaryModelGoodBONG
        (heHuLemma311OddSecondUnitUniformizerValue δ)).order
          ⟨1, hm⟩ := by
  omega

/-- Exact ternary tail
`2^-1*A(2,2rho) orthogonalSum <Delta*delta*pi>`. -/
noncomputable def heHuLemma311OddSecondUnitUniformizerTail
    [DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) :=
  (heHuDiscriminantEndpointGoodBONG (K := K) 0)
    |>.orthogonalProductRight_of_orderBounds
      (BONG.unaryModelGoodBONG
        (heHuLemma311OddSecondUnitUniformizerValue δ))
      (heHuLemma311OddSecondUnitUniformizer_orderBound δ hδ)
      (heHuLemma311OddSecondUnitUniformizer_lastSecondBound δ hδ)

@[simp]
theorem heHuLemma311OddSecondUnitUniformizerTail_order
    [DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (i : Fin 3) :
    (heHuLemma311OddSecondUnitUniformizerTail δ hδ).order i =
      ![0, -(2 * (ramificationIndex K : Int)), 1] i := by
  unfold heHuLemma311OddSecondUnitUniformizerTail
  fin_cases i
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (BONG.unaryModelGoodBONG
            (heHuLemma311OddSecondUnitUniformizerValue δ))
          (heHuLemma311OddSecondUnitUniformizer_orderBound δ hδ)
          (heHuLemma311OddSecondUnitUniformizer_lastSecondBound δ hδ)).order
            (BONG.orthogonalProductLeftIndex 1 (0 : Fin 2)) = 0
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_order]
    rfl
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (BONG.unaryModelGoodBONG
            (heHuLemma311OddSecondUnitUniformizerValue δ))
          (heHuLemma311OddSecondUnitUniformizer_orderBound δ hδ)
          (heHuLemma311OddSecondUnitUniformizer_lastSecondBound δ hδ)).order
            (BONG.orthogonalProductLeftIndex 1 (1 : Fin 2)) =
              -(2 * (ramificationIndex K : Int))
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_left,
      heHuDiscriminantEndpointGoodBONG_order]
    simp
  · change
      ((heHuDiscriminantEndpointGoodBONG (K := K) 0)
        |>.orthogonalProductRight_of_orderBounds
          (BONG.unaryModelGoodBONG
            (heHuLemma311OddSecondUnitUniformizerValue δ))
          (heHuLemma311OddSecondUnitUniformizer_orderBound δ hδ)
          (heHuLemma311OddSecondUnitUniformizer_lastSecondBound δ hδ)).order
            (BONG.orthogonalProductRightIndex 2 (0 : Fin 1)) = 1
    rw [heHuOrder_orthogonalProductRight_of_orderBounds_right,
      BONG.unaryModelGoodBONG_order,
      heHuLemma311OddSecondUnitUniformizerValue_order δ hδ]

/-- The complete `N_tilde_2^(2k+3)(delta*pi)` profile. -/
theorem heHu2022Lemma311iiSecondUnitUniformizer
    [DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) (k : Nat) :
    let b := heHuLemma311OddSecondUnitUniformizerTail δ hδ
    let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
      rw [heHuLemma311OddSecondUnitUniformizerTail_order]
      norm_num)
    (∀ t : Fin k,
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * t.val + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int))) ∧
      (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k, by omega⟩ = 0 ∧
        (Bong.heHu2022Lemma310BONG b hIntegral k).order
          ⟨2 * k + 1, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) ∧
          (Bong.heHu2022Lemma310BONG b hIntegral k).order
            ⟨2 * k + 2, by omega⟩ = 1 := by
  dsimp only
  have h := heHuLemma311_ternaryTailProfile
    (heHuLemma311OddSecondUnitUniformizerTail δ hδ)
    (heHuIntegral_of_firstOrder_nonneg
      (heHuLemma311OddSecondUnitUniformizerTail δ hδ) (by
        rw [heHuLemma311OddSecondUnitUniformizerTail_order]
        norm_num)) k
  refine ⟨h.1, ?_, ?_, ?_⟩
  · exact h.2.1.trans (by
      simpa using heHuLemma311OddSecondUnitUniformizerTail_order
        δ hδ (0 : Fin 3))
  · exact h.2.2.1.trans (by
      simpa using heHuLemma311OddSecondUnitUniformizerTail_order
        δ hδ (1 : Fin 3))
  · exact h.2.2.2.trans (by
      simpa using heHuLemma311OddSecondUnitUniformizerTail_order
        δ hδ (2 : Fin 3))

end BONG.GoodBONG

end Bong
