/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Sufficiency
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.UnaryBinaryModel
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019), Lemma 9.5(ii): explicit normal-form coefficients

This file separates the field-space calculation from the Jordan-lattice
calculation in Lemma 9.5(ii).  The coefficient list is defined literally as
in the paper.  We prove its orders, determinant class, isotropy type, binary
admissibility, and hence its ambient-space isometry with the original
ternary space.

The remaining integral step is the computation of the good-BONG orders and
weight ideal of the explicit unary--binary product lattice.  That step is
packaged below through the precise 2009 Jordan interfaces used by the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The unit part `ε₁ε₂ε₃` of the determinant of a ternary BONG. -/
noncomputable def ternaryDeterminantUnitPart
    (a : GoodBONG q L 3) : Kˣ :=
  normalizedUnitPart K a.toBONG.valueProduct

theorem ternaryDeterminantUnitPart_isValuationUnit
    (a : GoodBONG q L 3) :
    IsValuationUnit K (a.ternaryDeterminantUnitPart : K) :=
  normalizedUnitPart_isValuationUnit (K := K) a.toBONG.valueProduct

/-- The coefficient list in Lemma 9.5(ii), with `twist = 1` in the
isotropic case and `twist = Δ` in the anisotropic case. -/
noncomputable def beli2019Lemma95NormalFormValues
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ) : Fin 3 → Kˣ :=
  ![-(uniformizerPowerUnit K (a.order 0) *
        a.ternaryDeterminantUnitPart * twist),
    uniformizerPowerUnit K (a.order 0 + A₁),
    -(uniformizerPowerUnit K (a.order 0 - A₂) * twist)]

@[simp]
theorem beli2019Lemma95NormalFormValues_zero
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ) :
    a.beli2019Lemma95NormalFormValues A₁ A₂ twist 0 =
      -(uniformizerPowerUnit K (a.order 0) *
        a.ternaryDeterminantUnitPart * twist) := by
  rfl

@[simp]
theorem beli2019Lemma95NormalFormValues_one
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ) :
    a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1 =
      uniformizerPowerUnit K (a.order 0 + A₁) := by
  rfl

@[simp]
theorem beli2019Lemma95NormalFormValues_two
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ) :
    a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2 =
      -(uniformizerPowerUnit K (a.order 0 - A₂) * twist) := by
  rfl

/-- The three displayed coefficients have the orders written in the paper. -/
theorem beli2019Lemma95NormalFormValues_orders
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ)
    (htwist : IsValuationUnit K (twist : K)) :
    (∀ i, ordUnit K (a.beli2019Lemma95NormalFormValues A₁ A₂ twist i) =
      ![a.order 0, a.order 0 + A₁, a.order 0 - A₂] i) := by
  have hdet : ordUnit K a.ternaryDeterminantUnitPart = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      a.ternaryDeterminantUnitPart).1
      a.ternaryDeterminantUnitPart_isValuationUnit
  have htwistOrder : ordUnit K twist = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K twist).1 htwist
  intro i
  have hfin : i = 0 ∨ i = 1 ∨ i = 2 := by
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with
      hi | hi | hi
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Or.inl (Fin.ext hi))
    · exact Or.inr (Or.inr (Fin.ext hi))
  rcases hfin with rfl | rfl | rfl
  · rw [beli2019Lemma95NormalFormValues_zero, ordUnit_neg,
      ordUnit_mul, ordUnit_mul, ordUnit_uniformizerPowerUnit,
      hdet, htwistOrder]
    simp
  · rw [beli2019Lemma95NormalFormValues_one,
      ordUnit_uniformizerPowerUnit]
    rfl
  · rw [beli2019Lemma95NormalFormValues_two, ordUnit_neg,
      ordUnit_mul, ordUnit_uniformizerPowerUnit, htwistOrder]
    simp

/-- Integer witnesses for the two alphas satisfy the relation
`R₁ + A₁ = R₂ + A₂` from Remark 8.7. -/
theorem beli2019Lemma95_alphaInteger_relation
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    a.order 0 + A₁ = a.order 1 + A₂ := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hrelation := hremark.currentAlpha_eq
  change a.alphaValue 1 =
      ((a.order 0 - a.order 1 : Int) : ℚ) + a.alphaValue 0 at hrelation
  rw [hA₁, hA₂] at hrelation
  have hrelationInt : A₂ = a.order 0 - a.order 1 + A₁ := by
    exact_mod_cast hrelation
  omega

/-- The two integer alpha witnesses have the same parity. -/
theorem beli2019Lemma95_alphaInteger_sameParity
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    Even (A₁ - A₂) := by
  have hrelation := a.beli2019Lemma95_alphaInteger_relation
    houter A₁ A₂ hA₁ hA₂
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hmod := hremark.previous_middle_modEq
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨k, hk⟩
  have hk' : a.order (1 : Fin 3) - a.order (0 : Fin 3) = 2 * k := by
    change a.order (1 : Fin 3) - a.order (0 : Fin 3) = 2 * k at hk
    exact hk
  refine ⟨k, ?_⟩
  omega

/-- Integer witnesses for the two alphas satisfy the upper bound from
Remark 8.7. -/
theorem beli2019Lemma95_alphaInteger_sum_le_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    A₁ + A₂ ≤ 2 * (ramificationIndex K : Int) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hsum : a.alphaValue 0 + a.alphaValue 1 ≤
      2 * (ramificationIndex K : ℚ) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha] using
      hremark.alphaSum_le_twoE
  rw [hA₁, hA₂] at hsum
  exact_mod_cast hsum

/-- The sum of the two integer alpha witnesses is even. -/
theorem beli2019Lemma95_alphaInteger_sum_even
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    Even (A₁ + A₂) := by
  have hparity := a.beli2019Lemma95_alphaInteger_sameParity
    houter A₁ A₂ hA₁ hA₂
  simpa [add_comm] using (even_add_of_even_sub hparity)

/-- An even power of the chosen uniformizer is a square. -/
theorem isSquare_uniformizerPowerUnit_of_even
    (m : Int) (hm : Even m) :
    IsSquare (uniformizerPowerUnit K m) := by
  rcases hm with ⟨k, hk⟩
  refine ⟨uniformizerPowerUnit K k, ?_⟩
  change uniformizerUnit K ^ m =
    uniformizerUnit K ^ k * uniformizerUnit K ^ k
  rw [← zpow_add, hk]

/-- The parameter of the displayed binary block is the expected
uniformizer power, with the optional discriminant twist. -/
theorem beli2019Lemma95NormalForm_binaryParameter
    (a : GoodBONG q L 3) (A₁ A₂ : Int) (twist : Kˣ) :
    a.beli2019Lemma95NormalFormValues A₁ A₂ twist 2 /
        a.beli2019Lemma95NormalFormValues A₁ A₂ twist 1 =
      -(uniformizerPowerUnit K (-(A₁ + A₂)) * twist) := by
  rw [beli2019Lemma95NormalFormValues_two,
    beli2019Lemma95NormalFormValues_one, neg_div]
  have hpower :
      uniformizerPowerUnit K (a.order 0 - A₂) /
          uniformizerPowerUnit K (a.order 0 + A₁) =
        uniformizerPowerUnit K (-(A₁ + A₂)) := by
    unfold uniformizerPowerUnit
    rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  congr 1
  calc
    uniformizerPowerUnit K (a.order 0 - A₂) * twist /
          uniformizerPowerUnit K (a.order 0 + A₁) =
        (uniformizerPowerUnit K (a.order 0 - A₂) /
          uniformizerPowerUnit K (a.order 0 + A₁)) * twist := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ = uniformizerPowerUnit K (-(A₁ + A₂)) * twist := by
      rw [hpower]

/-- Multiplying the discriminant unit by an even uniformizer power has
integral absolute quadratic defect as soon as its total order is at least
`-2e`. -/
theorem hasNonnegativeAbsoluteQuadraticDefect_uniformizerPower_mul_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    (m : Int) (hm : Even m)
    (hlower : 0 ≤ m + 2 * (ramificationIndex K : Int)) :
    HasNonnegativeAbsoluteQuadraticDefect
      (uniformizerPowerUnit K m * laws.discriminantUnit) := by
  rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le]
  have horder :
      ordUnit K (uniformizerPowerUnit K m * laws.discriminantUnit) = m := by
    rw [ordUnit_mul, ordUnit_uniformizerPowerUnit]
    have hunit : ordUnit K laws.discriminantUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K
        laws.discriminantUnit).1 laws.discriminant_isValuationUnit
    rw [hunit]
    omega
  have hsquare := isSquare_uniformizerPowerUnit_of_even (K := K) m hm
  rcases hsquare with ⟨s, hs⟩
  have hfactor :
      uniformizerPowerUnit K m * laws.discriminantUnit =
        laws.discriminantUnit * s ^ 2 := by
    rw [hs, pow_two]
    ac_rfl
  rw [absoluteDefectThreshold, horder, hfactor,
    quadraticDefect_mul_square, laws.discriminant_defect]
  exact_mod_cast (show Int.toNat (-m) ≤
      2 * ramificationIndex K by omega)

/-- The binary block in the isotropic normal form is an actual admissible
binary lattice parameter. -/
theorem beli2019Lemma95NormalForm_binaryAdmissible_one
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    IsBinaryParameterAdmissible
      (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2 /
        a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1) := by
  apply (isBinaryParameterAdmissible_iff_beli _).2
  apply Or.inr
  constructor
  · rw [a.beli2019Lemma95NormalForm_binaryParameter, neg_neg, mul_one]
    exact isSquare_uniformizerPowerUnit_of_even
      (K := K) (-(A₁ + A₂))
      (a.beli2019Lemma95_alphaInteger_sum_even
        houter A₁ A₂ hA₁ hA₂).neg
  · have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [a.beli2019Lemma95NormalForm_binaryParameter,
      ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit, hone]
    have hsum := a.beli2019Lemma95_alphaInteger_sum_le_twoE
      houter A₁ A₂ hA₁ hA₂
    omega

/-- The discriminant-twisted binary block in the anisotropic normal form is
also an actual admissible binary lattice parameter. -/
theorem beli2019Lemma95NormalForm_binaryAdmissible_discriminant
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    IsBinaryParameterAdmissible
      (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 2 /
        a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 1) := by
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect _).2
  have hsum := a.beli2019Lemma95_alphaInteger_sum_le_twoE
    houter A₁ A₂ hA₁ hA₂
  have heven := (a.beli2019Lemma95_alphaInteger_sum_even
    houter A₁ A₂ hA₁ hA₂).neg
  constructor
  · rw [a.beli2019Lemma95NormalForm_binaryParameter,
      ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit]
    have hunit : ordUnit K laws.discriminantUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K
        laws.discriminantUnit).1 laws.discriminant_isValuationUnit
    rw [hunit]
    omega
  · rw [a.beli2019Lemma95NormalForm_binaryParameter, neg_neg]
    exact
      hasNonnegativeAbsoluteQuadraticDefect_uniformizerPower_mul_discriminant
        (K := K) (-(A₁ + A₂)) heven (by omega)

/-- The determinant of the displayed coefficient list is the original BONG
determinant multiplied by the square of the twist. -/
theorem beli2019Lemma95NormalForm_determinant_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (twist : Kˣ) :
    diagonalUnitDeterminant
        (a.beli2019Lemma95NormalFormValues A₁ A₂ twist) =
      a.toBONG.valueProduct * twist ^ 2 := by
  have hrelation := a.beli2019Lemma95_alphaInteger_relation
    houter A₁ A₂ hA₁ hA₂
  have horder : ordUnit K a.toBONG.valueProduct =
      3 * a.order 0 + A₁ - A₂ := by
    unfold GoodBONG.order at houter hrelation ⊢
    rw [a.toBONG.ordUnit_valueProduct_eq_sum_order,
      Fin.sum_univ_three, houter]
    omega
  have hfactor :=
    uniformizerPower_mul_normalizedUnitPart K a.toBONG.valueProduct
  change uniformizerPowerUnit K (ordUnit K a.toBONG.valueProduct) *
      a.ternaryDeterminantUnitPart = a.toBONG.valueProduct at hfactor
  rw [horder] at hfactor
  have hpower :
      uniformizerPowerUnit K (a.order 0) *
          uniformizerPowerUnit K (a.order 0 + A₁) *
          uniformizerPowerUnit K (a.order 0 - A₂) =
        uniformizerPowerUnit K (3 * a.order 0 + A₁ - A₂) := by
    unfold uniformizerPowerUnit
    rw [← zpow_add, ← zpow_add]
    congr 1
    omega
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_three,
    beli2019Lemma95NormalFormValues_zero,
    beli2019Lemma95NormalFormValues_one,
    beli2019Lemma95NormalFormValues_two]
  simp only [neg_mul, mul_neg, neg_neg]
  calc
    (uniformizerPowerUnit K (a.order 0) *
          a.ternaryDeterminantUnitPart * twist) *
        uniformizerPowerUnit K (a.order 0 + A₁) *
        (uniformizerPowerUnit K (a.order 0 - A₂) * twist) =
      (uniformizerPowerUnit K (a.order 0) *
          uniformizerPowerUnit K (a.order 0 + A₁) *
          uniformizerPowerUnit K (a.order 0 - A₂) *
          a.ternaryDeterminantUnitPart) * twist ^ 2 := by
        simp only [pow_two]
        ac_rfl
    _ = (uniformizerPowerUnit K (3 * a.order 0 + A₁ - A₂) *
          a.ternaryDeterminantUnitPart) * twist ^ 2 := by rw [hpower]
    _ = a.toBONG.valueProduct * twist ^ 2 := by rw [hfactor]

/-- Consequently the displayed and original coefficient lists have the same
determinant square class. -/
theorem beli2019Lemma95NormalForm_determinantSquare
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (twist : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant
          (a.beli2019Lemma95NormalFormValues A₁ A₂ twist) *
        diagonalUnitDeterminant a.valueUnit) := by
  rw [a.beli2019Lemma95NormalForm_determinant_eq
    houter A₁ A₂ hA₁ hA₂ twist]
  refine ⟨a.toBONG.valueProduct * twist, ?_⟩
  unfold diagonalUnitDeterminant BONG.valueProduct BONG.prefixProduct
  rw [show Finset.univ.filter (fun i : Fin 3 ↦ i.1 < 3) =
      Finset.univ by ext i; simp]
  simp only [pow_two]
  ac_rfl

/-- The untwisted displayed ternary form is isotropic. -/
theorem beli2019Lemma95NormalForm_isotropic_one
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ)) :
    DiagonalIsotropic
      (diagonalUnitCoefficients
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1)) := by
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
  have hparameter :
      -(a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1 *
          a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2) =
        uniformizerPowerUnit K
          (2 * a.order 0 + A₁ - A₂) := by
    rw [beli2019Lemma95NormalFormValues_one,
      beli2019Lemma95NormalFormValues_two]
    simp only [mul_one, mul_neg, neg_neg]
    unfold uniformizerPowerUnit
    rw [← zpow_add]
    congr 1
    omega
  rw [hparameter]
  have hsame := a.beli2019Lemma95_alphaInteger_sameParity
    houter A₁ A₂ hA₁ hA₂
  rcases hsame with ⟨k, hk⟩
  apply hilbertSymbol_eq_one_of_isSquare_right K
  apply isSquare_uniformizerPowerUnit_of_even
  exact ⟨a.order 0 + k, by omega⟩

/-- The discriminant-twisted displayed ternary form is anisotropic when
the first alpha witness is odd. -/
theorem beli2019Lemma95NormalForm_anisotropic_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3)
    (A₁ A₂ : Int)
    (hA₁Odd : Odd A₁)
    (hparity : Even (A₁ - A₂)) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit)) := by
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic]
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
  let c := a.beli2019Lemma95NormalFormValues A₁ A₂
    laws.discriminantUnit
  have hfirst : -(c 0 * c 1) =
      uniformizerPowerUnit K (2 * a.order 0 + A₁) *
        a.ternaryDeterminantUnitPart * laws.discriminantUnit := by
    dsimp only [c]
    rw [beli2019Lemma95NormalFormValues_zero,
      beli2019Lemma95NormalFormValues_one]
    simp only [neg_mul, neg_neg]
    have hpower :
        uniformizerPowerUnit K (a.order 0) *
            uniformizerPowerUnit K (a.order 0 + A₁) =
          uniformizerPowerUnit K (2 * a.order 0 + A₁) := by
      unfold uniformizerPowerUnit
      rw [← zpow_add]
      congr 1
      omega
    rw [show (uniformizerPowerUnit K (a.order 0) *
          a.ternaryDeterminantUnitPart * laws.discriminantUnit) *
          uniformizerPowerUnit K (a.order 0 + A₁) =
        (uniformizerPowerUnit K (a.order 0) *
          uniformizerPowerUnit K (a.order 0 + A₁)) *
          a.ternaryDeterminantUnitPart * laws.discriminantUnit by ac_rfl,
      hpower]
  have hsecond : -(c 1 * c 2) =
      uniformizerPowerUnit K (2 * a.order 0 + A₁ - A₂) *
        laws.discriminantUnit := by
    dsimp only [c]
    rw [beli2019Lemma95NormalFormValues_one,
      beli2019Lemma95NormalFormValues_two]
    simp only [mul_neg, neg_neg]
    have hpower :
        uniformizerPowerUnit K (a.order 0 + A₁) *
            uniformizerPowerUnit K (a.order 0 - A₂) =
          uniformizerPowerUnit K (2 * a.order 0 + A₁ - A₂) := by
      unfold uniformizerPowerUnit
      rw [← zpow_add]
      congr 1
      omega
    rw [← mul_assoc, hpower]
  have hfirstOdd : Odd (ordUnit K (-(c 0 * c 1))) := by
    rw [hfirst, ordUnit_mul, ordUnit_mul,
      ordUnit_uniformizerPowerUnit]
    have hdet : ordUnit K a.ternaryDeterminantUnitPart = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K
        a.ternaryDeterminantUnitPart).1
        a.ternaryDeterminantUnitPart_isValuationUnit
    have hdisc : ordUnit K laws.discriminantUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K
        laws.discriminantUnit).1 laws.discriminant_isValuationUnit
    rw [hdet, hdisc]
    rcases hA₁Odd with ⟨k, hk⟩
    exact ⟨a.order 0 + k, by omega⟩
  have hsecondTwistedSquare :
      IsSquare (-(c 1 * c 2) * laws.discriminantUnit) := by
    rw [hsecond]
    have hpowerEven : Even (2 * a.order 0 + A₁ - A₂) := by
      rcases hparity with ⟨k, hk⟩
      exact ⟨a.order 0 + k, by omega⟩
    have hsquarePower := isSquare_uniformizerPowerUnit_of_even
      (K := K) (2 * a.order 0 + A₁ - A₂) hpowerEven
    simpa only [mul_assoc] using
      hsquarePower.mul (show IsSquare
        (laws.discriminantUnit * laws.discriminantUnit) from
          ⟨laws.discriminantUnit, rfl⟩)
  have hne :=
    hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
      hsecondTwistedSquare hfirstOdd
  rw [hilbertSymbol_comm K (-(c 1 * c 2)) (-(c 0 * c 1))] at hne
  exact hne

/-- In rank three, the prefix-isotropy predicate used in Lemma 8.14 is
literally the isotropy predicate of the complete BONG coefficient list. -/
theorem lemma814FirstThreeIsotropic_iff_diagonalValueUnits
    (a : GoodBONG q L 3) :
    a.Lemma814FirstThreeIsotropic ↔
      DiagonalIsotropic (diagonalUnitCoefficients a.valueUnit) := by
  rw [a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
  rfl

/-- In the isotropic branch, the displayed form and the original ternary
BONG have the same Hasse symbol. -/
theorem beli2019Lemma95NormalForm_hasse_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    diagonalHasseSymbol K
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1) =
      diagonalHasseSymbol K a.valueUnit := by
  apply diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
  have hcandidate := a.beli2019Lemma95NormalForm_isotropic_one
    houter A₁ A₂ hA₁ hA₂
  have hsource :=
    (a.lemma814FirstThreeIsotropic_iff_diagonalValueUnits).mp hisotropic
  exact ⟨fun _ ↦ hsource, fun _ ↦ hcandidate⟩

/-- In the anisotropic branch, the discriminant-twisted displayed form and
the original ternary BONG have the same Hasse symbol. -/
theorem beli2019Lemma95NormalForm_hasse_eq_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3)
    (A₁ A₂ : Int)
    (hA₁Odd : Odd A₁)
    (hparity : Even (A₁ - A₂))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    diagonalHasseSymbol K
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit) =
      diagonalHasseSymbol K a.valueUnit := by
  apply diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
  have hcandidateAnisotropic :=
    a.beli2019Lemma95NormalForm_anisotropic_discriminant
      A₁ A₂ hA₁Odd hparity
  have hcandidateNot : ¬DiagonalIsotropic
      (diagonalUnitCoefficients
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit)) :=
    (not_diagonalIsotropic_iff_diagonalAnisotropic _).2
      hcandidateAnisotropic
  have hsourceNotPrefix : ¬a.Lemma814FirstThreeIsotropic :=
    a.not_firstThreeIsotropic_of_anisotropic hanisotropic
  have hsourceNot : ¬DiagonalIsotropic
      (diagonalUnitCoefficients a.valueUnit) := by
    rw [← a.lemma814FirstThreeIsotropic_iff_diagonalValueUnits]
    exact hsourceNotPrefix
  exact ⟨fun h ↦ False.elim (hcandidateNot h),
    fun h ↦ False.elim (hsourceNot h)⟩

/-- Local diagonal classification realizes the isotropic coefficient list
inside the original ternary quadratic space. -/
theorem beli2019Lemma95NormalForm_diagonalRepresents_one
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1))
      (diagonalUnitCoefficients a.valueUnit) :=
  DyadicDiagonalClassificationLaws.represents_of_invariants
    (a.beli2019Lemma95NormalFormValues A₁ A₂ 1) a.valueUnit
    (a.beli2019Lemma95NormalForm_determinantSquare
      houter A₁ A₂ hA₁ hA₂ 1)
    (a.beli2019Lemma95NormalForm_hasse_eq_one
      houter A₁ A₂ hA₁ hA₂ hisotropic)

/-- Local diagonal classification realizes the anisotropic coefficient list
inside the original ternary quadratic space. -/
theorem beli2019Lemma95NormalForm_diagonalRepresents_discriminant
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hA₁Odd : Odd A₁)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit))
      (diagonalUnitCoefficients a.valueUnit) := by
  apply DyadicDiagonalClassificationLaws.represents_of_invariants
  · exact a.beli2019Lemma95NormalForm_determinantSquare
      houter A₁ A₂ hA₁ hA₂ laws.discriminantUnit
  · exact a.beli2019Lemma95NormalForm_hasse_eq_discriminant
      A₁ A₂ hA₁Odd
      (a.beli2019Lemma95_alphaInteger_sameParity
        houter A₁ A₂ hA₁ hA₂)
      hanisotropic

/-- Ambient-space form of the isotropic normal form in Lemma 9.5(ii). -/
theorem beli2019Lemma95NormalForm_isIsometric_one
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hisotropic : a.Lemma814FirstThreeIsotropic) :
    q.IsIsometric
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂ 1 2)
        (a.beli2019Lemma95NormalForm_binaryAdmissible_one
          houter A₁ A₂ hA₁ hA₂)) := by
  apply a.isIsometric_unaryBinaryModel_of_diagonalRepresents
  exact a.beli2019Lemma95NormalForm_diagonalRepresents_one
    houter A₁ A₂ hA₁ hA₂ hisotropic

/-- Ambient-space form of the anisotropic normal form in Lemma 9.5(ii). -/
theorem beli2019Lemma95NormalForm_isIsometric_discriminant
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3)
    (houter : a.order 0 = a.order 2)
    (A₁ A₂ : Int)
    (hA₁ : a.alphaValue 0 = (A₁ : ℚ))
    (hA₂ : a.alphaValue 1 = (A₂ : ℚ))
    (hA₁Odd : Odd A₁)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    q.IsIsometric
      (unaryBinaryModelSpace
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 0)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 1)
        (a.beli2019Lemma95NormalFormValues A₁ A₂
          laws.discriminantUnit 2)
        (a.beli2019Lemma95NormalForm_binaryAdmissible_discriminant
          houter A₁ A₂ hA₁ hA₂)) := by
  apply a.isIsometric_unaryBinaryModel_of_diagonalRepresents
  exact a.beli2019Lemma95NormalForm_diagonalRepresents_discriminant
    houter A₁ A₂ hA₁ hA₂ hA₁Odd hanisotropic

end BONG.GoodBONG

end Bong
