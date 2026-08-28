/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.TernaryExactRealization
import Bong.Bong.Beli2019Lemma95Jordan
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.BinaryEndpointStandardModel
import Bong.Bong.Beli2019Lemma910Boundary
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019), Lemma 7.12(ii)

This file formalizes the discriminant-plane branch of Lemma 7.12.  The
source is the literal unary--binary product

`<a> ⊥ [p, -(Δ/4)p]`, with `ord(p) = ord(a) + 1`.

For valuation units `ε,η` of defects `1,2e-1` and Hilbert symbol `-1`,
the target good BONG has the exact values

`[aε, -(Δ/4)π²aεη, aη]`.

Allowing an arbitrary `p` of the required order is useful in Lemma 7.14:
there `p` is the first value of the rescaled initial binary block and need
not be literally `πa`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The endpoint parameter `-Δ/4`. -/
noncomputable def lemma712DiscriminantParameter
    [laws : DyadicDiscriminantClassLaws K] : Kˣ :=
  negativeQuarterUnit K * laws.discriminantUnit

/-- Orthogonal coefficients of the explicit source model. -/
noncomputable def lemma712SourceValues
    [DyadicDiscriminantClassLaws K] (a p : Kˣ) : Fin 3 → Kˣ :=
  ![a, p, p * lemma712DiscriminantParameter (K := K)]

/-- The three coefficients displayed in Lemma 7.12(ii). -/
noncomputable def lemma712TargetValues
    [DyadicDiscriminantClassLaws K] (a ε η : Kˣ) : Fin 3 → Kˣ :=
  ![a * ε,
    lemma712DiscriminantParameter (K := K) *
      uniformizerPowerUnit K 2 * a * ε * η,
    a * η]

@[simp]
theorem lemma712SourceValues_zero
    [DyadicDiscriminantClassLaws K] (a p : Kˣ) :
    lemma712SourceValues a p (0 : Fin 3) = a := by
  rfl

@[simp]
theorem lemma712SourceValues_one
    [DyadicDiscriminantClassLaws K] (a p : Kˣ) :
    lemma712SourceValues a p (1 : Fin 3) = p := by
  rfl

@[simp]
theorem lemma712SourceValues_two
    [DyadicDiscriminantClassLaws K] (a p : Kˣ) :
    lemma712SourceValues a p (2 : Fin 3) =
      p * lemma712DiscriminantParameter (K := K) := by
  rfl

@[simp]
theorem lemma712TargetValues_zero
    [DyadicDiscriminantClassLaws K] (a ε η : Kˣ) :
    lemma712TargetValues a ε η (0 : Fin 3) = a * ε := by
  rfl

@[simp]
theorem lemma712TargetValues_one
    [DyadicDiscriminantClassLaws K] (a ε η : Kˣ) :
    lemma712TargetValues a ε η (1 : Fin 3) =
      lemma712DiscriminantParameter (K := K) *
        uniformizerPowerUnit K 2 * a * ε * η := by
  rfl

@[simp]
theorem lemma712TargetValues_two
    [DyadicDiscriminantClassLaws K] (a ε η : Kˣ) :
    lemma712TargetValues a ε η (2 : Fin 3) = a * η := by
  rfl

/-- The binary endpoint parameter of the source admits the standard shear
`1/2`. -/
theorem lemma712_sourceBinaryAdmissible
    [laws : DyadicDiscriminantClassLaws K] (p : Kˣ) :
    IsBinaryParameterAdmissible
      ((p * lemma712DiscriminantParameter (K := K)) / p) := by
  have hratio :
      (p * lemma712DiscriminantParameter (K := K)) / p =
        lemma712DiscriminantParameter (K := K) := by
    simp
  rw [hratio]
  refine ⟨standardEndpointShear (K := K),
    standardEndpointShear_two_integral (K := K), ?_⟩
  exact discriminant_standardEndpointShear_diagonal_integral (K := K)

/-- The evident orthogonal basis of the unary--binary source model. -/
noncomputable def lemma712SourceOrthogonalBasisData
    [laws : DyadicDiscriminantClassLaws K] (a p : Kˣ) :
    BONG.OrthogonalBasisData
      (unaryBinaryModelSpace a p
        (p * lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible p)) 3 :=
  ⟨unaryBinaryOrthogonalBasis a p
      (p * lemma712DiscriminantParameter (K := K))
      (lemma712_sourceBinaryAdmissible p),
    unaryBinaryOrthogonalBasis_isOrtho a p
      (p * lemma712DiscriminantParameter (K := K))
      (lemma712_sourceBinaryAdmissible p)⟩

@[simp]
theorem lemma712SourceOrthogonalBasisData_valueUnit
    [laws : DyadicDiscriminantClassLaws K] (a p : Kˣ) (i : Fin 3) :
    (lemma712SourceOrthogonalBasisData a p).valueUnit i =
      lemma712SourceValues a p i := by
  apply Units.ext
  change
    (unaryBinaryModelSpace a p
      (p * lemma712DiscriminantParameter (K := K))
      (lemma712_sourceBinaryAdmissible p)).quadratic
        (unaryBinaryOrthogonalBasis a p
          (p * lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible p) i) = _
  rw [unaryBinaryOrthogonalBasis_quadratic]
  fin_cases i <;> rfl

/-- The explicit source model has good-BONG orders
`[R, R+2-2e, R]` and first alpha `1`. -/
noncomputable def lemma712SourceJordanData
    [laws : DyadicDiscriminantClassLaws K]
    [BONGGoodExistenceLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) :
    BONG.UnaryBinaryJordanData a p
      (p * lemma712DiscriminantParameter (K := K))
      (lemma712_sourceBinaryAdmissible p) := by
  let e : Int := ramificationIndex K
  refine {
    center := ordUnit K a - e + 1
    radius := e - 1
    alpha := 1
    head_order := by omega
    first_order := by omega
    second_order := ?_
    alpha_nonnegative := by omega
    dual_alpha_nonnegative := by
      have hePos := ramificationIndex_pos (K := K)
      dsimp [e]
      omega
    alpha_le_halfGap := by omega
    alpha_half_or_odd := Or.inl (by omega)
  }
  have hdelta : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit
  change ordUnit K
      (p * (negativeQuarterUnit K * laws.discriminantUnit)) = _
  rw [ordUnit_mul, ordUnit_mul, hp, ordUnit_negativeQuarterUnit,
    hdelta]
  dsimp [e]
  omega

/-- The chosen source good BONG has the paper's order profile. -/
theorem lemma712SourceGoodBONG_order
    [laws : DyadicDiscriminantClassLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) (i : Fin 3) :
    (lemma712SourceJordanData a p hp).goodBONG.order i =
      ![ordUnit K a,
        ordUnit K a + 2 - 2 * (ramificationIndex K : Int),
        ordUnit K a] i := by
  rw [(lemma712SourceJordanData a p hp).goodBONG_order i]
  fin_cases i <;> dsimp [lemma712SourceJordanData] <;> omega

/-- The first alpha of the chosen source good BONG is exactly one. -/
theorem lemma712SourceGoodBONG_alpha
    [laws : DyadicDiscriminantClassLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) :
    (lemma712SourceJordanData a p hp).goodBONG.alphaValue 0 = 1 := by
  rw [(lemma712SourceJordanData a p hp).goodBONG_alpha_zero]
  rfl

/-- The target coefficients have orders `[R,R+2-2e,R]`. -/
theorem lemma712TargetValues_orders
    [laws : DyadicDiscriminantClassLaws K]
    (a ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ∀ i, ordUnit K (lemma712TargetValues a ε η i) =
      ![ordUnit K a,
        ordUnit K a + 2 - 2 * (ramificationIndex K : Int),
        ordUnit K a] i := by
  have hε : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hη : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  have hdelta : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit
  intro i
  fin_cases i
  · simp [lemma712TargetValues, ordUnit_mul, hε]
  · simp [lemma712TargetValues, lemma712DiscriminantParameter,
      ordUnit_mul, ordUnit_negativeQuarterUnit,
      ordUnit_uniformizerPowerUnit, hdelta, hε, hη]
    omega
  · simp [lemma712TargetValues, ordUnit_mul, hη]

/-- The first signed adjacent product is `Δη` times a square. -/
theorem lemma712TargetValues_firstAdjacent_squareFactor
    [laws : DyadicDiscriminantClassLaws K] (a ε η : Kˣ) :
    ∃ s : Kˣ,
      -(lemma712TargetValues a ε η 0 *
          lemma712TargetValues a ε η 1) =
        (laws.discriminantUnit * η) * s ^ 2 := by
  have hpi : IsSquare (uniformizerPowerUnit K (2 : Int)) :=
    isSquare_uniformizerPowerUnit_of_even (K := K) 2 ⟨1, by omega⟩
  have ha : IsSquare (a ^ 2) := ⟨a, by simp [pow_two]⟩
  have hε : IsSquare (ε ^ 2) := ⟨ε, by simp [pow_two]⟩
  have hsquare : IsSquare
      (-(negativeQuarterUnit K) * uniformizerPowerUnit K 2 *
        a ^ 2 * ε ^ 2) :=
    (((isSquare_neg_negativeQuarterUnit (K := K)).mul hpi).mul ha).mul hε
  rcases hsquare with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [pow_two, ← hs]
  apply Units.ext
  simp only [lemma712TargetValues_zero, lemma712TargetValues_one,
    lemma712DiscriminantParameter, Units.val_neg, Units.val_mul,
    Units.val_pow_eq_pow_val]
  ring

/-- The second signed adjacent product is `Δε` times a square. -/
theorem lemma712TargetValues_secondAdjacent_squareFactor
    [laws : DyadicDiscriminantClassLaws K] (a ε η : Kˣ) :
    ∃ s : Kˣ,
      -(lemma712TargetValues a ε η 1 *
          lemma712TargetValues a ε η 2) =
        (laws.discriminantUnit * ε) * s ^ 2 := by
  have hpi : IsSquare (uniformizerPowerUnit K (2 : Int)) :=
    isSquare_uniformizerPowerUnit_of_even (K := K) 2 ⟨1, by omega⟩
  have ha : IsSquare (a ^ 2) := ⟨a, by simp [pow_two]⟩
  have hη : IsSquare (η ^ 2) := ⟨η, by simp [pow_two]⟩
  have hsquare : IsSquare
      (-(negativeQuarterUnit K) * uniformizerPowerUnit K 2 *
        a ^ 2 * η ^ 2) :=
    (((isSquare_neg_negativeQuarterUnit (K := K)).mul hpi).mul ha).mul hη
  rcases hsquare with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [pow_two, ← hs]
  apply Units.ext
  simp only [lemma712TargetValues_one, lemma712TargetValues_two,
    lemma712DiscriminantParameter, Units.val_neg, Units.val_mul,
    Units.val_pow_eq_pow_val]
  ring

/-- Multiplication by the discriminant does not change the prescribed
defect `2e-1`. -/
theorem lemma712TargetValues_firstAdjacentDefect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (a ε η : Kˣ)
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    defectOrder (K := K)
        (-(lemma712TargetValues a ε η 0 *
          lemma712TargetValues a ε η 1)) =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
  rcases lemma712TargetValues_firstAdjacent_squareFactor a ε η with
    ⟨s, hs⟩
  rw [hs, defectOrder_mul_square]
  have hdelta : defectOrder (K := K) laws.discriminantUnit =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    unfold defectOrder
    rw [laws.discriminant_defect]
    rfl
  have hlt : defectOrder (K := K) η <
      defectOrder (K := K) laws.discriminantUnit := by
    rw [hηDefect, hdelta]
    exact_mod_cast (show
      2 * (ramificationIndex K : ℚ) - 1 <
        2 * (ramificationIndex K : ℚ) by linarith)
  rw [defectOrder_mul_eq_right_of_lt_left hlt, hηDefect]

/-- Multiplication by the discriminant does not change the prescribed
defect `1`. -/
theorem lemma712TargetValues_secondAdjacentDefect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (a ε η : Kˣ)
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ)) :
    defectOrder (K := K)
        (-(lemma712TargetValues a ε η 1 *
          lemma712TargetValues a ε η 2)) =
      (1 : WithTop ℚ) := by
  rcases lemma712TargetValues_secondAdjacent_squareFactor a ε η with
    ⟨s, hs⟩
  rw [hs, defectOrder_mul_square]
  have hdelta : defectOrder (K := K) laws.discriminantUnit =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    unfold defectOrder
    rw [laws.discriminant_defect]
    rfl
  have hlt : defectOrder (K := K) ε <
      defectOrder (K := K) laws.discriminantUnit := by
    rw [hεDefect, hdelta]
    have hePos := ramificationIndex_pos (K := K)
    exact_mod_cast (show (1 : ℚ) <
      2 * (ramificationIndex K : ℚ) by
        norm_cast
        omega)
  rw [defectOrder_mul_eq_right_of_lt_left hlt, hεDefect]

/-- The first adjacent target parameter is admissible. -/
theorem lemma712TargetValues_firstBinaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (a ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    IsBinaryParameterAdmissible
      (lemma712TargetValues a ε η 1 /
        lemma712TargetValues a ε η 0) := by
  let t := lemma712TargetValues a ε η 1 /
    lemma712TargetValues a ε η 0
  have horders := lemma712TargetValues_orders a ε η hεUnit hηUnit
  have hord : ordUnit K t =
      2 - 2 * (ramificationIndex K : Int) := by
    dsimp [t]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      horders (1 : Fin 3), horders (0 : Fin 3)]
    simp
    omega
  have hdefect : defectOrder (K := K) (-t) =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
    dsimp [t]
    rw [defectOrder_neg_div_eq_neg_mul]
    simpa [mul_comm] using
      lemma712TargetValues_firstAdjacentDefect a ε η hηDefect
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect t).2
  constructor
  · rw [hord]
    omega
  · apply
      Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    have hneg : ordUnit K (-t) = ordUnit K t := by
      apply WithTop.coe_injective
      simp only [coe_ordUnit, Units.val_neg, ord_neg]
    rw [hneg, hord, hdefect]
    have hq : (0 : ℚ) ≤
        ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) +
          (2 * (ramificationIndex K : ℚ) - 1) := by
      push_cast
      linarith
    exact_mod_cast hq

/-- The second adjacent target parameter has nonnegative order and hence is
admissible. -/
theorem lemma712TargetValues_secondBinaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    (a ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    IsBinaryParameterAdmissible
      (lemma712TargetValues a ε η 2 /
        lemma712TargetValues a ε η 1) := by
  apply isBinaryParameterAdmissible_of_ordUnit_nonneg
  have horders := lemma712TargetValues_orders a ε η hεUnit hηUnit
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    horders (2 : Fin 3), horders (1 : Fin 3)]
  simp
  have hePos := ramificationIndex_pos (K := K)
  omega

/-- Both adjacent parameters of the target coefficient list are admissible. -/
theorem lemma712TargetValues_binaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (a ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
      IsBinaryParameterAdmissible
        (lemma712TargetValues a ε η ⟨i.1 + 1, hi⟩ /
          lemma712TargetValues a ε η i) := by
  intro i hi
  have hiCases : i = (0 : Fin 3) ∨ i = (1 : Fin 3) := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    rcases hval with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hiCases with rfl | rfl
  · simpa using lemma712TargetValues_firstBinaryAdmissible
      a ε η hεUnit hηUnit hηDefect
  · simpa using lemma712TargetValues_secondBinaryAdmissible
      a ε η hεUnit hηUnit

/-- The target and source coefficient lists have the same determinant square
class. -/
theorem lemma712TargetSource_determinantSquare
    [laws : DyadicDiscriminantClassLaws K]
    (a p ε η : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (lemma712TargetValues a ε η) *
        diagonalUnitDeterminant (lemma712SourceValues a p)) := by
  have hpi : uniformizerPowerUnit K (2 : Int) =
      uniformizerPowerUnit K (1 : Int) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    rfl
  refine ⟨lemma712DiscriminantParameter (K := K) *
      uniformizerPowerUnit K 1 * a ^ 2 * p * ε * η, ?_⟩
  apply Units.ext
  simp only [diagonalUnitDeterminant, Fin.prod_univ_three,
    lemma712TargetValues_zero, lemma712TargetValues_one,
    lemma712TargetValues_two, lemma712SourceValues_zero,
    lemma712SourceValues_one, lemma712SourceValues_two,
    Units.val_mul, Units.val_pow_eq_pow_val]
  rw [congrArg Units.val hpi]
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- The adjacent Hilbert symbol of the target list is `(η,ε)`. -/
theorem lemma712TargetValues_adjacentHilbert
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    hilbertSymbol K
        (-(lemma712TargetValues a ε η 0 *
          lemma712TargetValues a ε η 1))
        (-(lemma712TargetValues a ε η 1 *
          lemma712TargetValues a ε η 2)) =
      hilbertSymbol K η ε := by
  rcases lemma712TargetValues_firstAdjacent_squareFactor a ε η with
    ⟨s, hs⟩
  rcases lemma712TargetValues_secondAdjacent_squareFactor a ε η with
    ⟨t, ht⟩
  rw [hs, ht, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right]
  have hdeltaOrder : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  have hdeltaDelta :
      hilbertSymbol K laws.discriminantUnit laws.discriminantUnit = 1 := by
    apply (hilbertSymbol_discriminant_eq_one_iff_even_order
      laws.discriminantUnit).2
    rw [hdeltaOrder]
    exact ⟨0, by omega⟩
  have hdeltaEpsilon : hilbertSymbol K laws.discriminantUnit ε = 1 := by
    apply (hilbertSymbol_discriminant_eq_one_iff_even_order ε).2
    rw [hεOrder]
    exact ⟨0, by omega⟩
  have hdeltaEta : hilbertSymbol K laws.discriminantUnit η = 1 := by
    apply (hilbertSymbol_discriminant_eq_one_iff_even_order η).2
    rw [hηOrder]
    exact ⟨0, by omega⟩
  calc
    hilbertSymbol K (laws.discriminantUnit * η)
        (laws.discriminantUnit * ε) =
      hilbertSymbol K laws.discriminantUnit
          (laws.discriminantUnit * ε) *
        hilbertSymbol K η (laws.discriminantUnit * ε) :=
      hilbertSymbol_mul_left K laws.discriminantUnit η
        (laws.discriminantUnit * ε)
    _ = (hilbertSymbol K laws.discriminantUnit laws.discriminantUnit *
          hilbertSymbol K laws.discriminantUnit ε) *
        (hilbertSymbol K η laws.discriminantUnit *
          hilbertSymbol K η ε) := by
      rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
    _ = hilbertSymbol K η ε := by
      rw [hdeltaDelta, hdeltaEpsilon,
        hilbertSymbol_comm K η laws.discriminantUnit, hdeltaEta]
      simp

/-- In the source list, the second signed adjacent product is `Δ` times a
square. -/
theorem lemma712SourceValues_secondAdjacent_squareFactor
    [laws : DyadicDiscriminantClassLaws K] (a p : Kˣ) :
    ∃ s : Kˣ,
      -(lemma712SourceValues a p 1 * lemma712SourceValues a p 2) =
        laws.discriminantUnit * s ^ 2 := by
  have hsquare : IsSquare (-(negativeQuarterUnit K) * p ^ 2) :=
    (isSquare_neg_negativeQuarterUnit (K := K)).mul
      ⟨p, by simp [pow_two]⟩
  rcases hsquare with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [pow_two, ← hs]
  apply Units.ext
  simp only [lemma712SourceValues_one, lemma712SourceValues_two,
    lemma712DiscriminantParameter, Units.val_neg, Units.val_mul,
    Units.val_pow_eq_pow_val]
  ring

/-- The source ternary space is anisotropic: its adjacent Hilbert symbol is
`-1`, because the first signed product has odd order in the unramified norm
character. -/
theorem lemma712SourceValues_adjacentHilbert
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) :
    hilbertSymbol K
        (-(lemma712SourceValues a p 0 * lemma712SourceValues a p 1))
        (-(lemma712SourceValues a p 1 * lemma712SourceValues a p 2)) =
      -1 := by
  rcases lemma712SourceValues_secondAdjacent_squareFactor a p with ⟨s, hs⟩
  rw [hs, hilbertSymbol_mul_square_right,
    hilbertSymbol_comm K
      (-(lemma712SourceValues a p 0 * lemma712SourceValues a p 1))
      laws.discriminantUnit]
  have hodd : Odd (ordUnit K
      (-(lemma712SourceValues a p 0 * lemma712SourceValues a p 1))) := by
    refine ⟨ordUnit K a, ?_⟩
    simp only [lemma712SourceValues_zero, lemma712SourceValues_one,
      ordUnit_neg, ordUnit_mul, hp]
    omega
  apply (hilbertSymbol_eq_neg_one_iff K
    laws.discriminantUnit
    (-(lemma712SourceValues a p 0 * lemma712SourceValues a p 1))).2
  rw [isQuadraticNorm_discriminant_iff_even_order]
  exact Int.not_even_iff_odd.mpr hodd

/-- The target and source ternary coefficient lists have the same Hasse
invariant under the Hilbert condition of Lemma 7.12(ii). -/
theorem lemma712TargetSource_hasse_eq
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a p ε η : Kˣ)
    (hp : ordUnit K p = ordUnit K a + 1)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hhilbert : hilbertSymbol K ε η = -1) :
    diagonalHasseSymbol K (lemma712TargetValues a ε η) =
      diagonalHasseSymbol K (lemma712SourceValues a p) := by
  apply diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    lemma712TargetValues_adjacentHilbert a ε η hεUnit hηUnit,
    lemma712SourceValues_adjacentHilbert a p hp,
    ← hilbertSymbol_comm K ε η, hhilbert]

/-- Local diagonal classification realizes the exact target coefficients in
the explicit source ternary space. -/
theorem lemma712Target_diagonalRepresents_source
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a p ε η : Kˣ)
    (hp : ordUnit K p = ordUnit K a + 1)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hhilbert : hilbertSymbol K ε η = -1) :
    DiagonalRepresents
      (diagonalUnitCoefficients (lemma712TargetValues a ε η))
      (diagonalUnitCoefficients (lemma712SourceValues a p)) :=
  DyadicDiagonalClassificationLaws.represents_of_invariants
    (lemma712TargetValues a ε η) (lemma712SourceValues a p)
    (lemma712TargetSource_determinantSquare a p ε η)
    (lemma712TargetSource_hasse_eq a p ε η hp
      hεUnit hηUnit hhilbert)

/-- Beli (2019), Lemma 7.12(ii), in the generalized normalization needed by
Lemma 7.14.  The binary coefficient `p` need only have order one larger than
the unary coefficient `a`; the resulting good BONG has the exact three
values displayed in the paper. -/
theorem exists_beli2019Lemma712_ii_goodBONG
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
    (a p ε η : Kˣ)
    (hp : ordUnit K p = ordUnit K a + 1)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K ε η = -1) :
    ∃ b : GoodBONG
        (unaryBinaryModelSpace a p
          (p * lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible p))
        (unaryBinaryModelLattice (K := K)) 3,
      ∀ i, b.valueUnit i = lemma712TargetValues a ε η i := by
  let sourceData := lemma712SourceJordanData a p hp
  let reference := sourceData.goodBONG
  let sourceBasis := lemma712SourceOrthogonalBasisData a p
  have hsourceRep : DiagonalRepresents
      (diagonalUnitCoefficients (lemma712SourceValues a p))
      (diagonalUnitCoefficients reference.valueUnit) := by
    have h := sourceBasis.diagonalRepresents_bong reference.toBONG
    have hx : sourceBasis.valueUnit = lemma712SourceValues a p := by
      funext i
      exact lemma712SourceOrthogonalBasisData_valueUnit a p i
    rw [hx] at h
    exact h
  have htargetSource := lemma712Target_diagonalRepresents_source
    a p ε η hp hεUnit hηUnit hhilbert
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients (lemma712TargetValues a ε η))
      (diagonalUnitCoefficients reference.valueUnit) :=
    htargetSource.trans_exact hsourceRep
  let R := ordUnit K a
  let S := R + 2 - 2 * (ramificationIndex K : Int)
  have horders : ∀ i,
      ordUnit K (lemma712TargetValues a ε η i) = ![R, S, R] i := by
    simpa [R, S] using
      lemma712TargetValues_orders a ε η hεUnit hηUnit
  have hadmissible := lemma712TargetValues_binaryAdmissible
    a ε η hεUnit hηUnit hηDefect
  have hhalf :
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = (((1 : Int) : ℚ) : WithTop ℚ) := by
    apply congrArg WithTop.some
    dsimp [S, R]
    push_cast
    ring
  have hleft :
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K)
            (-(lemma712TargetValues a ε η 0 *
              lemma712TargetValues a ε η 1))) =
        (((1 : Int) : ℚ) : WithTop ℚ) := by
    rw [lemma712TargetValues_firstAdjacentDefect a ε η hηDefect]
    apply congrArg WithTop.some
    dsimp [S, R]
    push_cast
    ring
  have hright : defectOrder (K := K)
      (-(lemma712TargetValues a ε η 1 *
        lemma712TargetValues a ε η 2)) =
      (((1 : Int) : ℚ) : WithTop ℚ) := by
    simpa using
      lemma712TargetValues_secondAdjacentDefect a ε η hεDefect
  rcases exists_exactTernaryRealization reference
      (lemma712TargetValues a ε η) R S 1 hrep horders hadmissible
      hhalf hleft hright with ⟨target⟩
  have hsameOrders : reference.SameOrders target.bong := by
    intro i
    calc
      reference.order i = ![R, S, R] i := by
        simpa [reference, sourceData, R, S] using
          lemma712SourceGoodBONG_order a p hp i
      _ = target.bong.order i := (target.orders i).symm
  have houter : reference.order (0 : Fin 3) = reference.order 2 := by
    rw [hsameOrders (0 : Fin 3), hsameOrders (2 : Fin 3),
      target.orders (0 : Fin 3), target.orders (2 : Fin 3)]
    rfl
  have halpha : reference.alphaValue (0 : Fin 2) =
      target.bong.alphaValue 0 := by
    calc
      reference.alphaValue (0 : Fin 2) = 1 := by
        simpa [reference, sourceData] using
          lemma712SourceGoodBONG_alpha a p hp
      _ = target.bong.alphaValue 0 := by
        simpa using target.firstAlpha.symm
  have hisometric : Lattice.IsIsometric
      (unaryBinaryModelSpace a p
        (p * lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible p))
      (unaryBinaryModelSpace a p
        (p * lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible p))
      (unaryBinaryModelLattice (K := K)) target.lattice :=
    (reference.beli2019Lemma711 target.bong hsameOrders houter).2 halpha
  rcases hisometric with ⟨f⟩
  let result := target.bong.mapLatticeIsometry f.symm
  refine ⟨result, ?_⟩
  intro i
  apply Units.ext
  change (target.bong.toBONG.mapLatticeIsometry f.symm).value i =
    ((lemma712TargetValues a ε η i : Kˣ) : K)
  rw [BONG.value_mapLatticeIsometry]
  exact congrArg Units.val (target.valueUnits i)

end BONG.GoodBONG

end Bong
