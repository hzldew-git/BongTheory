/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma712
import Bong.Dyadic.ValuationUnitDefect

/-!
# Beli (2019), Lemma 7.12(i)

This file proves the hyperbolic branch of Lemma 7.12.  For a source lattice
\`<a> ⊥ [p,-p/4]\` with \`ord(p)=ord(a)+1\`, and every valuation unit
\`ε\`, it constructs a good BONG with the exact values

\`[aε, -π^(2-2e)aε, a]\`.

The binary source is the standard integral model of the scaled hyperbolic
plane \`H(πa/2)\`; allowing any \`p\` of the prescribed order makes the
result reusable in the induction proving Corollary 7.13.
-/

namespace Bong
open Dyadic
universe u
namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable def lemma712ISourceValues (a p : Kˣ) : Fin 3 → Kˣ :=
  ![a, p, p * negativeQuarterUnit K]

noncomputable def lemma712ITargetValues (a ε : Kˣ) : Fin 3 → Kˣ :=
  ![a * ε,
    -(uniformizerPowerUnit K (2 - 2 * (ramificationIndex K : Int)) *
      a * ε),
    a]

@[simp] theorem lemma712ISourceValues_zero (a p : Kˣ) :
    lemma712ISourceValues a p 0 = a := rfl
@[simp] theorem lemma712ISourceValues_one (a p : Kˣ) :
    lemma712ISourceValues a p 1 = p := rfl
@[simp] theorem lemma712ISourceValues_two (a p : Kˣ) :
    lemma712ISourceValues a p 2 = p * negativeQuarterUnit K := rfl

@[simp] theorem lemma712ITargetValues_zero (a ε : Kˣ) :
    lemma712ITargetValues a ε 0 = a * ε := rfl
@[simp] theorem lemma712ITargetValues_one (a ε : Kˣ) :
    lemma712ITargetValues a ε 1 =
      -(uniformizerPowerUnit K (2 - 2 * (ramificationIndex K : Int)) *
        a * ε) := rfl
@[simp] theorem lemma712ITargetValues_two (a ε : Kˣ) :
    lemma712ITargetValues a ε 2 = a := rfl

theorem lemma712I_sourceBinaryAdmissible (p : Kˣ) :
    IsBinaryParameterAdmissible
      ((p * negativeQuarterUnit K) / p) := by
  have hratio : (p * negativeQuarterUnit K) / p =
      negativeQuarterUnit K := by simp
  rw [hratio]
  refine ⟨standardEndpointShear (K := K),
    standardEndpointShear_two_integral (K := K), ?_⟩
  exact negativeQuarter_standardEndpointShear_diagonal_integral (K := K)

noncomputable def lemma712ISourceOrthogonalBasisData (a p : Kˣ) :
    BONG.OrthogonalBasisData
      (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p)) 3 :=
  ⟨unaryBinaryOrthogonalBasis a p (p * negativeQuarterUnit K)
      (lemma712I_sourceBinaryAdmissible p),
    unaryBinaryOrthogonalBasis_isOrtho a p (p * negativeQuarterUnit K)
      (lemma712I_sourceBinaryAdmissible p)⟩

@[simp] theorem lemma712ISourceOrthogonalBasisData_valueUnit
    (a p : Kˣ) (i : Fin 3) :
    (lemma712ISourceOrthogonalBasisData a p).valueUnit i =
      lemma712ISourceValues a p i := by
  apply Units.ext
  change
    (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
      (lemma712I_sourceBinaryAdmissible p)).quadratic
      (unaryBinaryOrthogonalBasis a p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p) i) = _
  rw [unaryBinaryOrthogonalBasis_quadratic]
  fin_cases i <;> rfl

noncomputable def lemma712ISourceJordanData
    [BONGGoodExistenceLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) :
    BONG.UnaryBinaryJordanData a p (p * negativeQuarterUnit K)
      (lemma712I_sourceBinaryAdmissible p) := by
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
  change ordUnit K (p * negativeQuarterUnit K) = _
  rw [ordUnit_mul, hp, ordUnit_negativeQuarterUnit]
  dsimp [e]
  omega

theorem lemma712ISourceGoodBONG_order
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) (i : Fin 3) :
    (lemma712ISourceJordanData a p hp).goodBONG.order i =
      ![ordUnit K a,
        ordUnit K a + 2 - 2 * (ramificationIndex K : Int),
        ordUnit K a] i := by
  rw [(lemma712ISourceJordanData a p hp).goodBONG_order i]
  fin_cases i <;> dsimp [lemma712ISourceJordanData] <;> omega

theorem lemma712ISourceGoodBONG_alpha
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    (a p : Kˣ) (hp : ordUnit K p = ordUnit K a + 1) :
    (lemma712ISourceJordanData a p hp).goodBONG.alphaValue 0 = 1 := by
  rw [(lemma712ISourceJordanData a p hp).goodBONG_alpha_zero]
  rfl

theorem lemma712ITargetValues_orders
    (a ε : Kˣ) (hεUnit : IsValuationUnit K (ε : K)) :
    ∀ i, ordUnit K (lemma712ITargetValues a ε i) =
      ![ordUnit K a,
        ordUnit K a + 2 - 2 * (ramificationIndex K : Int),
        ordUnit K a] i := by
  have hε : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  intro i
  fin_cases i
  · simp [lemma712ITargetValues, ordUnit_mul, hε]
  · change ordUnit K
        (-(uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int)) * a * ε)) =
        ordUnit K a + 2 - 2 * (ramificationIndex K : Int)
    rw [ordUnit_neg, ordUnit_mul, ordUnit_mul,
      ordUnit_uniformizerPowerUnit, hε]
    omega
  · simp [lemma712ITargetValues]

theorem lemma712ITargetValues_firstAdjacent_isSquare (a ε : Kˣ) :
    IsSquare (-(lemma712ITargetValues a ε 0 *
      lemma712ITargetValues a ε 1)) := by
  have hEven : Even (2 - 2 * (ramificationIndex K : Int)) :=
    ⟨1 - (ramificationIndex K : Int), by ring⟩
  have hpi := isSquare_uniformizerPowerUnit_of_even (K := K)
    (2 - 2 * (ramificationIndex K : Int)) hEven
  have hx : IsSquare ((a * ε) ^ 2) := ⟨a * ε, by simp [pow_two]⟩
  have heq :
      -(lemma712ITargetValues a ε 0 * lemma712ITargetValues a ε 1) =
        uniformizerPowerUnit K
            (2 - 2 * (ramificationIndex K : Int)) *
          (a * ε) ^ 2 := by
    apply Units.ext
    simp only [lemma712ITargetValues_zero, lemma712ITargetValues_one,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [heq]
  exact hpi.mul hx

theorem lemma712ITargetValues_secondAdjacent_squareFactor (a ε : Kˣ) :
    ∃ z : Kˣ,
      -(lemma712ITargetValues a ε 1 * lemma712ITargetValues a ε 2) =
        ε * z ^ 2 := by
  let z := uniformizerPowerUnit K
    (1 - (ramificationIndex K : Int)) * a
  refine ⟨z, ?_⟩
  have hpi : uniformizerPowerUnit K
        (2 - 2 * (ramificationIndex K : Int)) =
      uniformizerPowerUnit K
        (1 - (ramificationIndex K : Int)) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    ring
  have hz : z ^ 2 =
      uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int)) * a ^ 2 := by
    dsimp [z]
    rw [mul_pow, ← hpi]
  rw [hz]
  apply Units.ext
  simp only [lemma712ITargetValues_one, lemma712ITargetValues_two,
    Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

theorem lemma712ITargetValues_firstBinaryAdmissible
    [QuadraticDefectLaws K] (a ε : Kˣ) :
    IsBinaryParameterAdmissible
      (lemma712ITargetValues a ε 1 / lemma712ITargetValues a ε 0) := by
  let t := lemma712ITargetValues a ε 1 / lemma712ITargetValues a ε 0
  have ht : t = -uniformizerPowerUnit K
      (2 - 2 * (ramificationIndex K : Int)) := by
    dsimp [t]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_mul]
    field_simp [Units.ne_zero a, Units.ne_zero ε]
  have hord : ordUnit K t =
      2 - 2 * (ramificationIndex K : Int) := by
    rw [ht, ordUnit_neg, ordUnit_uniformizerPowerUnit]
  have hEven : Even (2 - 2 * (ramificationIndex K : Int)) :=
    ⟨1 - (ramificationIndex K : Int), by ring⟩
  have hminusSquare : IsSquare (-t) := by
    rw [ht]
    have heq : -(-uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int))) =
        uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int)) := by simp
    rw [heq]
    exact isSquare_uniformizerPowerUnit_of_even (K := K) _ hEven
  have hdefect : defectOrder (K := K) (-t) = ⊤ :=
    defectOrder_eq_top_of_isSquare hminusSquare
  apply (isBinaryParameterAdmissible_iff_order_add_two_e_and_defect t).2
  constructor
  · rw [hord]
    omega
  · apply
      Dyadic.hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    have hordNeg : ordUnit K (-t) =
        2 - 2 * (ramificationIndex K : Int) := by
      rw [ordUnit_neg, hord]
    rw [hordNeg, hdefect]
    exact le_top

theorem lemma712ITargetValues_secondBinaryAdmissible
    (a ε : Kˣ) (hεUnit : IsValuationUnit K (ε : K)) :
    IsBinaryParameterAdmissible
      (lemma712ITargetValues a ε 2 / lemma712ITargetValues a ε 1) := by
  apply isBinaryParameterAdmissible_of_ordUnit_nonneg
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    lemma712ITargetValues_two, lemma712ITargetValues_one,
    ordUnit_neg, ordUnit_mul, ordUnit_mul,
    ordUnit_uniformizerPowerUnit]
  have hε : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  rw [hε]
  have hePos := ramificationIndex_pos (K := K)
  omega

theorem lemma712ITargetValues_binaryAdmissible
    [QuadraticDefectLaws K] (a ε : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K)) :
    ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
      IsBinaryParameterAdmissible
        (lemma712ITargetValues a ε ⟨i.1 + 1, hi⟩ /
          lemma712ITargetValues a ε i) := by
  intro i hi
  have hiCases : i = (0 : Fin 3) ∨ i = (1 : Fin 3) := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    rcases hval with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hiCases with rfl | rfl
  · simpa using lemma712ITargetValues_firstBinaryAdmissible a ε
  · simpa using lemma712ITargetValues_secondBinaryAdmissible a ε hεUnit

theorem lemma712ITargetSource_determinantSquare (a p ε : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (lemma712ITargetValues a ε) *
        diagonalUnitDeterminant (lemma712ISourceValues a p)) := by
  have hEven : Even (2 - 2 * (ramificationIndex K : Int)) :=
    ⟨1 - (ramificationIndex K : Int), by ring⟩
  have hpi := isSquare_uniformizerPowerUnit_of_even (K := K)
    (2 - 2 * (ramificationIndex K : Int)) hEven
  have ha : IsSquare (a ^ 4) :=
    ⟨a ^ 2, by simpa using (pow_add a 2 2)⟩
  have hε : IsSquare (ε ^ 2) := ⟨ε, by simp [pow_two]⟩
  have hp : IsSquare (p ^ 2) := ⟨p, by simp [pow_two]⟩
  have hsquare : IsSquare
      ((-(negativeQuarterUnit K)) *
        uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int)) *
        a ^ 4 * ε ^ 2 * p ^ 2) :=
    ((((isSquare_neg_negativeQuarterUnit (K := K)).mul hpi).mul ha).mul hε).mul hp
  have heq :
      diagonalUnitDeterminant (lemma712ITargetValues a ε) *
          diagonalUnitDeterminant (lemma712ISourceValues a p) =
        (-(negativeQuarterUnit K)) *
          uniformizerPowerUnit K
            (2 - 2 * (ramificationIndex K : Int)) *
          a ^ 4 * ε ^ 2 * p ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Fin.prod_univ_three,
      lemma712ITargetValues_zero, lemma712ITargetValues_one,
      lemma712ITargetValues_two, lemma712ISourceValues_zero,
      lemma712ISourceValues_one, lemma712ISourceValues_two,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rwa [heq]

theorem lemma712ISourceValues_secondAdjacent_isSquare (a p : Kˣ) :
    IsSquare (-(lemma712ISourceValues a p 1 *
      lemma712ISourceValues a p 2)) := by
  have heq :
      -(lemma712ISourceValues a p 1 * lemma712ISourceValues a p 2) =
        (-(negativeQuarterUnit K)) * p ^ 2 := by
    apply Units.ext
    simp only [lemma712ISourceValues_one, lemma712ISourceValues_two,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [heq]
  exact (isSquare_neg_negativeQuarterUnit (K := K)).mul
    ⟨p, by simp [pow_two]⟩

theorem lemma712ITargetSource_hasse_eq
    [HilbertSymbolLaws K] (a p ε : Kˣ) :
    diagonalHasseSymbol K (lemma712ITargetValues a ε) =
      diagonalHasseSymbol K (lemma712ISourceValues a p) := by
  apply diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    hilbertSymbol_eq_one_of_isSquare_left K
      (lemma712ITargetValues_firstAdjacent_isSquare a ε),
    hilbertSymbol_eq_one_of_isSquare_right K
      (lemma712ISourceValues_secondAdjacent_isSquare a p)]

theorem lemma712ITarget_diagonalRepresents_source
    [HilbertSymbolLaws K] [DyadicDiagonalClassificationLaws K]
    (a p ε : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients (lemma712ITargetValues a ε))
      (diagonalUnitCoefficients (lemma712ISourceValues a p)) :=
  DyadicDiagonalClassificationLaws.represents_of_invariants
    (lemma712ITargetValues a ε) (lemma712ISourceValues a p)
    (lemma712ITargetSource_determinantSquare a p ε)
    (lemma712ITargetSource_hasse_eq a p ε)

theorem lemma712ITargetValues_firstAdjacentDefect (a ε : Kˣ) :
    defectOrder (K := K)
      (-(lemma712ITargetValues a ε 0 * lemma712ITargetValues a ε 1)) = ⊤ :=
  defectOrder_eq_top_of_isSquare
    (lemma712ITargetValues_firstAdjacent_isSquare a ε)

theorem lemma712ITargetValues_secondAdjacentDefect (a ε : Kˣ) :
    defectOrder (K := K)
      (-(lemma712ITargetValues a ε 1 * lemma712ITargetValues a ε 2)) =
        defectOrder (K := K) ε := by
  rcases lemma712ITargetValues_secondAdjacent_squareFactor a ε with ⟨z, hz⟩
  rw [hz, IsCoefficientScale.defectOrder_mul_square]

theorem exists_beli2019Lemma712_i_goodBONG
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [PerfectResidueFieldLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (a p ε : Kˣ)
    (hp : ordUnit K p = ordUnit K a + 1)
    (hεUnit : IsValuationUnit K (ε : K)) :
    ∃ b : GoodBONG
        (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
          (lemma712I_sourceBinaryAdmissible p))
        (unaryBinaryModelLattice (K := K)) 3,
      ∀ i, b.valueUnit i = lemma712ITargetValues a ε i := by
  let sourceData := lemma712ISourceJordanData a p hp
  let reference := sourceData.goodBONG
  let sourceBasis := lemma712ISourceOrthogonalBasisData a p
  have hsourceRep : DiagonalRepresents
      (diagonalUnitCoefficients (lemma712ISourceValues a p))
      (diagonalUnitCoefficients reference.valueUnit) := by
    have h := sourceBasis.diagonalRepresents_bong reference.toBONG
    have hx : sourceBasis.valueUnit = lemma712ISourceValues a p := by
      funext i
      exact lemma712ISourceOrthogonalBasisData_valueUnit a p i
    rw [hx] at h
    exact h
  have htargetSource := lemma712ITarget_diagonalRepresents_source a p ε
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients (lemma712ITargetValues a ε))
      (diagonalUnitCoefficients reference.valueUnit) :=
    htargetSource.trans_exact hsourceRep
  let R := ordUnit K a
  let S := R + 2 - 2 * (ramificationIndex K : Int)
  have horders : ∀ i,
      ordUnit K (lemma712ITargetValues a ε i) = ![R, S, R] i := by
    simpa [R, S] using lemma712ITargetValues_orders a ε hεUnit
  have hadmissible :=
    lemma712ITargetValues_binaryAdmissible a ε hεUnit
  have hhalf :
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = (((1 : Int) : ℚ) : WithTop ℚ) := by
    apply congrArg WithTop.some
    dsimp [S, R]
    push_cast
    ring
  have hleftLower :
      ((((1 : Int) : ℚ) : WithTop ℚ)) ≤
        ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K)
            (-(lemma712ITargetValues a ε 0 *
              lemma712ITargetValues a ε 1))) := by
    rw [lemma712ITargetValues_firstAdjacentDefect]
    exact le_top
  have hrightLower :
      ((((1 : Int) : ℚ) : WithTop ℚ)) ≤
        defectOrder (K := K)
          (-(lemma712ITargetValues a ε 1 *
            lemma712ITargetValues a ε 2)) := by
    rw [lemma712ITargetValues_secondAdjacentDefect]
    exact defectOrder_one_le_of_valuationUnit ε hεUnit
  rcases exists_exactTernaryRealization_of_halfGap reference
      (lemma712ITargetValues a ε) R S 1 hrep horders hadmissible
      hhalf hleftLower hrightLower with ⟨target⟩
  have hsameOrders : reference.SameOrders target.bong := by
    intro i
    calc
      reference.order i = ![R, S, R] i := by
        simpa [reference, sourceData, R, S] using
          lemma712ISourceGoodBONG_order a p hp i
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
          lemma712ISourceGoodBONG_alpha a p hp
      _ = target.bong.alphaValue 0 := by
        simpa using target.firstAlpha.symm
  have hisometric : Lattice.IsIsometric
      (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p))
      (unaryBinaryModelSpace a p (p * negativeQuarterUnit K)
        (lemma712I_sourceBinaryAdmissible p))
      (unaryBinaryModelLattice (K := K)) target.lattice :=
    (reference.beli2019Lemma711 target.bong hsameOrders houter).2 halpha
  rcases hisometric with ⟨f⟩
  let result := target.bong.mapLatticeIsometry f.symm
  refine ⟨result, ?_⟩
  intro i
  apply Units.ext
  change (target.bong.toBONG.mapLatticeIsometry f.symm).value i =
    ((lemma712ITargetValues a ε i : Kˣ) : K)
  rw [BONG.value_mapLatticeIsometry]
  exact congrArg Units.val (target.valueUnits i)

end BONG.GoodBONG
end Bong
