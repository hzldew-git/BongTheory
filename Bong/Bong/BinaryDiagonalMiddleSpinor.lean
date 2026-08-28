/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalMiddleSpinorOdd
import Bong.Bong.BeliLemma313
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.DiscriminantClassProof

/-!
# The full middle-range binary spinor formula

For a diagonal binary parameter of order `R > 2e`, put
`a♭ = π^(R - 2e) ε(a)`.  Thus `a = a♭ (π^e)^2`.  The main point of this
file is to identify integral reflections of the lattice `<1,a>` with norm
generators for `<1,a♭>`.  Together with the already proved local
norm-generator theorem, this gives both even branches of Xu (1993),
Proposition 2.2 and Beli (2003), Lemma 3.7 in the middle range.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The parameter obtained by removing the ramification square `π^(2e)`.
This is the parameter occurring on the right of Beli (2003), Lemma 3.13(i).
-/
noncomputable def binaryMiddleShiftedParameter (a : Kˣ) : Kˣ :=
  uniformizerPowerUnit K
      (ordUnit K a - 2 * (ramificationIndex K : Int)) *
    normalizedUnitPart K a

@[simp]
theorem ordUnit_binaryMiddleShiftedParameter (a : Kˣ) :
    ordUnit K (binaryMiddleShiftedParameter (K := K) a) =
      ordUnit K a - 2 * (ramificationIndex K : Int) := by
  unfold binaryMiddleShiftedParameter
  rw [ordUnit_uniformizerPower_mul_valuationUnit]
  exact normalizedUnitPart_isValuationUnit K a

/-- Exact factorization `a = a♭ (π^e)^2`. -/
theorem binaryMiddleShiftedParameter_mul_ramificationSquare (a : Kˣ) :
    binaryMiddleShiftedParameter (K := K) a *
        uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 = a := by
  unfold binaryMiddleShiftedParameter
  have hpower :
      uniformizerPowerUnit K
            (ordUnit K a - 2 * (ramificationIndex K : Int)) *
          uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 =
        uniformizerPowerUnit K (ordUnit K a) := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega
  calc
    uniformizerPowerUnit K
          (ordUnit K a - 2 * (ramificationIndex K : Int)) *
        normalizedUnitPart K a *
          uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 =
        (uniformizerPowerUnit K
            (ordUnit K a - 2 * (ramificationIndex K : Int)) *
          uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2) *
            normalizedUnitPart K a := by ac_rfl
    _ = uniformizerPowerUnit K (ordUnit K a) *
          normalizedUnitPart K a := by rw [hpower]
    _ = a := uniformizerPower_mul_normalizedUnitPart K a

theorem binaryMiddleShiftedParameter_order_pos
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    0 < ordUnit K (binaryMiddleShiftedParameter (K := K) a) := by
  rw [ordUnit_binaryMiddleShiftedParameter]
  omega

theorem binaryMiddleShiftedParameter_mem_integerRing
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    (binaryMiddleShiftedParameter (K := K) a : K) ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  change (0 : WithTop Int) ≤
    ord K (binaryMiddleShiftedParameter (K := K) a : K)
  rw [← coe_ordUnit]
  exact_mod_cast
    (binaryMiddleShiftedParameter_order_pos (K := K) a hR).le

/-- An integral unit value represented by the shifted diagonal model gives
an element of its norm-generator square-class group.  This is the forward
half of the reflection--norm-generator bridge. -/
theorem squareClass_mem_shiftedNormGeneratorGroup_of_representation
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a u : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hu : IsValuationUnit K (u : K))
    {x y : K} (hx : x ∈ IntegerRing K) (hy : y ∈ IntegerRing K)
    (hvalue : x ^ 2 +
        (binaryMiddleShiftedParameter (K := K) a : K) * y ^ 2 =
      (u : K)) :
    squareClass K u ∈ beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a) := by
  let shifted := binaryMiddleShiftedParameter (K := K) a
  have hshiftedIntegral : (shifted : K) ∈ IntegerRing K := by
    simpa [shifted] using
      binaryMiddleShiftedParameter_mem_integerRing (K := K) a hR
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (shifted : K) ∈ IntegerRing K := by
    simpa using hshiftedIntegral
  let z : Fin 2 → K := ![x, y]
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · simpa [z] using hx
    · simpa [z] using hy
  let uO : valuationUnitSubgroup K := ⟨u, hu⟩
  have hvalueModel :
      (QuadraticSpace.binaryModel shifted 0).quadratic z =
        ((uO : Kˣ) : K) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simpa [z, shifted, uO] using hvalue
  have hzGenerator : Lattice.IsNormGenerator
      (QuadraticSpace.binaryModel shifted 0)
      (binaryModelLattice (K := K)) z :=
    scratch_isNormGenerator_binaryModel_of_mem_of_unit_value
      shifted 0 htwo hdiag z hzMem uO hvalueModel
  let b := binaryExactModelBONG shifted 0 htwo hdiag
  have hratio : b.normGeneratorValueRatioUnit z hzGenerator = u := by
    apply Units.ext
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit]
    rw [binaryExactModelBONG_value_zero, div_one, hvalueModel]
  have hclass : b.normGeneratorValueRatioClass z hzGenerator ∈
      beliNormGeneratorGroup K b.binaryParameter :=
    scratch_normGeneratorValueRatioClass_mem_beliNormGeneratorGroup
      b z hzGenerator
  have hmapped :=
    valuationUnitClassToSquareClass_mem_beliNormGeneratorGroup
      (K := K) hclass
  rw [binaryExactModelBONG_binaryParameter] at hmapped
  change squareClass K (b.normGeneratorValueRatioUnit z hzGenerator) ∈
    beliNormGeneratorSquareClassGroup K shifted at hmapped
  rwa [hratio] at hmapped

/-- A diagonal value whose first coordinate has order at most `e` becomes a
norm-generator value after multiplying the second coordinate by `π^e` and
normalizing the first coordinate to one. -/
theorem squareClass_diagonalValue_mem_shiftedNormGenerator_of_first_order
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    {x y : K} (hx0 : x ≠ 0)
    (hxOrder : ordUnit K (Units.mk0 x hx0) ≤
      (ramificationIndex K : Int))
    (hyIntegral : y ∈ IntegerRing K)
    (hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0) :
    squareClass K (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) ∈
      beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) := by
  let xu : Kˣ := Units.mk0 x hx0
  have hxOrder' : ordUnit K xu ≤ (ramificationIndex K : Int) := by
    simpa [xu] using hxOrder
  by_cases hy0 : y = 0
  · have hclassOne :
        squareClass K
            (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) = 1 := by
      let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
      have hqU : qU = xu ^ 2 := by
        apply Units.ext
        simp [qU, xu, hy0]
      change squareClass K qU = 1
      rw [hqU]
      change squareClass K (xu ^ 2) = squareClass K (1 : Kˣ)
      simpa [pow_two] using squareClass_mul_square K (1 : Kˣ) xu
    rw [hclassOne]
    exact (beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a)).one_mem
  let yu : Kˣ := Units.mk0 y hy0
  have hyOrder : 0 ≤ ordUnit K yu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing yu
      (by simpa [yu] using hyIntegral)
  let t : Kˣ := uniformizerPowerUnit K (ramificationIndex K : Int)
  have htOrder : ordUnit K t = (ramificationIndex K : Int) := by
    exact ordUnit_uniformizerPowerUnit (K := K) _
  let w : K := (t : K) * y / x
  have hwIntegral : w ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K w
    have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    dsimp only [w]
    rw [div_eq_mul_inv, ord_mul, ord_mul, AddValuation.map_inv,
      ← coe_ordUnit K t, hxOrdTop, hyOrdTop]
    exact_mod_cast (show 0 ≤
      ordUnit K t + ordUnit K yu - ordUnit K xu by
        rw [htOrder]
        omega)
  let uK : K := 1 + (a : K) * (y / x) ^ 2
  have hqFactor : x ^ 2 + (a : K) * y ^ 2 = x ^ 2 * uK := by
    dsimp only [uK]
    field_simp [hx0]
  have hu0 : uK ≠ 0 := by
    intro hu
    apply hq0
    rw [hqFactor, hu, mul_zero]
  let u : Kˣ := Units.mk0 uK hu0
  let error : Kˣ := a * (yu / xu) ^ 2
  have herrorOrder : ordUnit K error =
      ordUnit K a + 2 * ordUnit K yu - 2 * ordUnit K xu := by
    simp [error, div_eq_mul_inv]
    ring
  have herrorPositive : (0 : WithTop Int) < ord K (error : K) := by
    have hpositive : 0 < ordUnit K error := by
      rw [herrorOrder]
      omega
    rw [← coe_ordUnit]
    exact_mod_cast hpositive
  have huValue : (u : K) = 1 + (error : K) := by
    simp only [u, uK, error, xu, yu, Units.val_mk0,
      Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val]
  have huUnit : IsValuationUnit K (u : K) := by
    rw [IsValuationUnit, huValue]
    have honeLt : ord K (1 : K) < ord K (error : K) := by
      simpa only [ord_one] using herrorPositive
    rw [(ord K).map_add_eq_of_lt_left honeLt, ord_one]
  have hparameter :=
    binaryMiddleShiftedParameter_mul_ramificationSquare (K := K) a
  have hparameterK := congrArg Units.val hparameter
  have hshiftedValue :
      1 ^ 2 +
          (binaryMiddleShiftedParameter (K := K) a : K) * w ^ 2 =
        (u : K) := by
    rw [huValue]
    simp only [error, xu, yu, w, t, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_div_eq_div_val,
      Units.val_mk0]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hparameterK
    rw [← hparameterK]
    field_simp [hx0]
  have huGroup : squareClass K u ∈
      beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) := by
    apply squareClass_mem_shiftedNormGeneratorGroup_of_representation
      a u hR huUnit
    · exact (IntegerRing K).one_mem
    · exact hwIntegral
    · exact hshiftedValue
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  have hqU : qU = u * xu ^ 2 := by
    apply Units.ext
    simpa only [qU, u, xu, Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val, mul_comm] using hqFactor
  change squareClass K qU ∈ _
  rw [hqU, squareClass_mul_square]
  exact huGroup

/-- If the second coordinate is a unit and the first coordinate has order at
least `R-e`, division by the parameter gives a shifted norm-generator value.
Consequently the original diagonal value lies in `<a> g(a♭)`. -/
theorem squareClass_diagonalValue_mem_cyclic_sup_shiftedNormGenerator_of_second_order
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hyUnit : IsValuationUnit K y)
    (hxOrder : ordUnit K a - (ramificationIndex K : Int) ≤
      ordUnit K (Units.mk0 x hx0))
    (hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0) :
    squareClass K (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) ∈
      cyclicSquareClassSubgroup K a ⊔
        beliNormGeneratorSquareClassGroup K
          (binaryMiddleShiftedParameter (K := K) a) := by
  let xu : Kˣ := Units.mk0 x hx0
  let yu : Kˣ := Units.mk0 y hy0
  have hxOrder' : ordUnit K a - (ramificationIndex K : Int) ≤
      ordUnit K xu := by simpa [xu] using hxOrder
  have hyOrder : ordUnit K yu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K yu).1
      (by simpa [yu] using hyUnit)
  let t : Kˣ := uniformizerPowerUnit K (ramificationIndex K : Int)
  have htOrder : ordUnit K t = (ramificationIndex K : Int) := by
    exact ordUnit_uniformizerPowerUnit (K := K) _
  let w : K := (t : K) * x / ((a : K) * y)
  have hwIntegral : w ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K w
    have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    have hdenOrdTop : ord K ((a : K) * y) =
        ((ordUnit K a + ordUnit K yu : Int) : WithTop Int) := by
      rw [ord_mul, ← coe_ordUnit K a, hyOrdTop]
      norm_cast
    have hnumOrdTop : ord K ((t : K) * x) =
        ((ordUnit K t + ordUnit K xu : Int) : WithTop Int) := by
      rw [ord_mul, ← coe_ordUnit K t, hxOrdTop]
      norm_cast
    dsimp only [w]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hnumOrdTop, hdenOrdTop]
    exact_mod_cast (show 0 ≤
      ordUnit K t + ordUnit K xu -
        (ordUnit K a + ordUnit K yu) by
        rw [htOrder, hyOrder]
        omega)
  let uK : K := 1 + (a : K)⁻¹ * (x / y) ^ 2
  have hqFactor : x ^ 2 + (a : K) * y ^ 2 =
      (a : K) * y ^ 2 * uK := by
    dsimp only [uK]
    field_simp [hy0, Units.ne_zero a]
    ring
  have hu0 : uK ≠ 0 := by
    intro hu
    apply hq0
    rw [hqFactor, hu, mul_zero]
  let u : Kˣ := Units.mk0 uK hu0
  let error : Kˣ := a⁻¹ * (xu / yu) ^ 2
  have herrorOrder : ordUnit K error =
      -ordUnit K a + 2 * ordUnit K xu - 2 * ordUnit K yu := by
    simp [error, div_eq_mul_inv]
    ring
  have herrorPositive : (0 : WithTop Int) < ord K (error : K) := by
    have hpositive : 0 < ordUnit K error := by
      rw [herrorOrder, hyOrder]
      omega
    rw [← coe_ordUnit]
    exact_mod_cast hpositive
  have huValue : (u : K) = 1 + (error : K) := by
    simp only [u, uK, error, xu, yu, Units.val_mk0,
      Units.val_inv_eq_inv_val, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
  have huUnit : IsValuationUnit K (u : K) := by
    rw [IsValuationUnit, huValue]
    have honeLt : ord K (1 : K) < ord K (error : K) := by
      simpa only [ord_one] using herrorPositive
    rw [(ord K).map_add_eq_of_lt_left honeLt, ord_one]
  have hparameter :=
    binaryMiddleShiftedParameter_mul_ramificationSquare (K := K) a
  have hparameterK := congrArg Units.val hparameter
  have hshiftedValue :
      1 ^ 2 +
          (binaryMiddleShiftedParameter (K := K) a : K) * w ^ 2 =
        (u : K) := by
    rw [huValue]
    simp only [error, xu, yu, w, t, Units.val_inv_eq_inv_val,
      Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val, Units.val_mk0]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hparameterK
    rw [← hparameterK]
    field_simp [hx0, hy0, Units.ne_zero a]
  have huGroup : squareClass K u ∈
      beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) := by
    apply squareClass_mem_shiftedNormGeneratorGroup_of_representation
      a u hR huUnit
    · exact (IntegerRing K).one_mem
    · exact hwIntegral
    · exact hshiftedValue
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  have hqU : qU = (a * u) * yu ^ 2 := by
    apply Units.ext
    simp only [qU, u, yu, Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val]
    rw [hqFactor]
    ring
  let T := cyclicSquareClassSubgroup K a ⊔
    beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a)
  have haT : squareClass K a ∈ T :=
    (le_sup_left : cyclicSquareClassSubgroup K a ≤ T)
      (Subgroup.mem_zpowers _)
  have huT : squareClass K u ∈ T :=
    (le_sup_right : beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a) ≤ T) huGroup
  change squareClass K qU ∈ T
  rw [hqU, squareClass_mul_square]
  exact T.mul_mem haT huT

/-- Every proper integral spinor class of `<1,a>`, for `R > 2e`, is
generated by the parameter class and the shifted norm-generator group. -/
theorem spinorNormImage_binaryDiagonal_le_cyclic_sup_shiftedNormGenerator
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) ⊆
      (cyclicSquareClassSubgroup K a ⊔
        beliNormGeneratorSquareClassGroup K
          (binaryMiddleShiftedParameter (K := K) a) :
        Subgroup (SquareClass K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  have haOrderNonneg : 0 ≤ ordUnit K a := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast haOrderNonneg
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  intro A hA
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag] at hA
  rcases hA with ⟨z, hz, hzMem, hzPrimitive,
    hfirst, hsecond, hclass⟩
  have hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz :=
    (isIntegralReflection_binaryModel_iff_of_primitive
      a 0 hz hzMem hzPrimitive).2 ⟨hfirst, hsecond⟩
  have hqFormula :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        z 0 ^ 2 + (a : K) * z 1 ^ 2 := by
    simp [QuadraticSpace.binaryModel_quadratic_apply]
  have hq0 : z 0 ^ 2 + (a : K) * z 1 ^ 2 ≠ 0 := by
    rw [← hqFormula]
    exact hz
  let T := cyclicSquareClassSubgroup K a ⊔
    beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a)
  have hcases :=
    primitive_integralReflection_binaryDiagonal_order_cases
      a hz hzMem hzPrimitive hzIntegral
  change A ∈ T
  rcases hcases with hsmall | ⟨hyUnit, hxCases⟩
  · rcases hsmall with ⟨hx0, hxOrder⟩
    have hvalueMem :=
      squareClass_diagonalValue_mem_shiftedNormGenerator_of_first_order
        a hR hx0 hxOrder
          (mem_binaryModelLattice_iff z |>.1 hzMem 1) hq0
    rw [← hclass]
    have hvalueT :
        squareClass K
            (Units.mk0 (z 0 ^ 2 + (a : K) * z 1 ^ 2) hq0) ∈ T :=
      (le_sup_right : beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) ≤ T) hvalueMem
    simpa only [hqFormula] using hvalueT
  · rcases hxCases with hxZero | ⟨hx0, hxSmall | hxHigh⟩
    · have hy0 : z 1 ≠ 0 := by
        intro hy
        rw [hy, IsValuationUnit, ord_zero] at hyUnit
        exact WithTop.top_ne_zero hyUnit
      let yu : Kˣ := Units.mk0 (z 1) hy0
      have hqUnit : Units.mk0
            ((QuadraticSpace.binaryModel a 0).quadratic z) hz =
          a * yu ^ 2 := by
        apply Units.ext
        change (QuadraticSpace.binaryModel a 0).quadratic z =
          (a : K) * (yu : K) ^ 2
        rw [hqFormula, hxZero]
        simp [yu]
      rw [← hclass, hqUnit, squareClass_mul_square]
      exact (le_sup_left : cyclicSquareClassSubgroup K a ≤ T)
        (Subgroup.mem_zpowers _)
    · have hvalueMem :=
        squareClass_diagonalValue_mem_shiftedNormGenerator_of_first_order
          a hR hx0 hxSmall
            (mem_binaryModelLattice_iff z |>.1 hzMem 1) hq0
      rw [← hclass]
      have hvalueT :
          squareClass K
              (Units.mk0 (z 0 ^ 2 + (a : K) * z 1 ^ 2) hq0) ∈ T :=
        (le_sup_right : beliNormGeneratorSquareClassGroup K
          (binaryMiddleShiftedParameter (K := K) a) ≤ T) hvalueMem
      simpa only [hqFormula] using hvalueT
    · have hy0 : z 1 ≠ 0 := by
        intro hy
        rw [hy, IsValuationUnit, ord_zero] at hyUnit
        exact WithTop.top_ne_zero hyUnit
      have hvalueT :=
        squareClass_diagonalValue_mem_cyclic_sup_shiftedNormGenerator_of_second_order
          a hR hx0 hy0 hyUnit hxHigh hq0
      rw [← hclass]
      simpa only [T, hqFormula] using hvalueT

/-- A unit represented integrally by `<1,a♭>` has unit first coordinate,
because `ord(a♭)>0`. -/
theorem first_coordinate_unit_of_shifted_unit_representation
    (a u : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (huUnit : IsValuationUnit K (u : K))
    {x y : K} (hxIntegral : x ∈ IntegerRing K)
    (hyIntegral : y ∈ IntegerRing K)
    (hvalue : x ^ 2 +
        (binaryMiddleShiftedParameter (K := K) a : K) * y ^ 2 =
      (u : K)) :
    IsValuationUnit K x := by
  let shifted := binaryMiddleShiftedParameter (K := K) a
  have hshiftedPos : 0 < ordUnit K shifted := by
    simpa [shifted] using
      binaryMiddleShiftedParameter_order_pos (K := K) a hR
  by_cases hy0 : y = 0
  · have hxSq : x ^ 2 = (u : K) := by simpa [hy0] using hvalue
    have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, zero_pow (by norm_num)] at hxSq
      exact Units.ne_zero u hxSq.symm
    let xu : Kˣ := Units.mk0 x hx0
    have horder := congrArg (ord K) hxSq
    have hxOrder : ordUnit K xu = 0 := by
      rw [ord_pow, huUnit] at horder
      have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
        simpa [xu] using (coe_ordUnit K xu).symm
      rw [hxOrdTop] at horder
      have htwice : 2 * ordUnit K xu = 0 := by
        exact_mod_cast horder
      omega
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxOrder
  · let yu : Kˣ := Units.mk0 y hy0
    have hyOrder : 0 ≤ ordUnit K yu :=
      Lattice.ordUnit_nonneg_of_mem_integerRing yu
        (by simpa [yu] using hyIntegral)
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    have htermOrder :
        ord K ((shifted : K) * y ^ 2) =
          ((ordUnit K shifted + 2 * ordUnit K yu : Int) : WithTop Int) := by
      rw [ord_mul, ord_pow, ← coe_ordUnit K shifted, hyOrdTop]
      norm_cast
    have htermPositive :
        (0 : WithTop Int) < ord K ((shifted : K) * y ^ 2) := by
      rw [htermOrder]
      have hpositive : 0 <
          ordUnit K shifted + 2 * ordUnit K yu :=
        add_pos_of_pos_of_nonneg hshiftedPos
          (mul_nonneg (by norm_num) hyOrder)
      exact_mod_cast hpositive
    have hx0 : x ≠ 0 := by
      intro hx
      have htermEq : (shifted : K) * y ^ 2 = (u : K) := by
        simpa [shifted, hx] using hvalue
      rw [htermEq, huUnit] at htermPositive
      exact (lt_irrefl (0 : WithTop Int)) htermPositive
    let xu : Kˣ := Units.mk0 x hx0
    have hxOrderNonneg : 0 ≤ ordUnit K xu :=
      Lattice.ordUnit_nonneg_of_mem_integerRing xu
        (by simpa [xu] using hxIntegral)
    have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hxOrderZero : ordUnit K xu = 0 := by
      by_contra hne
      have hxPositive : 0 < ordUnit K xu := by omega
      have hxSqPositive : (0 : WithTop Int) < ord K (x ^ 2) := by
        rw [ord_pow, hxOrdTop]
        exact_mod_cast (show 0 < 2 * ordUnit K xu by omega)
      have hminPositive : (0 : WithTop Int) <
          min (ord K (x ^ 2)) (ord K ((shifted : K) * y ^ 2)) :=
        lt_min hxSqPositive htermPositive
      have hminLe := min_ord_le_ord_add K (x ^ 2)
        ((shifted : K) * y ^ 2)
      have hsumOrder :
          ord K (x ^ 2 + (shifted : K) * y ^ 2) = 0 := by
        rw [hvalue]
        exact huUnit
      rw [hsumOrder] at hminLe
      exact (not_lt_of_ge hminLe) hminPositive
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxOrderZero

/-- An integral unit represented by the shifted model is the spinor class of
a primitive integral reflection of `<1,a>`.  The normalization divides the
two transported coordinates by `π^min(e,ord(y))`. -/
theorem squareClass_mem_spinorNormImage_of_shifted_unit_representation
    (a u : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (huUnit : IsValuationUnit K (u : K))
    {x y : K} (hxIntegral : x ∈ IntegerRing K)
    (hyIntegral : y ∈ IntegerRing K)
    (hvalue : x ^ 2 +
        (binaryMiddleShiftedParameter (K := K) a : K) * y ^ 2 =
      (u : K)) :
    squareClass K u ∈ Lattice.spinorNormImageSubgroup
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) := by
  have hxUnit := first_coordinate_unit_of_shifted_unit_representation
    a u hR huUnit hxIntegral hyIntegral hvalue
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, IsValuationUnit, ord_zero] at hxUnit
    exact WithTop.top_ne_zero hxUnit
  let xu : Kˣ := Units.mk0 x hx0
  have hxOrder : ordUnit K xu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K xu).1
      (by simpa [xu] using hxUnit)
  by_cases hy0 : y = 0
  · have huSquare : IsSquare u := by
      refine ⟨xu, ?_⟩
      apply Units.ext
      simpa [xu, hy0, pow_two] using hvalue.symm
    have hclass : squareClass K u = 1 :=
      squareClass_eq_one_of_isSquare u huSquare
    rw [hclass]
    exact (Lattice.spinorNormImageSubgroup
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K))).one_mem
  let yu : Kˣ := Units.mk0 y hy0
  have hyOrder : 0 ≤ ordUnit K yu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing yu
      (by simpa [yu] using hyIntegral)
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  let m : Int := min (ramificationIndex K : Int) (ordUnit K yu)
  have hmNonneg : 0 ≤ m := by
    dsimp only [m]
    exact le_min heNonneg hyOrder
  have hmLeE : m ≤ (ramificationIndex K : Int) := by
    exact min_le_left _ _
  have hmLeY : m ≤ ordUnit K yu := by
    exact min_le_right _ _
  have hmCases : m = (ramificationIndex K : Int) ∨
      m = ordUnit K yu := by
    rcases le_total (ramificationIndex K : Int) (ordUnit K yu) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  let t : Kˣ := uniformizerPowerUnit K (ramificationIndex K : Int)
  have htOrder : ordUnit K t = (ramificationIndex K : Int) := by
    exact ordUnit_uniformizerPowerUnit (K := K) _
  let s : Kˣ := uniformizerPowerUnit K (-m)
  have hsOrder : ordUnit K s = -m := by
    exact ordUnit_uniformizerPowerUnit (K := K) _
  let z : Fin 2 → K :=
    ![((s * t * xu : Kˣ) : K), ((s * yu : Kˣ) : K)]
  have hz0 : z 0 = ((s * t * xu : Kˣ) : K) := by simp [z]
  have hz1 : z 1 = ((s * yu : Kˣ) : K) := by simp [z]
  let qU : Kˣ := (s * t) ^ 2 * u
  have hqOrder : ordUnit K qU =
      2 * ((ramificationIndex K : Int) - m) := by
    simp only [qU, ordUnit_mul, ordUnit_pow, hsOrder, htOrder,
      (isValuationUnit_iff_ordUnit_eq_zero K u).1 huUnit]
    omega
  have hparameter :=
    binaryMiddleShiftedParameter_mul_ramificationSquare (K := K) a
  have hparameterK := congrArg Units.val hparameter
  have hvalueOriginal :
      (QuadraticSpace.binaryModel a 0).quadratic z = (qU : K) := by
    simp only [QuadraticSpace.binaryModel_quadratic_apply, z,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add,
      qU, xu, yu, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hparameterK
    rw [← hvalue, ← hparameterK]
    ring
  have hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z := by
    rw [QuadraticSpace.IsAnisotropic, hvalueOriginal]
    exact Units.ne_zero qU
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((s * t * xu : Kˣ) : K)
      rw [← coe_ordUnit]
      exact_mod_cast (show 0 ≤ ordUnit K (s * t * xu) by
        simp only [ordUnit_mul, hsOrder, htOrder, hxOrder]
        omega)
    · apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((s * yu : Kˣ) : K)
      rw [← coe_ordUnit]
      exact_mod_cast (show 0 ≤ ordUnit K (s * yu) by
        simp only [ordUnit_mul, hsOrder]
        omega)
  have hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)) := by
    apply (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).2
    rcases hmCases with hmE | hmY
    · left
      have horder : ordUnit K (s * t * xu) = 0 := by
        simp only [ordUnit_mul, hsOrder, htOrder, hxOrder]
        omega
      simpa [z] using
        (isValuationUnit_iff_ordUnit_eq_zero K (s * t * xu)).2 horder
    · right
      have horder : ordUnit K (s * yu) = 0 := by
        simp only [ordUnit_mul, hsOrder]
        omega
      simpa [z] using
        (isValuationUnit_iff_ordUnit_eq_zero K (s * yu)).2 horder
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  let firstCoefficient : Kˣ :=
    twoU * (s * t * xu) * qU⁻¹
  have hfirstOrder : ordUnit K firstCoefficient = m := by
    simp only [firstCoefficient, ordUnit_mul, ordUnit_inv, htwoOrder,
      hsOrder, htOrder, hxOrder, hqOrder]
    omega
  have hfirstMem : (firstCoefficient : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (firstCoefficient : K)
    rw [← coe_ordUnit, hfirstOrder]
    exact_mod_cast hmNonneg
  let secondCoefficient : Kˣ :=
    twoU * a * (s * yu) * qU⁻¹
  have hsecondOrder : ordUnit K secondCoefficient =
      ordUnit K a + ordUnit K yu + m -
        (ramificationIndex K : Int) := by
    simp only [secondCoefficient, ordUnit_mul, ordUnit_inv, htwoOrder,
      hsOrder, hqOrder]
    omega
  have hsecondMem : (secondCoefficient : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (secondCoefficient : K)
    rw [← coe_ordUnit, hsecondOrder]
    exact_mod_cast (show 0 ≤
      ordUnit K a + ordUnit K yu + m -
        (ramificationIndex K : Int) by omega)
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast (show 0 ≤ ordUnit K a by omega)
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  change squareClass K u ∈ Lattice.spinorNormImage
    (q := QuadraticSpace.binaryModel a 0)
    (L := binaryModelLattice (K := K))
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag]
  refine ⟨z, hz, hzMem, hzPrimitive, ?_, ?_, ?_⟩
  · have hcoefficient :
        2 * z 0 /
            (QuadraticSpace.binaryModel a 0).quadratic z =
          (firstCoefficient : K) := by
      rw [hz0, hvalueOriginal]
      simp only [firstCoefficient, twoU, qU, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      field_simp [Units.ne_zero s, Units.ne_zero t, Units.ne_zero xu,
        Units.ne_zero u]
    rw [zero_mul, add_zero, hcoefficient]
    exact hfirstMem
  · have hcoefficient :
        2 * ((a : K) * z 1) /
            (QuadraticSpace.binaryModel a 0).quadratic z =
          (secondCoefficient : K) := by
      rw [hz1, hvalueOriginal]
      simp only [secondCoefficient, twoU, qU, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      field_simp [Units.ne_zero s, Units.ne_zero t, Units.ne_zero u]
    norm_num only [zero_mul, zero_pow, zero_add, add_zero]
    rw [hcoefficient]
    exact hsecondMem
  · have hqUnit : Units.mk0
          ((QuadraticSpace.binaryModel a 0).quadratic z) hz = qU := by
      apply Units.ext
      simpa only [Units.val_mk0] using hvalueOriginal
    rw [hqUnit]
    calc
      squareClass K qU = squareClass K (u * (s * t) ^ 2) := by
        apply congrArg (squareClass K)
        simp [qU, mul_comm]
      _ = squareClass K u := squareClass_mul_square K u (s * t)

/-- The shifted norm-generator group is contained in the proper integral
spinor image of `<1,a>`. -/
theorem shiftedNormGeneratorGroup_le_spinorNormImage_binaryDiagonal
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : BinaryNormGeneratorLocalLaws.{u, u} K :=
    binaryNormGeneratorLocalLawsProved
  let shifted := binaryMiddleShiftedParameter (K := K) a
  have hshiftedIntegral : (shifted : K) ∈ IntegerRing K := by
    simpa [shifted] using
      binaryMiddleShiftedParameter_mem_integerRing (K := K) a hR
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (shifted : K) ∈ IntegerRing K := by
    simpa using hshiftedIntegral
  let b := binaryExactModelBONG shifted 0 htwo hdiag
  intro A hA
  rcases hA with ⟨c, hc, rfl⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  change valuationUnitClassHom K u ∈
    beliNormGeneratorGroup K
      (binaryMiddleShiftedParameter (K := K) a) at hc
  have hc' : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.binaryParameter := by
    rw [binaryExactModelBONG_binaryParameter]
    simpa [shifted] using hc
  rcases b.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
      u hc' with ⟨y, hy, hratio⟩
  have hyMem := hy.mem
  have hxIntegral : y 0 ∈ IntegerRing K :=
    (mem_binaryModelLattice_iff y).1 hyMem 0
  have hyIntegral : y 1 ∈ IntegerRing K :=
    (mem_binaryModelLattice_iff y).1 hyMem 1
  have hvalue : y 0 ^ 2 + (shifted : K) * y 1 ^ 2 =
      (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
    have hratioK := congrArg Units.val hratio
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit] at hratioK
    rw [binaryExactModelBONG_value_zero, div_one] at hratioK
    rw [QuadraticSpace.binaryModel_quadratic_apply] at hratioK
    simpa [b, shifted] using hratioK
  change squareClass K (u : Kˣ) ∈
    Lattice.spinorNormImageSubgroup
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K))
  apply squareClass_mem_spinorNormImage_of_shifted_unit_representation
    a (u : Kˣ) hR u.property hxIntegral hyIntegral
  simpa [shifted] using hvalue

/-- Xu's complete formula for every diagonal parameter with `R > 2e`,
expressed through the shifted norm-generator group. -/
theorem spinorNormImage_binaryDiagonal_eq_cyclic_sup_shiftedNormGenerator
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      ↑(cyclicSquareClassSubgroup K a ⊔
        beliNormGeneratorSquareClassGroup K
          (binaryMiddleShiftedParameter (K := K) a)) := by
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have haOrderNonneg : 0 ≤ ordUnit K a := by omega
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast haOrderNonneg
  let S := Lattice.spinorNormImageSubgroup
    (q := QuadraticSpace.binaryModel a 0)
    (L := binaryModelLattice (K := K))
  have haMem : squareClass K a ∈ S :=
    squareClass_parameter_mem_spinorNormImage_binaryDiagonal a haIntegral
  have hcyclic : cyclicSquareClassSubgroup K a ≤ S := by
    rw [cyclicSquareClassSubgroup, Subgroup.zpowers_le]
    exact haMem
  have hshifted : beliNormGeneratorSquareClassGroup K
      (binaryMiddleShiftedParameter (K := K) a) ≤ S :=
    shiftedNormGeneratorGroup_le_spinorNormImage_binaryDiagonal a hR
  have hreverse : cyclicSquareClassSubgroup K a ⊔
      beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) ≤ S :=
    sup_le hcyclic hshifted
  ext A
  constructor
  · intro hA
    exact spinorNormImage_binaryDiagonal_le_cyclic_sup_shiftedNormGenerator
      a hR hA
  · intro hA
    change A ∈ S
    exact hreverse hA

/-- Beli (2003), Lemma 3.13(i), specialized to the canonical normalized
factorization of an arbitrary parameter. -/
theorem beliAuxiliarySpinorGroup_eq_binaryMiddleShiftedNormGenerator
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliAuxiliarySpinorGroup K a hR =
      beliNormGeneratorSquareClassGroup K
        (binaryMiddleShiftedParameter (K := K) a) := by
  let R : Int := ordUnit K a
  let ε : Kˣ := normalizedUnitPart K a
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * ε = a := by
    simpa [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
  have h := beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
    (K := K) R ε hε (by simpa [R] using hR)
  simpa [R, ε, binaryMiddleShiftedParameter, hfactor] using h

/-- Beli (2003), Lemma 3.7 on every representative of order `R > 2e`.
This includes Xu (1993), Propositions 2.1, 2.2(i), and 2.2(ii). -/
theorem spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_two_e_lt
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have haNonneg : 0 ≤ ordUnit K a := by omega
  have haAdmissible : IsBinaryParameterAdmissible a :=
    isBinaryParameterAdmissible_of_ordUnit_nonneg haNonneg
  have hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
    rw [ordUnit_negativeQuarterUnit] at horder
    omega
  rw [spinorNormImage_binaryDiagonal_eq_cyclic_sup_shiftedNormGenerator
    a hR]
  symm
  rw [beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
    K a haAdmissible hquarter hR,
    beliAuxiliarySpinorGroup_eq_binaryMiddleShiftedNormGenerator a hR]

/-- The `R > 2e` formula transported from the diagonal model to an arbitrary
binary BONG. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_two_e_lt
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hR : 2 * (ramificationIndex K : Int) < b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  have hnonneg : 0 ≤ b.binaryOrderGap := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  rw [b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hnonneg]
  apply
    spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_two_e_lt
  change 2 * (ramificationIndex K : Int) < b.binaryParameterOrder
  rwa [b.binaryParameterOrder_eq_orderGap]

end BONG

end Bong
