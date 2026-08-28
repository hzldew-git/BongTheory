/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryPrimitiveCoordinates
import Bong.Bong.BinaryDiagonalMiddleSpinorOdd

/-!
# Odd low-range binary spinor norms

This is the odd-order branch of Xu (1993), Proposition 2.3(i).  When
`0 < R < 2e` is odd, the two diagonal summands of a primitive vector can
never have the same order.  The elementary coefficient criterion therefore
shows that every primitive anisotropic vector defines an integral
reflection.  Scaling a vector on each represented line to a primitive
lattice vector then identifies the spinor image with the full quadratic
norm square-class subgroup.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- In the low range, a primitive vector whose two diagonal summands have
different orders defines an integral reflection. -/
theorem primitive_isIntegralReflection_binaryDiagonal_of_low_of_unequal_terms
    (a : Kˣ)
    (hRnonneg : 0 ≤ ordUnit K a)
    (_hRhigh : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)))
    (hUnequal : ∀ (hx0 : z 0 ≠ 0) (hy0 : z 1 ≠ 0),
      2 * ordUnit K (Units.mk0 (z 0) hx0) ≠
        ordUnit K a + 2 * ordUnit K (Units.mk0 (z 1) hy0)) :
    Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz := by
  let x : K := z 0
  let y : K := z 1
  have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
  have hxMem : x ∈ IntegerRing K := by simpa [x] using hzCoords 0
  have hyMem : y ∈ IntegerRing K := by simpa [y] using hzCoords 1
  have hprimitive :=
    (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1 hzPrimitive
  have hqFormula :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        x ^ 2 + (a : K) * y ^ 2 := by
    simp [QuadraticSpace.binaryModel_quadratic_apply, x, y]
  have hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0 := by
    rw [← hqFormula]
    exact hz
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  have hqOrdTop :
      ord K (x ^ 2 + (a : K) * y ^ 2) =
        (ordUnit K qU : WithTop Int) := by
    simpa [qU] using (coe_ordUnit K qU).symm
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have hcoefficient_mem
      {w : K} (hw0 : w ≠ 0) (wu : Kˣ)
      (hwu : (wu : K) = w)
      (hbound : ordUnit K qU ≤
        (ramificationIndex K : Int) + ordUnit K wu) :
      2 * w / (x ^ 2 + (a : K) * y ^ 2) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤
      ord K (2 * w / (x ^ 2 + (a : K) * y ^ 2))
    rw [div_eq_mul_inv, ord_mul, ord_mul, AddValuation.map_inv,
      ← ramificationIndex_spec, hqOrdTop]
    have hwOrd : ord K w = (ordUnit K wu : WithTop Int) := by
      rw [← hwu, ← coe_ordUnit]
    rw [hwOrd]
    exact_mod_cast (show 0 ≤
      (ramificationIndex K : Int) + ordUnit K wu - ordUnit K qU by
        omega)
  apply (isIntegralReflection_binaryDiagonal_iff_of_primitive
    a hz hzMem hzPrimitive).2
  by_cases hxUnit : IsValuationUnit K x
  · have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, IsValuationUnit, ord_zero] at hxUnit
      exact WithTop.top_ne_zero hxUnit
    let xu : Kˣ := Units.mk0 x hx0
    have hxOrder : ordUnit K xu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K xu).1
        (by simpa [xu] using hxUnit)
    have hqOrder : ordUnit K qU = 0 := by
      by_cases hy0 : y = 0
      · have hq : qU = xu ^ 2 := by
          apply Units.ext
          simp [qU, xu, hy0]
        rw [hq, ordUnit_pow, hxOrder]
        simp
      · let yu : Kˣ := Units.mk0 y hy0
        have hyOrder : 0 ≤ ordUnit K yu :=
          Lattice.ordUnit_nonneg_of_mem_integerRing yu
            (by simpa [yu] using hyMem)
        have hxTermOrder : ord K (x ^ 2) = 0 := by
          rw [ord_pow]
          have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
            simpa [xu] using (coe_ordUnit K xu).symm
          rw [hxOrdTop, hxOrder]
          simp
        have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
          simpa [yu] using (coe_ordUnit K yu).symm
        have hyTermOrder :
            ord K ((a : K) * y ^ 2) =
              ((ordUnit K a + 2 * ordUnit K yu : Int) : WithTop Int) := by
          rw [ord_mul, ord_pow, ← coe_ordUnit K a, hyOrdTop]
          norm_cast
        have hterms : ord K (x ^ 2) < ord K ((a : K) * y ^ 2) := by
          rw [hxTermOrder, hyTermOrder]
          have hsumNe : ordUnit K a + 2 * ordUnit K yu ≠ 0 := by
            have h := hUnequal (by simpa [x] using hx0)
              (by simpa [y] using hy0)
            have h' : 0 ≠ ordUnit K a + 2 * ordUnit K yu := by
              simpa [x, y, xu, yu, hxOrder] using h
            exact fun hzero => h' hzero.symm
          exact_mod_cast (show 0 < ordUnit K a + 2 * ordUnit K yu by
            omega)
        have hsum := (ord K).map_add_eq_of_lt_left hterms
        apply WithTop.coe_injective
        rw [← hqOrdTop, hsum, hxTermOrder]
        norm_num
    constructor
    · rw [hqFormula]
      apply hcoefficient_mem hx0 xu
      · rfl
      · rw [hqOrder, hxOrder]
        exact heNonneg
    · by_cases hy0 : y = 0
      · simp [hqFormula, y, hy0]
      · let yu : Kˣ := Units.mk0 y hy0
        have hyOrder : 0 ≤ ordUnit K yu :=
          Lattice.ordUnit_nonneg_of_mem_integerRing yu
            (by simpa [yu] using hyMem)
        let aw : Kˣ := a * yu
        have haw : (aw : K) = (a : K) * y := by rfl
        rw [hqFormula]
        have hmem := hcoefficient_mem
          (mul_ne_zero (Units.ne_zero a) hy0) aw haw (by
            simp only [hqOrder, aw, ordUnit_mul]
            omega)
        simpa only [y, mul_assoc] using hmem
  · have hyUnit : IsValuationUnit K y := hprimitive.resolve_left hxUnit
    have hy0 : y ≠ 0 := by
      intro hy
      rw [hy, IsValuationUnit, ord_zero] at hyUnit
      exact WithTop.top_ne_zero hyUnit
    let yu : Kˣ := Units.mk0 y hy0
    have hyOrder : ordUnit K yu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K yu).1
        (by simpa [yu] using hyUnit)
    by_cases hx0 : x = 0
    · have hq : qU = a * yu ^ 2 := by
        apply Units.ext
        simp [qU, yu, hx0]

      have hqOrder : ordUnit K qU = ordUnit K a := by
        rw [hq, ordUnit_mul, ordUnit_pow, hyOrder]
        simp
      constructor
      · simp [hqFormula, x, hx0]
      · let aw : Kˣ := a * yu
        have haw : (aw : K) = (a : K) * y := by rfl
        rw [hqFormula]
        have hmem := hcoefficient_mem
          (mul_ne_zero (Units.ne_zero a) hy0) aw haw (by
            simp only [hqOrder, aw, ordUnit_mul, hyOrder, add_zero]
            omega)
        simpa only [y, mul_assoc] using hmem
    · let xu : Kˣ := Units.mk0 x hx0
      have hxOrderNonneg : 0 ≤ ordUnit K xu :=
        Lattice.ordUnit_nonneg_of_mem_integerRing xu
          (by simpa [xu] using hxMem)
      have hxOrderNe : ordUnit K xu ≠ 0 := by
        intro hzero
        apply hxUnit
        simpa [xu] using
          (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hzero
      have hxOrderPos : 0 < ordUnit K xu := by omega
      have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
        simpa [xu] using (coe_ordUnit K xu).symm
      have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
        simpa [yu] using (coe_ordUnit K yu).symm
      have hxTermOrder :
          ord K (x ^ 2) = ((2 * ordUnit K xu : Int) : WithTop Int) := by
        rw [ord_pow, hxOrdTop]
        norm_cast
      have hyTermOrder :
          ord K ((a : K) * y ^ 2) = (ordUnit K a : WithTop Int) := by
        rw [ord_mul, ord_pow, ← coe_ordUnit K a, hyOrdTop, hyOrder]
        simp
      have hordersNe : 2 * ordUnit K xu ≠ ordUnit K a := by
        have h := hUnequal (by simpa [x] using hx0)
          (by simpa [y] using hy0)
        simpa [x, y, xu, yu, hyOrder] using h
      rcases lt_or_gt_of_ne hordersNe with hlt | hgt
      · have hterms : ord K (x ^ 2) < ord K ((a : K) * y ^ 2) := by
          rw [hxTermOrder, hyTermOrder]
          exact_mod_cast hlt
        have hsum := (ord K).map_add_eq_of_lt_left hterms
        have hqOrder : ordUnit K qU = 2 * ordUnit K xu := by
          apply WithTop.coe_injective
          rw [← hqOrdTop, hsum, hxTermOrder]
        constructor
        · rw [hqFormula]
          apply hcoefficient_mem hx0 xu
          · rfl
          · rw [hqOrder]
            omega
        · let aw : Kˣ := a * yu
          have haw : (aw : K) = (a : K) * y := by rfl
          rw [hqFormula]
          have hmem := hcoefficient_mem
            (mul_ne_zero (Units.ne_zero a) hy0) aw haw (by
              simp only [hqOrder, aw, ordUnit_mul, hyOrder, add_zero]
              omega)
          simpa only [y, mul_assoc] using hmem

      · have hterms : ord K ((a : K) * y ^ 2) < ord K (x ^ 2) := by
          rw [hxTermOrder, hyTermOrder]
          exact_mod_cast hgt
        have hsum := (ord K).map_add_eq_of_lt_right hterms
        have hqOrder : ordUnit K qU = ordUnit K a := by
          apply WithTop.coe_injective
          rw [← hqOrdTop, hsum, hyTermOrder]
        constructor
        · rw [hqFormula]
          apply hcoefficient_mem hx0 xu
          · rfl
          · rw [hqOrder]
            omega
        · let aw : Kˣ := a * yu
          have haw : (aw : K) = (a : K) * y := by rfl
          rw [hqFormula]
          have hmem := hcoefficient_mem
            (mul_ne_zero (Units.ne_zero a) hy0) aw haw (by
              simp only [hqOrder, aw, ordUnit_mul, hyOrder, add_zero]
              omega)
          simpa [y, mul_assoc] using hmem

/-- In the odd low range, every primitive anisotropic vector of the
diagonal lattice defines an integral reflection. -/
theorem primitive_isIntegralReflection_binaryDiagonal_of_low_odd
    (a : Kˣ)
    (hRpos : 0 < ordUnit K a)
    (hRhigh : ordUnit K a < 2 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a))
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz := by
  apply primitive_isIntegralReflection_binaryDiagonal_of_low_of_unequal_terms
    a hRpos.le hRhigh.le hz hzMem hzPrimitive
  intro hx0 hy0 heq
  rcases hROdd with ⟨k, hk⟩
  omega

/-- If every primitive anisotropic vector of an integral diagonal binary
lattice defines an integral reflection, then its proper spinor image is the
complete quadratic norm square-class subgroup. -/
theorem spinorNormImage_binaryDiagonal_eq_norm_of_all_primitive_reflections
    (a : Kˣ) (haIntegral : (a : K) ∈ IntegerRing K)
    (hreflection : ∀ {z : Fin 2 → K},
      (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z) →
      (hzMem : z ∈ binaryModelLattice (K := K)) →
      (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
        (binaryModelLattice (K := K))) →
      Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) hz) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag]
  ext A
  constructor
  · rintro ⟨z, hz, _hzMem, _hzPrimitive, _hfirst, _hsecond, hclass⟩
    let qU : Kˣ := Units.mk0
      ((QuadraticSpace.binaryModel a 0).quadratic z) hz
    have hnorm : IsQuadraticNorm K (-a) qU := by
      refine ⟨z 0, z 1, ?_⟩
      change z 0 ^ 2 - ((-a : Kˣ) : K) * z 1 ^ 2 =
        (QuadraticSpace.binaryModel a 0).quadratic z
      simp [QuadraticSpace.binaryModel_quadratic_apply]
    have hmem : squareClass K qU ∈
        quadraticNormSquareClassSubgroup K (-a) :=
      ⟨qU, hnorm, rfl⟩
    rw [hclass] at hmem
    exact hmem
  · intro hA
    rcases hA with ⟨u, huNorm, huClass⟩
    rcases huNorm with ⟨x, y, hxy⟩
    let z : Fin 2 → K := ![x, y]
    have hvalue :
        (QuadraticSpace.binaryModel a 0).quadratic z = (u : K) := by
      rw [QuadraticSpace.binaryModel_quadratic_apply]
      simpa [z] using hxy
    have hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z := by
      rw [QuadraticSpace.IsAnisotropic, hvalue]
      exact Units.ne_zero u
    have hz0 : z ≠ 0 := by
      intro hzero
      apply hz
      rw [hzero]
      simp [QuadraticSpace.quadratic]
    rcases Lattice.exists_unit_smul_mem_not_mem_uniformizer_rescale
        (binaryModelLattice (K := K)) hz0 with
      ⟨t, htzMem, htzPrimitive⟩
    let w : Fin 2 → K := (t : K) • z
    let hw : (QuadraticSpace.binaryModel a 0).IsAnisotropic w :=
      hz.unit_smul t
    have hwIntegral : Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) hw :=
      hreflection hw
        (by simpa [w] using htzMem)
        (by simpa [w] using htzPrimitive)
    have hcoefficients :=
      (isIntegralReflection_binaryDiagonal_iff_of_primitive
        a hw (by simpa [w] using htzMem)
          (by simpa [w] using htzPrimitive)).1 hwIntegral
    refine ⟨w, hw, by simpa [w] using htzMem,
      by simpa [w] using htzPrimitive, ?_, ?_, ?_⟩
    · simpa only [zero_mul, add_zero] using hcoefficients.1
    · simpa [mul_assoc] using hcoefficients.2
    · let valueUnit : Kˣ := Units.mk0
          ((QuadraticSpace.binaryModel a 0).quadratic w) hw
      have hvalueScaled : valueUnit = t ^ 2 * u := by
        apply Units.ext
        simp only [valueUnit, Units.val_mul, Units.val_pow_eq_pow_val,
          Units.val_mk0]
        rw [(QuadraticSpace.binaryModel a 0).quadratic_smul, hvalue]
      change squareClass K valueUnit = A
      rw [hvalueScaled]
      calc
        squareClass K (t ^ 2 * u) = squareClass K (u * t ^ 2) := by
          congr 1
          ac_rfl
        _ = squareClass K u := squareClass_mul_square K u t
        _ = A := huClass

/-- Xu (1993), Proposition 2.3(i), odd branch: the proper spinor image is
the complete quadratic norm square-class subgroup. -/
theorem spinorNormImage_binaryDiagonal_eq_norm_of_low_odd
    (a : Kˣ)
    (hRpos : 0 < ordUnit K a)
    (hRhigh : ordUnit K a < 2 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      quadraticNormSquareClassSubgroup K (-a) := by
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast hRpos.le
  apply spinorNormImage_binaryDiagonal_eq_norm_of_all_primitive_reflections
    a haIntegral
  intro z hz hzMem hzPrimitive
  exact primitive_isIntegralReflection_binaryDiagonal_of_low_odd
    a hRpos hRhigh hROdd hz hzMem hzPrimitive

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The odd positive part of Beli (2003), Lemma 3.7, without a
`BinarySpinorLocalLaws` hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_low_odd
    (b : BONG V q L 2)
    (hRpos : 0 < b.binaryOrderGap)
    (hRhigh : b.binaryOrderGap <
      2 * (ramificationIndex K : Int))
    (hROdd : Odd b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      beliSpinorGroupRepresentative K b.binaryParameter := by
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap :=
    b.binaryParameterOrder_eq_orderGap
  have hRpos' : 0 < ordUnit K b.binaryParameter := by omega
  have hRhigh' : ordUnit K b.binaryParameter <
      2 * (ramificationIndex K : Int) := by omega
  have hROdd' : Odd (ordUnit K b.binaryParameter) := by
    rwa [hparameterOrder]
  have hquarter : unitSquareClass K b.binaryParameter ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
    rw [ordUnit_negativeQuarterUnit] at horder
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hdefect : beliParameterDefect K b.binaryParameter = 0 := by
    apply quadraticDefect_eq_zero_of_odd_ordUnit
    have hnegOdd : Odd (ordUnit K (-b.binaryParameter)) := by
      simpa only [ordUnit_neg] using hROdd'
    exact hnegOdd
  have hd : 2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞) := by
    rw [hdefect]
    simp
  have hformula := beliSpinorGroupRepresentative_caseIII_low
    K b.binaryParameter b.binaryParameter_isBinaryParameterAdmissible
      hquarter (by omega) hd
  calc
    Lattice.spinorNormImage (q := q) (L := L) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel b.binaryParameter 0)
          (L := binaryModelLattice (K := K)) :=
      b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hRpos.le
    _ = quadraticNormSquareClassSubgroup K (-b.binaryParameter) :=
      spinorNormImage_binaryDiagonal_eq_norm_of_low_odd
        b.binaryParameter hRpos' hRhigh' hROdd'
    _ = beliSpinorGroupRepresentative K b.binaryParameter := by
      exact congrArg
        (fun H : Subgroup (SquareClass K) => (H : Set (SquareClass K)))
        hformula.symm

end BONG

end Bong
