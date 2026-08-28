/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySquareDifferenceDefect
import Bong.Bong.BinaryDiagonalEvenShiftSpinor
import Bong.Bong.BinaryDiagonalReflectionOrders

/-!
# Upper containments for even low-range binary spinor norms

This file proves the forward containment in the even part of Xu (1993),
Proposition 2.3.  The common coordinate calculation is separated from the
middle- and high-defect arithmetic.  Thus the latter two branches differ
only in the depth supplied to the principal-unit filtration.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The class `-1` is a square to dyadic depth `e`, using the approximation
`1²` and the identity `1 - 1²/(-1)=2`. -/
theorem ramificationIndex_le_quadraticDefect_neg_one :
    ((ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K (-1 : Kˣ) := by
  apply natCast_le_quadraticDefect K
  refine ⟨1, ?_⟩
  have herror : 1 - (1 : K) ^ 2 / ((-1 : Kˣ) : K) = 2 := by
    norm_num
  rw [herror]
  exact (ramificationIndex_spec (K := K)).le

/-- An even-order normalized parameter belongs to every principal-unit
square-class group whose depth is bounded by both `e` and the defect of its
negative unit part. -/
theorem squareClass_evenParameter_mem_principalUnitSquareClassSubgroup
    [QuadraticDefectLaws K]
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (hEven : Even R) (k : Nat)
    (hkE : k ≤ ramificationIndex K)
    (hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon)) :
    squareClass K (uniformizerPowerUnit K R * epsilon) ∈
      principalUnitSquareClassSubgroup K k := by
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have haEven : Even (ordUnit K a) := by simpa [haOrder] using hEven
  have hnegA : quadraticDefect K (-a) = quadraticDefect K (-epsilon) := by
    dsimp only [a]
    exact beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R epsilon hUnit hEven
  have hkCast : (k : ℕ∞) ≤ (ramificationIndex K : Nat) := by
    exact_mod_cast hkE
  have hminusOne : (k : ℕ∞) ≤ quadraticDefect K (-1 : Kˣ) :=
    hkCast.trans (ramificationIndex_le_quadraticDefect_neg_one (K := K))
  have hdom := quadraticDefect_mul_ge_min K (-1 : Kˣ) (-a)
  have hfactor : (-1 : Kˣ) * (-a) = a := by simp
  rw [hfactor] at hdom
  have haDefect : (k : ℕ∞) ≤ quadraticDefect K a := by
    exact (le_min hminusOne (by simpa [hnegA] using hkDefect)).trans hdom
  exact
    squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
      a k haEven haDefect

/-- Every nonzero value of the diagonal form `X²+aY²` is a norm from
the quadratic algebra of parameter `-a`. -/
theorem squareClass_diagonalValue_mem_quadraticNorm
    (a : Kˣ) {x y : K}
    (hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0) :
    squareClass K (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) ∈
      quadraticNormSquareClassSubgroup K (-a) := by
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  refine ⟨qU, ?_, rfl⟩
  change IsQuadraticNorm K (-a) qU
  refine ⟨x, y, ?_⟩
  simp only [qU, Units.val_neg, Units.val_mk0]
  ring

/-- Square-class form of the positive-order square-difference lemma. -/
theorem squareClass_one_sub_positive_even_mem_principalUnit
    [QuadraticDefectLaws K]
    (u : Kˣ) (h : Int) (k : Nat)
    (huOrder : ordUnit K u = h) (hpos : 0 < h) (hEven : Even h)
    (hdefect : (k : ℕ∞) ≤ quadraticDefect K u)
    (hkBound : (k : Int) ≤
      (ramificationIndex K : Int) + h / 2)
    (hdelta0 : 1 - (u : K) ≠ 0) :
    squareClass K (Units.mk0 (1 - (u : K)) hdelta0) ∈
      principalUnitSquareClassSubgroup K k := by
  let deltaU : Kˣ := Units.mk0 (1 - (u : K)) hdelta0
  have hdeltaOrder : ordUnit K deltaU = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    have hlt : ord K (1 : K) < ord K (u : K) := by
      rw [ord_one, ← coe_ordUnit, huOrder]
      exact_mod_cast hpos
    have hzero : ord K (1 - (u : K)) = (0 : WithTop Int) := by
      simpa only [ord_one] using (ord K).map_sub_eq_of_lt_left hlt
    change ord K (1 - (u : K)) = ((0 : Int) : WithTop Int)
    rw [hzero]
    norm_num
  have hdeltaEven : Even (ordUnit K deltaU) := by
    rw [hdeltaOrder]
    exact ⟨0, by simp⟩
  apply
    squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
      deltaU k hdeltaEven
  exact quadraticDefect_one_sub_of_positive_even_order
    u h k huOrder hpos hEven hdefect hkBound hdelta0

/-- Square-class form of the equal-order cancellation lemma. -/
theorem squareClass_one_sub_unit_cancellation_mem_principalUnit
    [QuadraticDefectLaws K]
    (u : Kˣ) (n k : Nat)
    (hu : IsValuationUnit K (u : K))
    (horder : ord K (1 - (u : K)) = ((n : Int) : WithTop Int))
    (hnEven : Even n) (hnLt : n < 2 * ramificationIndex K)
    (hdefect : ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K u)
    (hkBound : (k : Int) ≤
      (ramificationIndex K : Int) - (n : Int) / 2)
    (hdelta0 : 1 - (u : K) ≠ 0) :
    squareClass K (Units.mk0 (1 - (u : K)) hdelta0) ∈
      principalUnitSquareClassSubgroup K k := by
  let deltaU : Kˣ := Units.mk0 (1 - (u : K)) hdelta0
  have hdeltaOrder : ordUnit K deltaU = (n : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa only [deltaU, Units.val_mk0] using horder
  have hdeltaEven : Even (ordUnit K deltaU) := by
    rw [hdeltaOrder]
    exact_mod_cast hnEven
  apply
    squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
      deltaU k hdeltaEven
  exact quadraticDefect_one_sub_of_unit_cancellation
    u n k hu horder hnEven hnLt hdefect hkBound hdelta0

/-- Common coordinate calculation for the even part of Xu's Proposition
2.3.  The hypothesis `hcancel` is the only branch-specific arithmetic: it
records the three bounds needed when the two diagonal terms have equal
order. -/
theorem squareClass_primitive_integralReflectionValue_mem_principalUnit_even
    [QuadraticDefectLaws K]
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R) (k : Nat) (hkPos : 0 < k)
    (hkE : k ≤ ramificationIndex K)
    (hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon))
    (hcancel : ∀ n : Nat,
      (n : Int) ≤ (ramificationIndex K : Int) - R / 2 →
        ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        (k : Int) ≤
          (ramificationIndex K : Int) - (n : Int) / 2)
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel
      (uniformizerPowerUnit K R * epsilon) 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)))
    (hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel
        (uniformizerPowerUnit K R * epsilon) 0)
      (L := binaryModelLattice (K := K)) hz) :
    squareClass K
        (Units.mk0
          ((QuadraticSpace.binaryModel
            (uniformizerPowerUnit K R * epsilon) 0).quadratic z) hz) ∈
      principalUnitSquareClassSubgroup K k := by
  classical
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have hnegADefect : quadraticDefect K (-a) =
      quadraticDefect K (-epsilon) := by
    dsimp only [a]
    exact beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R epsilon hUnit hEven
  have haPrincipal : squareClass K a ∈
      principalUnitSquareClassSubgroup K k := by
    simpa only [a] using
      squareClass_evenParameter_mem_principalUnitSquareClassSubgroup
        (K := K) R epsilon hUnit hEven k hkE hkDefect
  let x : K := z 0
  let y : K := z 1
  have hqFormula :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        x ^ 2 + (a : K) * y ^ 2 := by
    simp [QuadraticSpace.binaryModel_quadratic_apply, a, x, y]
  have hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0 := by
    rw [← hqFormula]
    change (QuadraticSpace.binaryModel
      (uniformizerPowerUnit K R * epsilon) 0).quadratic z ≠ 0 at hz
    simpa only [a] using hz
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  have htargetClass :
      squareClass K
          (Units.mk0
            ((QuadraticSpace.binaryModel
              (uniformizerPowerUnit K R * epsilon) 0).quadratic z) hz) =
        squareClass K qU := by
    congr 1
    apply Units.ext
    simpa only [a, qU, Units.val_mk0] using hqFormula
  rw [htargetClass]
  have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
  have hprimitive :=
    (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1
      hzPrimitive
  have hcoefficients :=
    (isIntegralReflection_binaryDiagonal_iff_of_primitive
      a (by simpa only [a] using hz) hzMem hzPrimitive).1
      (by simpa only [a] using hzIntegral)
  by_cases hxZero : x = 0
  · have hy0 : y ≠ 0 := by
      intro hy
      apply hq0
      simp [hxZero, hy]
    let yu : Kˣ := Units.mk0 y hy0
    have hqUnit : qU = a * yu ^ 2 := by
      apply Units.ext
      simp [qU, yu, hxZero]
    rw [hqUnit, squareClass_mul_square]
    exact haPrincipal
  by_cases hyZero : y = 0
  · let xu : Kˣ := Units.mk0 x hxZero
    have hqUnit : qU = 1 * xu ^ 2 := by
      apply Units.ext
      simp [qU, xu, hyZero]
    rw [hqUnit, squareClass_mul_square]
    exact (principalUnitSquareClassSubgroup K k).one_mem
  let xu : Kˣ := Units.mk0 x hxZero
  let yu : Kˣ := Units.mk0 y hyZero
  have hxMem : x ∈ IntegerRing K := by simpa [x] using hzCoords 0
  have hyMem : y ∈ IntegerRing K := by simpa [y] using hzCoords 1
  have hxNonneg : 0 ≤ ordUnit K xu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing xu (by simpa [xu] using hxMem)
  have hyNonneg : 0 ≤ ordUnit K yu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing yu (by simpa [yu] using hyMem)
  have hprimitiveOrders : ordUnit K xu = 0 ∨ ordUnit K yu = 0 := by
    rcases hprimitive with hxUnit | hyUnit
    · left
      exact (isValuationUnit_iff_ordUnit_eq_zero K xu).1
        (by simpa [x, xu] using hxUnit)
    · right
      exact (isValuationUnit_iff_ordUnit_eq_zero K yu).1
        (by simpa [y, yu] using hyUnit)
  let ratio : Kˣ := (-a) * (yu * xu⁻¹) ^ 2
  have hratioOrder : ordUnit K ratio =
      R + 2 * ordUnit K yu - 2 * ordUnit K xu := by
    simp only [ratio, ordUnit_mul, ordUnit_pow, ordUnit_inv,
      ordUnit_neg, haOrder]
    omega
  have hratioEven : Even (ordUnit K ratio) := by
    rcases hEven with ⟨r, hr⟩
    refine ⟨r + ordUnit K yu - ordUnit K xu, ?_⟩
    rw [hratioOrder]
    omega
  have hratioDefect : quadraticDefect K ratio =
      quadraticDefect K (-epsilon) := by
    dsimp only [ratio]
    rw [quadraticDefect_mul_square, hnegADefect]
  have hratioVal : (ratio : K) =
      -((a : K) * y ^ 2 / x ^ 2) := by
    simp only [ratio, xu, yu, Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    field_simp [hxZero]
  have hfactorX :
      x ^ 2 * (1 - (ratio : K)) = x ^ 2 + (a : K) * y ^ 2 := by
    rw [hratioVal]
    field_simp [hxZero]
    ring
  rcases lt_trichotomy 0 (ordUnit K ratio) with
      hratioPos | hratioZero | hratioNeg
  · have hdelta0 : 1 - (ratio : K) ≠ 0 := by
      intro hdelta
      apply hq0
      rw [← hfactorX, hdelta, mul_zero]
    have hkBound : (k : Int) ≤
        (ramificationIndex K : Int) + ordUnit K ratio / 2 := by
      have hkEInt : (k : Int) ≤ ramificationIndex K := by
        exact_mod_cast hkE
      rcases hratioEven with ⟨s, hs⟩
      omega
    have hdeltaMem :=
      squareClass_one_sub_positive_even_mem_principalUnit
        (K := K) ratio (ordUnit K ratio) k rfl hratioPos
          hratioEven (by simpa [hratioDefect] using hkDefect)
            hkBound hdelta0
    let deltaU : Kˣ := Units.mk0 (1 - (ratio : K)) hdelta0
    have hqUnit : qU = deltaU * xu ^ 2 := by
      apply Units.ext
      simp only [qU, deltaU, xu, Units.val_mk0, Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [← hfactorX]
      ring
    rw [hqUnit, squareClass_mul_square]
    exact hdeltaMem
  · have hratioZero' : ordUnit K ratio = 0 := hratioZero.symm
    have hratioUnit : IsValuationUnit K (ratio : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K ratio).2 hratioZero'
    have hdelta0 : 1 - (ratio : K) ≠ 0 := by
      intro hdelta
      apply hq0
      rw [← hfactorX, hdelta, mul_zero]
    let deltaU : Kˣ := Units.mk0 (1 - (ratio : K)) hdelta0
    have hratioOrdTop : ord K (ratio : K) = 0 := by
      rw [← coe_ordUnit, hratioZero']
      norm_num
    have hdeltaNonnegTop : (0 : WithTop Int) ≤
        ord K (1 - (ratio : K)) := by
      have hmin := min_ord_le_ord_add K (1 : K) (-(ratio : K))
      have hsum : (1 : K) + -(ratio : K) = 1 - (ratio : K) := by ring
      rw [hsum] at hmin
      simpa only [ord_one, ord_neg, hratioOrdTop, min_self] using hmin
    have hdeltaOrderNonneg : 0 ≤ ordUnit K deltaU := by
      apply WithTop.coe_le_coe.mp
      rw [coe_ordUnit]
      change ((0 : Int) : WithTop Int) ≤ ord K (1 - (ratio : K))
      norm_num
      exact hdeltaNonnegTop
    let n : Nat := Int.toNat (ordUnit K deltaU)
    have hnCast : (n : Int) = ordUnit K deltaU := by
      simpa only [n] using Int.toNat_of_nonneg hdeltaOrderNonneg
    have hdeltaOrder : ord K (1 - (ratio : K)) =
        ((n : Int) : WithTop Int) := by
      calc
        ord K (1 - (ratio : K)) =
            (ordUnit K deltaU : WithTop Int) := by
          simpa only [deltaU, Units.val_mk0] using
            (coe_ordUnit K deltaU).symm
        _ = ((n : Int) : WithTop Int) := by rw [hnCast]
    have hyOrderZero : ordUnit K yu = 0 := by
      rcases hprimitiveOrders with hxOrderZero | hyOrderZero
      · rw [hratioOrder] at hratioZero'
        omega
      · exact hyOrderZero
    have hqUnit : qU = deltaU * xu ^ 2 := by
      apply Units.ext
      simp only [qU, deltaU, xu, Units.val_mk0, Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [← hfactorX]
      ring
    have hqOrder : ordUnit K qU = 2 * ordUnit K xu + n := by
      rw [hqUnit, ordUnit_mul, ordUnit_pow, ← hnCast]
      omega
    have hxRelation : 2 * ordUnit K xu = R := by
      rw [hratioOrder, hyOrderZero] at hratioZero'
      omega
    have hfirst :
        2 * x / (x ^ 2 + (a : K) * y ^ 2) ∈ IntegerRing K := by
      have h := hcoefficients.1
      simpa only [hqFormula, x] using h
    let coefficient : Kˣ := Units.mk0
      (2 * x / (x ^ 2 + (a : K) * y ^ 2))
      (div_ne_zero (mul_ne_zero (by norm_num) hxZero) hq0)
    have hcoefficientNonneg : 0 ≤ ordUnit K coefficient :=
      Lattice.ordUnit_nonneg_of_mem_integerRing coefficient
        (by simpa [coefficient] using hfirst)
    let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
    have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, ramificationIndex_spec]
      rfl
    have hcoefficientUnit : coefficient = twoU * xu * qU⁻¹ := by
      apply Units.ext
      simp only [coefficient, twoU, xu, qU, Units.val_mk0,
        Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    have hcoefficientOrder : ordUnit K coefficient =
        (ramificationIndex K : Int) + ordUnit K xu - ordUnit K qU := by
      rw [hcoefficientUnit, ordUnit_mul, ordUnit_mul, ordUnit_inv,
        htwoOrder]
      omega
    have hnBound : (n : Int) ≤
        (ramificationIndex K : Int) - R / 2 := by
      rw [hcoefficientOrder, hqOrder] at hcoefficientNonneg
      rcases hEven with ⟨r, hr⟩
      omega
    obtain ⟨hnext, hnk, hkCancel⟩ := hcancel n hnBound
    have hnLt : n < 2 * ramificationIndex K := by
      have hePos := ramificationIndex_pos K
      exact_mod_cast (show (n : Int) <
        2 * (ramificationIndex K : Int) by omega)
    have hnEven : Even n := by
      by_cases hn0 : n = 0
      · have hzeroEven : Even (0 : Nat) := ⟨0, rfl⟩
        simpa only [hn0] using hzeroEven
      · apply even_order_one_sub_unit_of_succ_le_defect
          ratio hratioUnit n hdeltaOrder (Nat.pos_of_ne_zero hn0) hnLt
        simpa [hratioDefect] using hnext
    have hdeltaMem :=
      squareClass_one_sub_unit_cancellation_mem_principalUnit
        (K := K) ratio n k hratioUnit hdeltaOrder hnEven hnLt
          (by simpa [hratioDefect] using hnk) hkCancel hdelta0
    rw [hqUnit, squareClass_mul_square]
    exact hdeltaMem
  · let inverseRatio : Kˣ := ratio⁻¹
    have hinverseOrder : ordUnit K inverseRatio = -ordUnit K ratio := by
      simp [inverseRatio]
    have hinversePos : 0 < ordUnit K inverseRatio := by
      rw [hinverseOrder]
      omega
    have hinverseEven : Even (ordUnit K inverseRatio) := by
      rcases hratioEven with ⟨s, hs⟩
      refine ⟨-s, ?_⟩
      rw [hinverseOrder, hs]
      omega
    have hinverseDefect : quadraticDefect K inverseRatio =
        quadraticDefect K (-epsilon) := by
      dsimp only [inverseRatio]
      rw [quadraticDefect_inv, hratioDefect]
    have hfactorY :
        (a : K) * y ^ 2 * (1 - (inverseRatio : K)) =
          x ^ 2 + (a : K) * y ^ 2 := by
      dsimp only [inverseRatio]
      simp only [Units.val_inv_eq_inv_val]
      rw [hratioVal]
      field_simp [Units.ne_zero a, hxZero, hyZero]
      ring
    have hdelta0 : 1 - (inverseRatio : K) ≠ 0 := by
      intro hdelta
      apply hq0
      rw [← hfactorY, hdelta, mul_zero]
    have hkBound : (k : Int) ≤
        (ramificationIndex K : Int) + ordUnit K inverseRatio / 2 := by
      have hkEInt : (k : Int) ≤ ramificationIndex K := by
        exact_mod_cast hkE
      rcases hinverseEven with ⟨s, hs⟩
      omega
    have hdeltaMem :=
      squareClass_one_sub_positive_even_mem_principalUnit
        (K := K) inverseRatio (ordUnit K inverseRatio) k rfl
          hinversePos hinverseEven
            (by simpa [hinverseDefect] using hkDefect)
              hkBound hdelta0
    let deltaU : Kˣ := Units.mk0 (1 - (inverseRatio : K)) hdelta0
    have hqUnit : qU = (a * deltaU) * yu ^ 2 := by
      apply Units.ext
      simp only [qU, deltaU, yu, Units.val_mk0, Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [← hfactorY]
      ring
    rw [hqUnit, squareClass_mul_square, squareClass_mul_eq]
    exact (principalUnitSquareClassSubgroup K k).mul_mem
      haPrincipal hdeltaMem

/-- Subgroup-level form of the common even coordinate calculation. -/
theorem spinorNormImage_binaryDiagonal_le_principalUnit_even
    [QuadraticDefectLaws K]
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R) (k : Nat) (hkPos : 0 < k)
    (hkE : k ≤ ramificationIndex K)
    (hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon))
    (hcancel : ∀ n : Nat,
      (n : Int) ≤ (ramificationIndex K : Int) - R / 2 →
        ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        (k : Int) ≤
          (ramificationIndex K : Int) - (n : Int) / 2) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * epsilon) 0)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K k : Set (SquareClass K)) := by
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply unit_mem_integerRing_of_ordUnit_nonneg a
    rw [haOrder]
    exact hRnonneg
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  intro A hA
  rw [show uniformizerPowerUnit K R * epsilon = a by rfl,
    spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
      a 0 htwo hdiag] at hA
  rcases hA with ⟨z, hz, hzMem, hzPrimitive,
    hfirst, hsecond, hclass⟩
  have hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz :=
    (isIntegralReflection_binaryModel_iff_of_primitive
      a 0 hz hzMem hzPrimitive).2 ⟨hfirst, hsecond⟩
  have hvalueMem :=
    squareClass_primitive_integralReflectionValue_mem_principalUnit_even
      (K := K) R epsilon hUnit hRnonneg hRupper hEven k hkPos hkE
        hkDefect hcancel (by simpa only [a] using hz) hzMem hzPrimitive
          (by simpa only [a] using hzIntegral)
  rw [hclass] at hvalueMem
  exact hvalueMem

/-- The spinor image of an integral diagonal binary model is always
contained in its ambient quadratic norm square-class group. -/
theorem spinorNormImage_binaryDiagonal_le_quadraticNorm
    (a : Kˣ) (haIntegral : (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) ⊆
      (quadraticNormSquareClassSubgroup K (-a) : Set (SquareClass K)) := by
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  intro A hA
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag] at hA
  rcases hA with ⟨z, hz, _hzMem, _hzPrimitive,
    _hfirst, _hsecond, hclass⟩
  have hqFormula :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        z 0 ^ 2 + (a : K) * z 1 ^ 2 := by
    simp [QuadraticSpace.binaryModel_quadratic_apply]
  have hq0 : z 0 ^ 2 + (a : K) * z 1 ^ 2 ≠ 0 := by
    rw [← hqFormula]
    exact hz
  have hnorm := squareClass_diagonalValue_mem_quadraticNorm a hq0
  have hclass' :
      squareClass K
          (Units.mk0 (z 0 ^ 2 + (a : K) * z 1 ^ 2) hq0) = A := by
    rw [← hclass]
    congr 1
    apply Units.ext
    simpa only [Units.val_mk0] using hqFormula.symm
  rwa [hclass'] at hnorm

/-- Pure integer arithmetic behind the middle-defect even branch. -/
private theorem caseIIIMiddle_even_integer_bounds
    (e R d k : Int)
    (hePos : 0 < e) (hRnonneg : 0 ≤ R) (hRupper : R ≤ 2 * e)
    (hEven : Even R)
    (hdLower : 2 * e - R < 2 * d)
    (hdUpper : 4 * d ≤ 6 * e - R)
    (hk : k = R / 2 + d - e) :
    0 < k ∧ k ≤ e ∧ k ≤ d ∧
      ∀ n : Int, 0 ≤ n → n ≤ e - R / 2 →
        n + 1 ≤ d ∧ n + k ≤ d ∧ k ≤ e - n / 2 := by
  rcases hEven with ⟨r, hr⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  intro n hnNonneg hnUpper
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Pure integer arithmetic behind the high-defect even branch.  The
Euclidean quotient is exactly Beli's `floor((2e-R)/4)`. -/
private theorem caseIIIHigh_even_integer_bounds
    (e R d k : Int)
    (hePos : 0 < e) (hRnonneg : 0 ≤ R) (hRupper : R ≤ 2 * e)
    (hEven : Even R)
    (hdHigh : 6 * e - R < 4 * d)
    (hk : k = e - (2 * e - R) / 4) :
    0 < k ∧ k ≤ e ∧ k ≤ d ∧
      ∀ n : Int, 0 ≤ n → n ≤ e - R / 2 →
        n + 1 ≤ d ∧ n + k ≤ d ∧ k ≤ e - n / 2 := by
  rcases hEven with ⟨r, hr⟩
  have hdivLower := Int.ediv_mul_le (2 * e - R)
    (by norm_num : (4 : Int) ≠ 0)
  have hdivUpper : 2 * e - R < ((2 * e - R) / 4 + 1) * 4 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  intro n hnNonneg hnUpper
  have hhalfLower := Int.ediv_mul_le n (by norm_num : (2 : Int) ≠ 0)
  have hhalfUpper : n < (n / 2 + 1) * 2 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Xu (1993), Proposition 2.3(ii), forward containment in the even
middle-defect branch. -/
theorem spinorNormImage_binaryDiagonal_le_caseIIIMiddle_even
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hdUpper : 4 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (6 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * epsilon) 0)
        (L := binaryModelLattice (K := K)) ⊆
      ((principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIIMiddleExponent K
            (uniformizerPowerUnit K R * epsilon)) ⊓
        quadraticNormSquareClassSubgroup K
          (-(uniformizerPowerUnit K R * epsilon))) :
        Set (SquareClass K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  let e : Int := ramificationIndex K
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  let d : Nat := (quadraticDefect K (-epsilon)).toNat
  let k : Nat := beliSpinorCaseIIIMiddleExponent K a
  have hePos : 0 < e := by
    dsimp only [e]
    exact_mod_cast ramificationIndex_pos K
  have htop : quadraticDefect K (-epsilon) ≠ ⊤ := by
    intro htop
    rw [htop] at hdUpper
    simp at hdUpper
  have hdCoe : (d : ℕ∞) = quadraticDefect K (-epsilon) := by
    dsimp only [d]
    exact ENat.coe_toNat htop
  have hlowNat :
      Int.toNat (2 * (ramificationIndex K : Int) - R) < 2 * d := by
    have h := hdLower
    rw [← hdCoe] at h
    norm_cast at h
    omega
  have hlowInt : 2 * e - R < 2 * (d : Int) := by
    have hcast :
        (Int.toNat (2 * (ramificationIndex K : Int) - R) : Int) <
          2 * (d : Int) := by
      exact_mod_cast hlowNat
    have hnonneg : 0 ≤ 2 * (ramificationIndex K : Int) - R := by
      omega
    rw [Int.toNat_of_nonneg hnonneg] at hcast
    simpa only [e] using hcast
  have huppNat : 4 * d ≤
      Int.toNat (6 * (ramificationIndex K : Int) - R) := by
    have h := hdUpper
    rw [← hdCoe] at h
    norm_cast at h
  have huppInt : 4 * (d : Int) ≤ 6 * e - R := by
    have hcast : 4 * (d : Int) ≤
        (Int.toNat (6 * (ramificationIndex K : Int) - R) : Int) := by
      exact_mod_cast huppNat
    have hnonneg : 0 ≤ 6 * (ramificationIndex K : Int) - R := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    rw [Int.toNat_of_nonneg hnonneg] at hcast
    simpa only [e] using hcast
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have hparameterDefect : beliParameterDefect K a =
      quadraticDefect K (-epsilon) := by
    dsimp only [a]
    exact beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R epsilon hUnit hEven
  have hparameterDefectNat : beliParameterDefectNat K a = d := by
    unfold beliParameterDefectNat
    rw [hparameterDefect]
  have hkFormula : k =
      Int.toNat (R / 2 + (d : Int) - e) := by
    dsimp only [k]
    unfold beliSpinorCaseIIIMiddleExponent
    rw [haOrder, hparameterDefectNat]
  have hkInsidePos : 0 < R / 2 + (d : Int) - e := by
    rcases hEven with ⟨r, hr⟩
    omega
  have hkInt : (k : Int) = R / 2 + (d : Int) - e := by
    rw [hkFormula, Int.toNat_of_nonneg hkInsidePos.le]
  have hbounds := caseIIIMiddle_even_integer_bounds
    e R (d : Int) (k : Int) hePos hRnonneg
      (by simpa only [e] using hRupper) hEven hlowInt huppInt hkInt
  have hkPos : 0 < k := by exact_mod_cast hbounds.1
  have hkE : k ≤ ramificationIndex K := by
    have hkEInt : (k : Int) ≤ (ramificationIndex K : Int) := by
      simpa only [e] using (show (k : Int) ≤ e from hbounds.2.1)
    exact_mod_cast hkEInt
  have hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon) := by
    rw [← hdCoe]
    exact_mod_cast (show (k : Int) ≤ (d : Int) from hbounds.2.2.1)
  have hcancel : ∀ n : Nat,
      (n : Int) ≤ (ramificationIndex K : Int) - R / 2 →
        ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
        (k : Int) ≤
          (ramificationIndex K : Int) - (n : Int) / 2 := by
    intro n hnUpper
    have hb := hbounds.2.2.2 (n : Int) (by positivity)
      (by simpa only [e] using hnUpper)
    constructor
    · rw [← hdCoe]
      exact_mod_cast hb.1
    constructor
    · rw [← hdCoe]
      exact_mod_cast hb.2.1
    · simpa only [e] using hb.2.2
  have hprincipal :=
    spinorNormImage_binaryDiagonal_le_principalUnit_even
      (K := K) R epsilon hUnit hRnonneg hRupper hEven k hkPos hkE
        hkDefect hcancel
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply unit_mem_integerRing_of_ordUnit_nonneg a
    rw [haOrder]
    exact hRnonneg
  have hnorm := spinorNormImage_binaryDiagonal_le_quadraticNorm
    (K := K) a haIntegral
  intro A hA
  change A ∈ principalUnitSquareClassSubgroup K k ⊓
    quadraticNormSquareClassSubgroup K (-a)
  constructor
  · exact hprincipal hA
  · exact hnorm (by simpa only [a] using hA)

/-- Xu (1993), Proposition 2.3(ii), forward containment in the even
high-defect branch. -/
theorem spinorNormImage_binaryDiagonal_le_caseIIIHigh_even
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdHigh : ¬4 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (6 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * epsilon) 0)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIIHighExponent K
            (uniformizerPowerUnit K R * epsilon)) :
        Set (SquareClass K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  let e : Int := ramificationIndex K
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  let k : Nat := beliSpinorCaseIIIHighExponent K a
  have hePos : 0 < e := by
    dsimp only [e]
    exact_mod_cast ramificationIndex_pos K
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have hkFormula : k =
      Int.toNat (e - (2 * e - R) / 4) := by
    dsimp only [k]
    unfold beliSpinorCaseIIIHighExponent
    rw [haOrder]
  have hdivLower := Int.ediv_mul_le (2 * e - R)
    (by norm_num : (4 : Int) ≠ 0)
  have hdivUpper : 2 * e - R < ((2 * e - R) / 4 + 1) * 4 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hkInsidePos : 0 < e - (2 * e - R) / 4 := by
    rcases hEven with ⟨r, hr⟩
    have hRupper' : R ≤ 2 * e := by simpa only [e] using hRupper
    omega
  have hkInt : (k : Int) = e - (2 * e - R) / 4 := by
    rw [hkFormula, Int.toNat_of_nonneg hkInsidePos.le]
  have hfakeHigh : 6 * e - R < 4 * (2 * e + 1) := by
    have hRnonneg' : 0 ≤ R := hRnonneg
    omega
  have hbase := caseIIIHigh_even_integer_bounds
    e R (2 * e + 1) (k : Int) hePos hRnonneg
      (by simpa only [e] using hRupper) hEven hfakeHigh hkInt
  have hkPos : 0 < k := by exact_mod_cast hbase.1
  have hkE : k ≤ ramificationIndex K := by
    have hkEInt : (k : Int) ≤ (ramificationIndex K : Int) := by
      simpa only [e] using (show (k : Int) ≤ e from hbase.2.1)
    exact_mod_cast hkEInt
  by_cases htop : quadraticDefect K (-epsilon) = ⊤
  · have hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon) := by
      rw [htop]
      exact le_top
    have hcancel : ∀ n : Nat,
        (n : Int) ≤ (ramificationIndex K : Int) - R / 2 →
          ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
          ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
          (k : Int) ≤
            (ramificationIndex K : Int) - (n : Int) / 2 := by
      intro n hnUpper
      have hb := hbase.2.2.2 (n : Int) (by positivity)
        (by simpa only [e] using hnUpper)
      constructor
      · rw [htop]
        exact le_top
      constructor
      · rw [htop]
        exact le_top
      · simpa only [e] using hb.2.2
    exact spinorNormImage_binaryDiagonal_le_principalUnit_even
      (K := K) R epsilon hUnit hRnonneg hRupper hEven k hkPos hkE
        hkDefect hcancel
  · let d : Nat := (quadraticDefect K (-epsilon)).toNat
    have hdCoe : (d : ℕ∞) = quadraticDefect K (-epsilon) := by
      dsimp only [d]
      exact ENat.coe_toNat htop
    have hhighNat :
        Int.toNat (6 * (ramificationIndex K : Int) - R) < 4 * d := by
      have h := hdHigh
      rw [← hdCoe] at h
      norm_cast at h
      omega
    have hhighInt : 6 * e - R < 4 * (d : Int) := by
      have hcast :
          (Int.toNat (6 * (ramificationIndex K : Int) - R) : Int) <
            4 * (d : Int) := by
        exact_mod_cast hhighNat
      have hnonneg : 0 ≤ 6 * (ramificationIndex K : Int) - R := by
        have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
        omega
      rw [Int.toNat_of_nonneg hnonneg] at hcast
      simpa only [e] using hcast
    have hbounds := caseIIIHigh_even_integer_bounds
      e R (d : Int) (k : Int) hePos hRnonneg
        (by simpa only [e] using hRupper) hEven hhighInt hkInt
    have hkDefect : (k : ℕ∞) ≤ quadraticDefect K (-epsilon) := by
      rw [← hdCoe]
      exact_mod_cast (show (k : Int) ≤ (d : Int) from hbounds.2.2.1)
    have hcancel : ∀ n : Nat,
        (n : Int) ≤ (ramificationIndex K : Int) - R / 2 →
          ((n + 1 : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
          ((n + k : Nat) : ℕ∞) ≤ quadraticDefect K (-epsilon) ∧
          (k : Int) ≤
            (ramificationIndex K : Int) - (n : Int) / 2 := by
      intro n hnUpper
      have hb := hbounds.2.2.2 (n : Int) (by positivity)
        (by simpa only [e] using hnUpper)
      constructor
      · rw [← hdCoe]
        exact_mod_cast hb.1
      constructor
      · rw [← hdCoe]
        exact_mod_cast hb.2.1
      · simpa only [e] using hb.2.2
    exact spinorNormImage_binaryDiagonal_le_principalUnit_even
      (K := K) R epsilon hUnit hRnonneg hRupper hEven k hkPos hkE
        hkDefect hcancel

/-- Complete even, non-low-defect part of Xu (1993), Proposition 2.3,
written for the normalized parameter `pi^R epsilon`. -/
theorem spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_even_nonlow
    (R : Int) (epsilon : Kˣ)
    (hUnit : IsValuationUnit K (epsilon : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * epsilon))
    (hRnonneg : 0 ≤ R)
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * epsilon) 0)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K
        (uniformizerPowerUnit K R * epsilon) : Set (SquareClass K)) := by
  let a : Kˣ := uniformizerPowerUnit K R * epsilon
  have haOrder : ordUnit K a = R := by
    dsimp only [a]
    exact ordUnit_uniformizerPower_mul_valuationUnit epsilon hUnit R
  have hparameterDefect : beliParameterDefect K a =
      quadraticDefect K (-epsilon) := by
    dsimp only [a]
    exact beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R epsilon hUnit hEven
  have hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K) := by
    intro hclass
    have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
    rw [haOrder, ordUnit_negativeQuarterUnit] at horder
    have hePos := ramificationIndex_pos K
    omega
  have hRrep : ordUnit K a ≤ 2 * (ramificationIndex K : Int) := by
    rwa [haOrder]
  have hdLowerRep : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [haOrder, hparameterDefect]
    exact hdLower
  have hshiftFormula : beliSpinorGroupRepresentative K a =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * epsilon) := by
    exact beliSpinorGroupRepresentative_eq_evenShift_normGenerator
      (K := K) R epsilon hUnit (by simpa only [a] using ha)
        hRupper hEven hdLower
  have hreverse :=
    evenShiftedNormGeneratorGroup_le_spinorNormImage_binaryDiagonal
      (K := K) R epsilon hUnit (by simpa only [a] using ha)
        hRnonneg hRupper hEven hdLower
  apply Set.Subset.antisymm
  · by_cases hdUpper : 4 * quadraticDefect K (-epsilon) ≤
        (Int.toNat (6 * (ramificationIndex K : Int) - R) : ℕ∞)
    · have hupper :=
        spinorNormImage_binaryDiagonal_le_caseIIIMiddle_even
          (K := K) R epsilon hUnit hRnonneg hRupper hEven
            hdLower hdUpper
      have hdUpperRep : 4 * beliParameterDefect K a ≤
          (beliSpinorCaseIIIUpperCutoff K a : ℕ∞) := by
        unfold beliSpinorCaseIIIUpperCutoff
        rw [haOrder, hparameterDefect]
        exact hdUpper
      have hformula := beliSpinorGroupRepresentative_caseIII_middle
        K a (by simpa only [a] using ha) hquarter hRrep
          hdLowerRep hdUpperRep
      rw [show uniformizerPowerUnit K R * epsilon = a by rfl]
      rw [hformula]
      exact hupper
    · have hupper :=
        spinorNormImage_binaryDiagonal_le_caseIIIHigh_even
          (K := K) R epsilon hUnit hRnonneg hRupper hEven hdUpper
      have hdUpperRep : ¬4 * beliParameterDefect K a ≤
          (beliSpinorCaseIIIUpperCutoff K a : ℕ∞) := by
        unfold beliSpinorCaseIIIUpperCutoff
        rw [haOrder, hparameterDefect]
        exact hdUpper
      have hformula := beliSpinorGroupRepresentative_caseIII_high
        K a (by simpa only [a] using ha) hquarter hRrep
          hdLowerRep hdUpperRep
      rw [show uniformizerPowerUnit K R * epsilon = a by rfl]
      rw [hformula]
      exact hupper
  · intro A hA
    have hshiftMem : A ∈ beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * epsilon) := by
      rw [← hshiftFormula]
      change A ∈ (beliSpinorGroupRepresentative K a : Set (SquareClass K))
      simpa only [a] using hA
    exact hreverse hshiftMem

/-- The same even non-low formula for an arbitrary representative, obtained
by removing its uniformizer power. -/
theorem spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_even_nonlow
    (a : Kˣ)
    (hRnonneg : 0 ≤ ordUnit K a)
    (hRupper : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  let R : Int := ordUnit K a
  let epsilon : Kˣ := normalizedUnitPart K a
  have hUnit : IsValuationUnit K (epsilon : K) := by
    simpa only [epsilon] using normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * epsilon = a := by
    simpa only [R, epsilon] using uniformizerPower_mul_normalizedUnitPart K a
  have hdefect : quadraticDefect K (-epsilon) =
      beliParameterDefect K a := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) R epsilon hUnit (by simpa only [R] using hEven)
    rw [hfactor] at h
    exact h.symm
  have hdLower' : ¬2 * quadraticDefect K (-epsilon) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
    unfold beliSpinorCaseIIILowerCutoff at hdLower
    rw [hdefect]
    simpa only [R] using hdLower
  have ha : IsBinaryParameterAdmissible a :=
    isBinaryParameterAdmissible_of_ordUnit_nonneg hRnonneg
  have h :=
    spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_even_nonlow
      (K := K) R epsilon hUnit (by simpa only [hfactor] using ha)
        (by simpa only [R] using hRnonneg)
          (by simpa only [R] using hRupper)
            (by simpa only [R] using hEven) hdLower'
  simpa only [hfactor] using h

universe v

/-- The even non-low formula transported from the diagonal model to an
arbitrary binary BONG. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_even_nonlow
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hRnonneg : 0 ≤ b.binaryOrderGap)
    (hRupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hEven : Even b.binaryOrderGap)
    (hdLower : ¬2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  rw [b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hRnonneg]
  apply
    spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_even_nonlow
  · change 0 ≤ b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change b.binaryParameterOrder ≤ 2 * (ramificationIndex K : Int)
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change Even b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · exact hdLower

end BONG

end Bong
