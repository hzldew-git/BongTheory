/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryModularSpinorUpper
import Bong.Bong.BinaryDefectAdaptedShear
import Bong.Bong.BinarySquareDifferenceDefect
import Bong.Bong.BinaryEndpointSpinor

/-!
# Principal-unit upper bounds in the negative modular branch

This file isolates the valuation calculation behind Hsia (1975),
Propositions C--E, and Xu (1989).  For a defect-adapted shear, integrality
of a primitive reflection first bounds the order of its first coordinate.
The quadratic value is then a square plus an error deep enough to lie in
the required principal-unit square-class subgroup.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- An absolute square approximation whose error begins at `ord(a) + k`
gives normalized quadratic defect at least `k`. -/
theorem quadraticDefect_ge_of_absolute_square_approximation
    [QuadraticDefectLaws K]
    (a : Kˣ) (x : K) (h : Int) (k : Nat)
    (haOrder : ordUnit K a = h)
    (herror : (((h + (k : Int) : Int)) : WithTop Int) ≤
      ord K ((a : K) - x ^ 2)) :
    (k : ℕ∞) ≤ quadraticDefect K a := by
  apply natCast_le_quadraticDefect K
  refine ⟨x, ?_⟩
  have hfield :
      1 - x ^ 2 / (a : K) = ((a : K) - x ^ 2) / (a : K) := by
    field_simp [Units.ne_zero a]
  rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
    ← coe_ordUnit, haOrder]
  have hadd := add_le_add_right herror (-(h : WithTop Int))
  calc
    ((k : Int) : WithTop Int) =
        ((h + (k : Int) : Int) : WithTop Int) +
          (-(h : WithTop Int)) := by
            norm_cast
            omega
    _ ≤ ord K ((a : K) - x ^ 2) + (-(h : WithTop Int)) := by
      simpa [add_comm] using hadd

/-- Coordinate form of the principal-unit upper bound for a negative
modular binary model.  The hypotheses are the arithmetic content common to
the middle- and high-defect branches. -/
theorem squareClass_primitive_integralReflectionValue_mem_principalUnit_modular
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K) (r m : Int) (k : Nat)
    (hrNeg : r < 0) (hmNonneg : 0 ≤ m)
    (hm : m = (ramificationIndex K : Int) + r)
    (hcOrder : ord K c = (r : WithTop Int))
    (hdiagDepth :
      c ^ 2 + (a : K) = 0 ∨
        ∃ H : Int,
          ord K (c ^ 2 + (a : K)) = (H : WithTop Int) ∧
            m + (k : Int) ≤ H)
    (hkPos : 0 < k)
    (hkHalf : (k : Int) + m / 2 ≤ m)
    {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)))
    (hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hz) :
    squareClass K
        (Units.mk0
          ((QuadraticSpace.binaryModel a c).quadratic z) hz) ∈
      principalUnitSquareClassSubgroup K k := by
  classical
  let x : K := z 0
  let y : K := z 1
  let D : K := c ^ 2 + (a : K)
  let qv : K := (QuadraticSpace.binaryModel a c).quadratic z
  have hq0 : qv ≠ 0 := by
    change (QuadraticSpace.binaryModel a c).quadratic z ≠ 0
    exact hz
  let qU : Kˣ := Units.mk0 qv hq0
  change squareClass K qU ∈ principalUnitSquareClassSubgroup K k
  have hqExpanded :
      qv = x ^ 2 + ((2 : K) * c) * x * y + D * y ^ 2 := by
    simp only [qv, x, y, D,
      QuadraticSpace.binaryModel_quadratic_apply]
    ring
  have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
  have hxMem : x ∈ IntegerRing K := by simpa [x] using hzCoords 0
  have hyMem : y ∈ IntegerRing K := by simpa [y] using hzCoords 1
  have hprimitive :=
    (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1
      hzPrimitive
  have hcoefficients :=
    (isIntegralReflection_binaryModel_iff_of_primitive
      a c hz hzMem hzPrimitive).1 hzIntegral
  have hmHalfNonneg : 0 ≤ m / 2 := Int.ediv_nonneg hmNonneg (by omega)
  have hkLeM : (k : Int) ≤ m := by omega
  have htwoCOrder : ord K ((2 : K) * c) = (m : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder, hm]
    norm_cast
  by_cases hxUnit : IsValuationUnit K x
  · have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, IsValuationUnit, ord_zero] at hxUnit
      exact WithTop.top_ne_coe hxUnit
    let xu : Kˣ := Units.mk0 x hx0
    have hxOrder : ordUnit K xu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K xu).1
        (by simpa [xu] using hxUnit)
    have hxOrderField : ord K x =
        (ordUnit K xu : WithTop Int) := by
      simpa only [xu, Units.val_mk0] using (coe_ordUnit K xu).symm
    by_cases hy0 : y = 0
    · have hqUnit : qU = xu ^ 2 := by
        apply Units.ext
        simp [qU, qv, xu, hqExpanded, hy0]
      rw [hqUnit]
      have hclass : squareClass K (xu ^ 2) =
          squareClass K (1 : Kˣ) := by
        simpa only [one_mul] using squareClass_mul_square K (1 : Kˣ) xu
      rw [hclass]
      change (1 : SquareClass K) ∈ principalUnitSquareClassSubgroup K k
      exact (principalUnitSquareClassSubgroup K k).one_mem
    · let yu : Kˣ := Units.mk0 y hy0
      have hyOrderNonneg : 0 ≤ ordUnit K yu :=
        Lattice.ordUnit_nonneg_of_mem_integerRing yu
          (by simpa [yu] using hyMem)
      have hyOrderField : ord K y =
          (ordUnit K yu : WithTop Int) := by
        simpa only [yu, Units.val_mk0] using (coe_ordUnit K yu).symm
      let cross : K := ((2 : K) * c) * x * y
      let diagonal : K := D * y ^ 2
      let error : K := cross + diagonal
      have hcrossOrder : ord K cross =
          ((m + ordUnit K yu : Int) : WithTop Int) := by
        dsimp only [cross]
        rw [ord_mul, ord_mul, htwoCOrder, hxOrderField,
          hxOrder, hyOrderField]
        norm_cast
        omega
      have hcrossLower : ((k : Int) : WithTop Int) ≤ ord K cross := by
        rw [hcrossOrder]
        exact_mod_cast (show (k : Int) ≤ m + ordUnit K yu by omega)
      have hdiagonalLower : ((k : Int) : WithTop Int) ≤
          ord K diagonal := by
        rcases hdiagDepth with hDzero | ⟨H, hDOrder, hmkH⟩
        · simp [diagonal, D, hDzero]
        · dsimp only [diagonal]
          rw [ord_mul, show ord K D = (H : WithTop Int) by
            simpa only [D] using hDOrder, ord_pow, hyOrderField]
          exact_mod_cast (show (k : Int) ≤
            H + 2 * ordUnit K yu by omega)
      have herrorLower : ((k : Int) : WithTop Int) ≤ ord K error := by
        exact (le_min hcrossLower hdiagonalLower).trans
          (min_ord_le_ord_add K cross diagonal)
      have herrorPositive : (0 : WithTop Int) < ord K error := by
        exact (by exact_mod_cast hkPos :
          (0 : WithTop Int) < ((k : Int) : WithTop Int)).trans_le
            herrorLower
      have hxSqOrder : ord K (x ^ 2) = 0 := by
        rw [ord_pow, hxOrderField, hxOrder]
        norm_num
      have hqDecomp : qv = x ^ 2 + error := by
        rw [hqExpanded]
        simp only [error, cross, diagonal]
        ring
      have hqOrderField : ord K qv = 0 := by
        rw [hqDecomp, (ord K).map_add_eq_of_lt_left]
        · exact hxSqOrder
        · simpa only [hxSqOrder] using herrorPositive
      have hqOrder : ordUnit K qU = 0 := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        change ord K qv = ((0 : Int) : WithTop Int)
        simpa using hqOrderField
      have habsolute : (((0 + (k : Int) : Int)) : WithTop Int) ≤
          ord K ((qU : K) - x ^ 2) := by
        have hdiff : (qU : K) - x ^ 2 = error := by
          simp only [qU, Units.val_mk0]
          rw [hqDecomp]
          ring
        rw [hdiff]
        simpa using herrorLower
      apply squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
      · rw [hqOrder]
        exact ⟨0, by simp⟩
      · exact quadraticDefect_ge_of_absolute_square_approximation
          qU x 0 k hqOrder habsolute
  · have hyUnit : IsValuationUnit K y := hprimitive.resolve_left hxUnit
    have hy0 : y ≠ 0 := by
      intro hy
      rw [hy, IsValuationUnit, ord_zero] at hyUnit
      exact WithTop.top_ne_coe hyUnit
    let yu : Kˣ := Units.mk0 y hy0
    have hyOrder : ordUnit K yu = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K yu).1
        (by simpa [yu] using hyUnit)
    have hyOrderField : ord K y =
        (ordUnit K yu : WithTop Int) := by
      simpa only [yu, Units.val_mk0] using (coe_ordUnit K yu).symm
    have hcyOrder : ord K (c * y) = (r : WithTop Int) := by
      rw [ord_mul, hcOrder, hyOrderField, hyOrder]
      norm_num
    have hxOrderGt : (r : WithTop Int) < ord K x := by
      by_cases hx0 : x = 0
      · rw [hx0, ord_zero]
        exact WithTop.coe_lt_top r
      · let xu : Kˣ := Units.mk0 x hx0
        have hxNonneg : 0 ≤ ordUnit K xu :=
          Lattice.ordUnit_nonneg_of_mem_integerRing xu
            (by simpa [xu] using hxMem)
        rw [← show (xu : K) = x by rfl, ← coe_ordUnit]
        exact_mod_cast (show r < ordUnit K xu by omega)
    let l₁ : K := x + c * y
    have hl₁Order : ord K l₁ = (r : WithTop Int) := by
      dsimp only [l₁]
      have hsum := (ord K).map_add_eq_of_lt_right
        (show ord K x > ord K (c * y) by
          rw [hcyOrder]
          exact hxOrderGt)
      simpa only [hcyOrder] using hsum
    have hl₁Ne : l₁ ≠ 0 := by
      apply (ord_eq_top_iff K).not.mp
      rw [hl₁Order]
      exact WithTop.coe_ne_top
    let l₁U : Kˣ := Units.mk0 l₁ hl₁Ne
    have hl₁UnitOrder : ordUnit K l₁U = r := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      simpa only [l₁U, Units.val_mk0] using hl₁Order
    let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
    have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, ramificationIndex_spec]
      rfl
    let coefficient : Kˣ := twoU * l₁U * qU⁻¹
    have hcoefficientMem : (coefficient : K) ∈ IntegerRing K := by
      have hfirst := hcoefficients.1
      simpa [coefficient, twoU, l₁U, l₁, qU, qv,
        div_eq_mul_inv, mul_assoc] using hfirst
    have hcoefficientNonneg : 0 ≤ ordUnit K coefficient :=
      Lattice.ordUnit_nonneg_of_mem_integerRing coefficient
        hcoefficientMem
    have hcoefficientOrder : ordUnit K coefficient =
        (ramificationIndex K : Int) + r - ordUnit K qU := by
      simp only [coefficient, ordUnit_mul, ordUnit_inv,
        htwoOrder, hl₁UnitOrder]
      omega
    have hqBound : ordUnit K qU ≤ m := by
      rw [hcoefficientOrder] at hcoefficientNonneg
      omega
    have hx0 : x ≠ 0 := by
      intro hxzero
      rcases hdiagDepth with hDzero | ⟨H, hDOrder, hmkH⟩
      · apply hz
        change qv = 0
        rw [hqExpanded, hxzero]
        simp [D, hDzero]
      · have hqOrderH : ordUnit K qU = H := by
          apply WithTop.coe_injective
          rw [coe_ordUnit]
          change ord K qv = (H : WithTop Int)
          have hqAtZero : qv = D * y ^ 2 := by
            rw [hqExpanded, hxzero]
            ring
          rw [hqAtZero]
          rw [ord_mul, show ord K D = (H : WithTop Int) by
            simpa only [D] using hDOrder, ord_pow, hyOrderField,
            hyOrder]
          norm_num
        rw [hqOrderH] at hqBound
        omega
    let xu : Kˣ := Units.mk0 x hx0
    have hxOrderField : ord K x =
        (ordUnit K xu : WithTop Int) := by
      simpa only [xu, Units.val_mk0] using (coe_ordUnit K xu).symm
    have hxNonneg : 0 ≤ ordUnit K xu :=
      Lattice.ordUnit_nonneg_of_mem_integerRing xu
        (by simpa [xu] using hxMem)
    have hxOrderNe : ordUnit K xu ≠ 0 := by
      intro hzero
      apply hxUnit
      exact (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hzero
    have hxPos : 0 < ordUnit K xu := lt_of_le_of_ne hxNonneg
      (Ne.symm hxOrderNe)
    let X : Int := ordUnit K xu
    let cross : K := ((2 : K) * c) * x * y
    let diagonal : K := D * y ^ 2
    let error : K := cross + diagonal
    have hXPos : 0 < X := by simpa only [X] using hxPos
    have hxSqOrder : ord K (x ^ 2) = ((2 * X : Int) : WithTop Int) := by
      rw [ord_pow, hxOrderField]
      change (2 : ℕ) • (ordUnit K xu : WithTop Int) =
        ((2 * X : Int) : WithTop Int)
      norm_cast
    have hcrossOrder : ord K cross =
        ((m + X : Int) : WithTop Int) := by
      dsimp only [cross]
      rw [ord_mul, ord_mul, htwoCOrder, hxOrderField,
        hyOrderField, hyOrder]
      norm_cast
      simp only [X, add_zero]
    have hdiagGtM : (m : WithTop Int) < ord K diagonal := by
      rcases hdiagDepth with hDzero | ⟨H, hDOrder, hmkH⟩
      · simp [diagonal, D, hDzero]
      · dsimp only [diagonal]
        rw [ord_mul, show ord K D = (H : WithTop Int) by
          simpa only [D] using hDOrder, ord_pow, hyOrderField,
          hyOrder]
        norm_num
        exact_mod_cast (show m < H by omega)
    have htwoXLeM : 2 * X ≤ m := by
      by_contra hnot
      have htwoXGt : m < 2 * X := by omega
      have hcrossGt : (m : WithTop Int) < ord K cross := by
        rw [hcrossOrder]
        exact_mod_cast (show m < m + X by omega)
      have hxSqGt : (m : WithTop Int) < ord K (x ^ 2) := by
        rw [hxSqOrder]
        exact_mod_cast htwoXGt
      have hfirstGt : (m : WithTop Int) <
          ord K (x ^ 2 + cross) :=
        (lt_min hxSqGt hcrossGt).trans_le
          (min_ord_le_ord_add K (x ^ 2) cross)
      have hqGt : (m : WithTop Int) < ord K qv := by
        have hsum : (m : WithTop Int) <
            ord K ((x ^ 2 + cross) + diagonal) :=
          (lt_min hfirstGt hdiagGtM).trans_le
            (min_ord_le_ord_add K (x ^ 2 + cross) diagonal)
        rw [hqExpanded]
        simpa only [cross, diagonal, add_assoc] using hsum
      have hqOrderField : ord K qv =
          (ordUnit K qU : WithTop Int) := by
        simpa only [qU, Units.val_mk0] using (coe_ordUnit K qU).symm
      rw [hqOrderField] at hqGt
      exact (not_lt_of_ge hqBound) (by exact_mod_cast hqGt)
    have hXLeHalf : X ≤ m / 2 := by omega
    have hXKLeM : X + (k : Int) ≤ m := by omega
    have hcrossDeep :
        ((2 * X + (k : Int) : Int) : WithTop Int) ≤ ord K cross := by
      rw [hcrossOrder]
      exact_mod_cast (show 2 * X + (k : Int) ≤ m + X by omega)
    have hdiagDeep :
        ((2 * X + (k : Int) : Int) : WithTop Int) ≤
          ord K diagonal := by
      rcases hdiagDepth with hDzero | ⟨H, hDOrder, hmkH⟩
      · simp [diagonal, D, hDzero]
      · dsimp only [diagonal]
        rw [ord_mul, show ord K D = (H : WithTop Int) by
          simpa only [D] using hDOrder, ord_pow, hyOrderField,
          hyOrder]
        have hInt : 2 * X + (k : Int) ≤ H := by omega
        have hcast : ((2 * X + (k : Int) : Int) : WithTop Int) ≤
            (H : WithTop Int) := by exact_mod_cast hInt
        simpa using hcast
    have herrorDeep :
        ((2 * X + (k : Int) : Int) : WithTop Int) ≤ ord K error :=
      (le_min hcrossDeep hdiagDeep).trans
        (min_ord_le_ord_add K cross diagonal)
    have herrorStrict : ord K (x ^ 2) < ord K error := by
      rw [hxSqOrder]
      exact (by exact_mod_cast (show 2 * X < 2 * X + (k : Int) by
        omega) :
          ((2 * X : Int) : WithTop Int) <
            ((2 * X + (k : Int) : Int) : WithTop Int)).trans_le
              herrorDeep
    have hqDecomp : qv = x ^ 2 + error := by
      rw [hqExpanded]
      simp only [error, cross, diagonal]
      ring
    have hqOrderField : ord K qv =
        ((2 * X : Int) : WithTop Int) := by
      rw [hqDecomp, (ord K).map_add_eq_of_lt_left herrorStrict,
        hxSqOrder]
    have hqOrder : ordUnit K qU = 2 * X := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      simpa only [qU, Units.val_mk0] using hqOrderField
    have habsolute :
        (((2 * X + (k : Int) : Int)) : WithTop Int) ≤
          ord K ((qU : K) - x ^ 2) := by
      have hdiff : (qU : K) - x ^ 2 = error := by
        simp only [qU, Units.val_mk0]
        rw [hqDecomp]
        ring
      rwa [hdiff]
    apply squareClass_mem_principalUnitSquareClassSubgroup_of_even_order_of_defect
    · rw [hqOrder]
      exact ⟨X, by omega⟩
    · exact quadraticDefect_ge_of_absolute_square_approximation
        qU x (2 * X) k hqOrder habsolute

/-- Subgroup-level form of the negative modular coordinate calculation. -/
theorem spinorNormImage_binaryModel_le_principalUnit_modular
    [QuadraticDefectLaws K]
    (a : Kˣ) (c : K) (r m : Int) (k : Nat)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hrNeg : r < 0) (hmNonneg : 0 ≤ m)
    (hm : m = (ramificationIndex K : Int) + r)
    (hcOrder : ord K c = (r : WithTop Int))
    (hdiagDepth :
      c ^ 2 + (a : K) = 0 ∨
        ∃ H : Int,
          ord K (c ^ 2 + (a : K)) = (H : WithTop Int) ∧
            m + (k : Int) ≤ H)
    (hkPos : 0 < k)
    (hkHalf : (k : Int) + m / 2 ≤ m) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K k : Set (SquareClass K)) := by
  intro A hA
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a c htwo hdiag] at hA
  rcases hA with ⟨z, hz, hzMem, hzPrimitive,
    hfirst, hsecond, hclass⟩
  have hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hz :=
    (isIntegralReflection_binaryModel_iff_of_primitive
      a c hz hzMem hzPrimitive).2 ⟨hfirst, hsecond⟩
  have hmem :=
    squareClass_primitive_integralReflectionValue_mem_principalUnit_modular
      (K := K) a c r m k hrNeg hmNonneg hm hcOrder hdiagDepth
        hkPos hkHalf hz hzMem hzPrimitive hzIntegral
  rwa [hclass] at hmem

/-- Integer inequalities for the negative-order middle-defect branch. -/
private theorem caseIIIMiddle_negative_integer_bounds
    (e R d k : Int)
    (hePos : 0 < e)
    (hRlower : -(2 * e) ≤ R) (hRneg : R < 0)
    (hEven : Even R)
    (hdLower : 2 * e - R < 2 * d)
    (hdUpper : 4 * d ≤ 6 * e - R)
    (hk : k = R / 2 + d - e) :
    let r := R / 2
    let m := e + r
    0 ≤ m ∧ r < 0 ∧ 0 < k ∧
      k + m / 2 ≤ m ∧ m + k ≤ R + d := by
  rcases hEven with ⟨s, hs⟩
  dsimp only
  have hmLower := Int.ediv_mul_le (e + R / 2)
    (by norm_num : (2 : Int) ≠ 0)
  have hmUpper : e + R / 2 < ((e + R / 2) / 2 + 1) * 2 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  omega

/-- Integer inequalities for the negative-order high-defect branch. -/
private theorem caseIIIHigh_negative_integer_bounds
    (e R d k : Int)
    (hePos : 0 < e)
    (hRlower : -(2 * e) < R) (hRneg : R < 0)
    (hEven : Even R)
    (hdHigh : 6 * e - R < 4 * d)
    (hk : k = e - (2 * e - R) / 4) :
    let r := R / 2
    let m := e + r
    0 ≤ m ∧ r < 0 ∧ 0 < k ∧
      k + m / 2 ≤ m ∧ m + k ≤ R + d := by
  rcases hEven with ⟨s, hs⟩
  dsimp only
  have hRhalf : R / 2 = s := by omega
  have hfloorIdentity :
      (2 * e - R) / 4 = (e + R / 2) / 2 - R / 2 := by
    have hj : (2 * e - R) / 4 = (e - s) / 2 := by
      calc
        (2 * e - R) / 4 = (2 * (e - s)) / (2 * 2) := by
          congr 1 <;> omega
        _ = (e - s) / 2 :=
          Int.mul_ediv_mul_of_pos (e - s) 2 (by omega)
    rw [hj, hRhalf]
    have hdiv : (e - s) / 2 =
        (e + s) / 2 + (-2 * s) / 2 := by
      rw [← Int.add_ediv_of_dvd_right]
      · congr 1
        ring
      · exact ⟨-s, by ring⟩
    rw [hdiv]
    have hcancel : (-2 * s) / 2 = -s := by
      apply Int.ediv_eq_of_eq_mul_left (by omega)
      ring
    rw [hcancel]
    omega
  have hjHalf : (2 * e - R) / 4 = (e - s) / 2 := by
    calc
      (2 * e - R) / 4 = (2 * (e - s)) / (2 * 2) := by
        congr 1 <;> omega
      _ = (e - s) / 2 :=
        Int.mul_ediv_mul_of_pos (e - s) 2 (by omega)
  rw [hfloorIdentity] at hk
  have hjLower := Int.ediv_mul_le (2 * e - R)
    (by norm_num : (4 : Int) ≠ 0)
  have hjUpper : 2 * e - R < ((2 * e - R) / 4 + 1) * 4 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hmLower := Int.ediv_mul_le (e + R / 2)
    (by norm_num : (2 : Int) ≠ 0)
  have hmUpper : e + R / 2 < ((e + R / 2) / 2 + 1) * 2 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hnLower := Int.ediv_mul_le (e - s)
    (by norm_num : (2 : Int) ≠ 0)
  have hnUpper : e - s < ((e - s) / 2 + 1) * 2 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hkHalfFormula : k = e - (e - s) / 2 := by omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · have hdTwice : 3 * e - s < 2 * d := by omega
    have hremainder : e - s - 2 * ((e - s) / 2) ≤ 1 := by omega
    have htargetTwice :
        2 * (2 * e - s - (e - s) / 2) ≤ 2 * d := by
      omega
    have htarget : 2 * e - s - (e - s) / 2 ≤ d := by omega
    omega

/-- Transport the negative modular principal bound from a defect-adapted
shear to an arbitrary admissible shear. -/
theorem spinorNormImage_binaryModel_le_principalUnit_of_negative_bounds
    (a : Kˣ) (c : K) (k : Nat)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hmNonneg : 0 ≤
      (ramificationIndex K : Int) + ordUnit K a / 2)
    (hkPos : 0 < k)
    (hkHalf : (k : Int) +
        ((ramificationIndex K : Int) + ordUnit K a / 2) / 2 ≤
      (ramificationIndex K : Int) + ordUnit K a / 2)
    (hfiniteDepth : beliParameterDefect K a ≠ ⊤ →
      (ramificationIndex K : Int) + ordUnit K a / 2 + (k : Int) ≤
        ordUnit K a + (beliParameterDefectNat K a : Int)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K k : Set (SquareClass K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  let R : Int := ordUnit K a
  let r : Int := R / 2
  let m : Int := (ramificationIndex K : Int) + r
  rcases exists_defectAdaptedShear a ha hEven with
    ⟨c₀, htwo₀, hdiag₀, hcross₀, hsecond₀⟩
  have hc₀Ne : c₀ ≠ 0 := by
    intro hc
    rw [hc, mul_zero, ord_zero] at hcross₀
    exact WithTop.top_ne_coe hcross₀
  let c₀U : Kˣ := Units.mk0 c₀ hc₀Ne
  have hc₀UnitOrder : ordUnit K c₀U = r := by
    apply WithTop.coe_injective
    have hcross := hcross₀
    rw [ord_mul, ← ramificationIndex_spec] at hcross
    have hcField : ord K c₀ =
        (ordUnit K c₀U : WithTop Int) := by
      simpa only [c₀U, Units.val_mk0] using (coe_ordUnit K c₀U).symm
    rw [hcField] at hcross
    change (ordUnit K c₀U : WithTop Int) = (r : WithTop Int)
    dsimp only [r, R]
    norm_cast at hcross ⊢
    omega
  have hc₀Order : ord K c₀ = (r : WithTop Int) := by
    rw [← show (c₀U : K) = c₀ by rfl, ← coe_ordUnit,
      hc₀UnitOrder]
  have hrNeg : r < 0 := by
    dsimp only [r, R]
    rcases hEven with ⟨s, hs⟩
    omega
  have hmDef : m = (ramificationIndex K : Int) + r := rfl
  have hmNonneg' : 0 ≤ m := by
    simpa only [m, r, R] using hmNonneg
  have hkHalf' : (k : Int) + m / 2 ≤ m := by
    simpa only [m, r, R] using hkHalf
  have hdiagDepth :
      c₀ ^ 2 + (a : K) = 0 ∨
        ∃ H : Int,
          ord K (c₀ ^ 2 + (a : K)) = (H : WithTop Int) ∧
            m + (k : Int) ≤ H := by
    rcases hsecond₀ with htop | hfinite
    · exact Or.inl htop.2
    · refine Or.inr ⟨ordUnit K a +
          (beliParameterDefectNat K a : Int), hfinite.2, ?_⟩
      simpa only [m, r, R] using hfiniteDepth hfinite.1
  have hadapted := spinorNormImage_binaryModel_le_principalUnit_modular
    (K := K) a c₀ r m k htwo₀ hdiag₀ hrNeg hmNonneg' hmDef
      hc₀Order hdiagDepth hkPos hkHalf'
  have hsub : c₀ - c ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing a c₀ c
      htwo₀ hdiag₀ htwo hdiag
  rcases binaryModel_isIsometric_of_shear_sub_integral
      a c₀ c hsub with ⟨f⟩
  have hspinor :
      Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c₀)
          (L := binaryModelLattice (K := K)) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel a c)
          (L := binaryModelLattice (K := K)) :=
    Lattice.spinorNormImage_eq_of_isometry f
  intro A hA
  apply hadapted
  rwa [hspinor]

/-- Principal-unit containment in Beli's case III(v) for a negative even
parameter order. -/
theorem spinorNormImage_binaryModel_le_caseIIIMiddle_negative
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hdUpper : 4 * beliParameterDefect K a ≤
      (beliSpinorCaseIIIUpperCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K
        (beliSpinorCaseIIIMiddleExponent K a) : Set (SquareClass K)) := by
  let e : Int := ramificationIndex K
  let R : Int := ordUnit K a
  let d : Nat := (beliParameterDefect K a).toNat
  let k : Nat := beliSpinorCaseIIIMiddleExponent K a
  have hePos : 0 < e := by
    dsimp only [e]
    exact_mod_cast ramificationIndex_pos K
  have hRlower : -(2 * e) ≤ R := by
    simpa only [e, R] using ha.ordUnit_ge_neg_two_mul_e
  have htop : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hdUpper
    simp at hdUpper
  have hdCoe : (d : ℕ∞) = beliParameterDefect K a := by
    dsimp only [d]
    exact ENat.coe_toNat htop
  have hlowNat :
      Int.toNat (2 * (ramificationIndex K : Int) - ordUnit K a) <
        2 * d := by
    have h := hdLower
    unfold beliSpinorCaseIIILowerCutoff at h
    rw [← hdCoe] at h
    norm_cast at h
    omega
  have hlowInt : 2 * e - R < 2 * (d : Int) := by
    have hcast :
        (Int.toNat
          (2 * (ramificationIndex K : Int) - ordUnit K a) : Int) <
            2 * (d : Int) := by exact_mod_cast hlowNat
    have hnonneg :
        0 ≤ 2 * (ramificationIndex K : Int) - ordUnit K a := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    rw [Int.toNat_of_nonneg hnonneg] at hcast
    simpa only [e, R] using hcast
  have huppNat : 4 * d ≤
      Int.toNat (6 * (ramificationIndex K : Int) - ordUnit K a) := by
    have h := hdUpper
    unfold beliSpinorCaseIIIUpperCutoff at h
    rw [← hdCoe] at h
    norm_cast at h
  have huppInt : 4 * (d : Int) ≤ 6 * e - R := by
    have hcast : 4 * (d : Int) ≤
        (Int.toNat
          (6 * (ramificationIndex K : Int) - ordUnit K a) : Int) := by
      exact_mod_cast huppNat
    have hnonneg :
        0 ≤ 6 * (ramificationIndex K : Int) - ordUnit K a := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    rw [Int.toNat_of_nonneg hnonneg] at hcast
    simpa only [e, R] using hcast
  have hdefectNat : beliParameterDefectNat K a = d := by
    unfold beliParameterDefectNat
    rfl
  have hkFormula : k = Int.toNat (R / 2 + (d : Int) - e) := by
    dsimp only [k]
    unfold beliSpinorCaseIIIMiddleExponent
    rw [hdefectNat]
  have hkInsidePos : 0 < R / 2 + (d : Int) - e := by
    have hEven' := hEven
    rcases hEven' with ⟨s, hs⟩
    change R = s + s at hs
    omega
  have hkInt : (k : Int) = R / 2 + (d : Int) - e := by
    rw [hkFormula, Int.toNat_of_nonneg hkInsidePos.le]
  have hbounds := caseIIIMiddle_negative_integer_bounds
    e R (d : Int) (k : Int) hePos hRlower
      (by simpa only [R] using hRneg)
        (by simpa only [R] using hEven) hlowInt huppInt hkInt
  apply spinorNormImage_binaryModel_le_principalUnit_of_negative_bounds
    (K := K) a c k ha hRneg hEven htwo hdiag
  · simpa only [e, R] using hbounds.1
  · exact_mod_cast hbounds.2.2.1
  · simpa only [e, R] using hbounds.2.2.2.1
  · intro _hfinite
    simpa only [e, R, hdefectNat] using hbounds.2.2.2.2

/-- Full forward containment in Beli's case III(v): the principal-unit
bound is intersected with the ambient quadratic-norm group. -/
theorem spinorNormImage_binaryModel_le_caseIIIMiddle_negative_full
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hdUpper : 4 * beliParameterDefect K a ≤
      (beliSpinorCaseIIIUpperCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      ((principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIIMiddleExponent K a) ⊓
        quadraticNormSquareClassSubgroup K (-a)) : Set (SquareClass K)) := by
  have hprincipal :=
    spinorNormImage_binaryModel_le_caseIIIMiddle_negative
      (K := K) a c ha hRneg hEven hdLower hdUpper htwo hdiag
  have hnorm := spinorNormImage_binaryModel_le_quadraticNorm
    (K := K) a c htwo hdiag
  intro A hA
  exact ⟨hprincipal hA, hnorm hA⟩

/-- Principal-unit containment in Beli's case III(vi) for a negative even
parameter order strictly above the endpoint `-2e`. -/
theorem spinorNormImage_binaryModel_le_caseIIIHigh_negative
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRlower : -(2 * (ramificationIndex K : Int)) < ordUnit K a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdHigh : ¬4 * beliParameterDefect K a ≤
      (beliSpinorCaseIIIUpperCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (principalUnitSquareClassSubgroup K
        (beliSpinorCaseIIIHighExponent K a) : Set (SquareClass K)) := by
  let e : Int := ramificationIndex K
  let R : Int := ordUnit K a
  let k : Nat := beliSpinorCaseIIIHighExponent K a
  have hePos : 0 < e := by
    dsimp only [e]
    exact_mod_cast ramificationIndex_pos K
  have hkFormula : k = Int.toNat (e - (2 * e - R) / 4) := by
    dsimp only [k]
    unfold beliSpinorCaseIIIHighExponent
    rfl
  have hquotientLt : (2 * e - R) / 4 < e := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).2
    simpa only [e, R] using (show
      2 * (ramificationIndex K : Int) - ordUnit K a <
        (ramificationIndex K : Int) * 4 by omega)
  have hkInsidePos : 0 < e - (2 * e - R) / 4 := by omega
  have hkInt : (k : Int) = e - (2 * e - R) / 4 := by
    rw [hkFormula, Int.toNat_of_nonneg hkInsidePos.le]
  by_cases htop : beliParameterDefect K a = ⊤
  · have hfakeHigh : 6 * e - R < 4 * (2 * e + 1) := by
      have hlower : -(2 * e) < R := by simpa only [e, R] using hRlower
      omega
    have hbounds := caseIIIHigh_negative_integer_bounds
      e R (2 * e + 1) (k : Int) hePos
        (by simpa only [e, R] using hRlower)
          (by simpa only [R] using hRneg)
            (by simpa only [R] using hEven) hfakeHigh hkInt
    apply spinorNormImage_binaryModel_le_principalUnit_of_negative_bounds
      (K := K) a c k ha hRneg hEven htwo hdiag
    · simpa only [e, R] using hbounds.1
    · exact_mod_cast hbounds.2.2.1
    · simpa only [e, R] using hbounds.2.2.2.1
    · intro hfinite
      exact (hfinite htop).elim
  · let d : Nat := (beliParameterDefect K a).toNat
    have hdCoe : (d : ℕ∞) = beliParameterDefect K a := by
      dsimp only [d]
      exact ENat.coe_toNat htop
    have hhighNat :
        Int.toNat
            (6 * (ramificationIndex K : Int) - ordUnit K a) <
          4 * d := by
      have h := hdHigh
      unfold beliSpinorCaseIIIUpperCutoff at h
      rw [← hdCoe] at h
      norm_cast at h
      omega
    have hhighInt : 6 * e - R < 4 * (d : Int) := by
      have hcast :
          (Int.toNat
            (6 * (ramificationIndex K : Int) - ordUnit K a) : Int) <
              4 * (d : Int) := by exact_mod_cast hhighNat
      have hnonneg :
          0 ≤ 6 * (ramificationIndex K : Int) - ordUnit K a := by
        have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
        omega
      rw [Int.toNat_of_nonneg hnonneg] at hcast
      simpa only [e, R] using hcast
    have hdefectNat : beliParameterDefectNat K a = d := by
      unfold beliParameterDefectNat
      rfl
    have hbounds := caseIIIHigh_negative_integer_bounds
      e R (d : Int) (k : Int) hePos
        (by simpa only [e, R] using hRlower)
          (by simpa only [R] using hRneg)
            (by simpa only [R] using hEven) hhighInt hkInt
    apply spinorNormImage_binaryModel_le_principalUnit_of_negative_bounds
      (K := K) a c k ha hRneg hEven htwo hdiag
    · simpa only [e, R] using hbounds.1
    · exact_mod_cast hbounds.2.2.1
    · simpa only [e, R] using hbounds.2.2.2.1
    · intro _hfinite
      simpa only [e, R, hdefectNat] using hbounds.2.2.2.2

/-- At the lower admissible endpoint, infinite parameter defect forces the
exceptional refined class `-1/4`. -/
theorem unitSquareClass_eq_negativeQuarter_of_order_eq_neg_two_e_of_defect_top
    (a : Kˣ)
    (hR : ordUnit K a = -(2 * (ramificationIndex K : Int)))
    (htop : beliParameterDefect K a = ⊤) :
    unitSquareClass K a = unitSquareClass K (negativeQuarterUnit K) := by
  let R : Int := ordUnit K a
  let epsilon : Kˣ := normalizedUnitPart K a
  have hUnit : IsValuationUnit K (epsilon : K) :=
    normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * epsilon = a := by
    simpa only [R, epsilon] using uniformizerPower_mul_normalizedUnitPart K a
  have hnegA : IsSquare (-a) :=
    (quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).1
      (by simpa only [beliParameterDefect] using htop)
  have hEvenR : Even R := by
    refine ⟨-(ramificationIndex K : Int), ?_⟩
    dsimp only [R]
    rw [hR]
    omega
  have hpowerSquare : IsSquare (uniformizerPowerUnit K R) := by
    rcases hEvenR with ⟨s, hs⟩
    refine ⟨uniformizerPowerUnit K s, ?_⟩
    unfold uniformizerPowerUnit
    rw [← zpow_add, hs]
  have hnegFactor : uniformizerPowerUnit K R * (-epsilon) = -a := by
    rw [← hfactor]
    simp
  have hnegEpsilon : IsSquare (-epsilon) := by
    have heq : -epsilon = (-a) / uniformizerPowerUnit K R := by
      calc
        -epsilon =
            (uniformizerPowerUnit K R * (-epsilon)) /
              uniformizerPowerUnit K R := by
                apply Units.ext
                simp only [Units.val_neg, Units.val_div_eq_div_val,
                  Units.val_mul]
                field_simp [Units.ne_zero (uniformizerPowerUnit K R)]
                congr 1
                simpa [uniformizerPowerUnit] using
                  (div_self
                    (zpow_ne_zero R (uniformizer_ne_zero K))).symm
        _ = (-a) / uniformizerPowerUnit K R := by rw [hnegFactor]
    rw [heq]
    exact hnegA.div hpowerSquare
  rw [← hfactor]
  exact unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
    (K := K) R epsilon hUnit (by simpa only [R] using hR) hnegEpsilon

/-- The defect-top endpoint is the already proved hyperbolic exceptional
case. -/
theorem spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_endpoint
    (a : Kˣ) (c : K)
    (hR : ordUnit K a = -(2 * (ramificationIndex K : Int)))
    (htop : beliParameterDefect K a = ⊤)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  let b := binaryExactModelBONG a c htwo hdiag
  have hclass : b.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
    unfold BONG.binaryUnitSquareClass
    rw [binaryExactModelBONG_binaryParameter]
    exact unitSquareClass_eq_negativeQuarter_of_order_eq_neg_two_e_of_defect_top
      (K := K) a hR htop
  have h :=
    b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_negativeQuarter
      hclass
  simpa only [b, binaryExactModelBONG_binaryParameter] using h

/-- Complete forward containment for every negative, even, non-low binary
parameter.  The endpoint, middle-defect, and high-defect branches are
dispatched to the preceding unconditional calculations. -/
theorem spinorNormImage_binaryModel_le_beliSpinorGroupRepresentative_negative_even_nonlow
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRneg : ordUnit K a < 0)
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) ⊆
      (beliSpinorGroupRepresentative K a : Set (SquareClass K)) := by
  have hRlower := ha.ordUnit_ge_neg_two_mul_e
  rcases hRlower.eq_or_lt with hEndpoint | hInterior
  · have hR : ordUnit K a =
        -(2 * (ramificationIndex K : Int)) := hEndpoint.symm
    have htop : beliParameterDefect K a = ⊤ := by
      by_contra hfinite
      have hnotSquare : ¬IsSquare (-a) := by
        intro hsquare
        exact hfinite
          ((quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).2 hsquare)
      have hbound := quadraticDefect_le_two_mul_e_of_not_isSquare
        (K := K) hnotSquare
      change beliParameterDefect K a ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) at hbound
      have hboundNat := hbound
      rw [← ENat.coe_toNat hfinite] at hboundNat
      norm_cast at hboundNat
      have hcontra := hdLower
      unfold beliSpinorCaseIIILowerCutoff at hcontra
      rw [hR, ← ENat.coe_toNat hfinite] at hcontra
      norm_cast at hcontra
      have hcutoff : Int.toNat
          (((2 * ramificationIndex K : Nat) : Int) -
            -((2 * ramificationIndex K : Nat) : Int)) =
          4 * ramificationIndex K := by
        apply Int.ofNat_injective
        calc
          (Int.toNat
              (((2 * ramificationIndex K : Nat) : Int) -
                -((2 * ramificationIndex K : Nat) : Int)) : Int) =
              ((2 * ramificationIndex K : Nat) : Int) -
                -((2 * ramificationIndex K : Nat) : Int) :=
            Int.toNat_of_nonneg (by
              have hnonneg :
                  0 ≤ ((2 * ramificationIndex K : Nat) : Int) := by
                positivity
              omega)
          _ = ((4 * ramificationIndex K : Nat) : Int) := by
            norm_cast
            omega
      rw [hcutoff] at hcontra
      omega
    have heq :=
      spinorNormImage_binaryModel_eq_beliSpinorGroupRepresentative_endpoint
        (K := K) a c hR htop htwo hdiag
    rw [heq]
  · have hquarter : unitSquareClass K a ≠
        unitSquareClass K (negativeQuarterUnit K) := by
      intro hclass
      have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
      rw [ordUnit_negativeQuarterUnit] at horder
      omega
    have hRupper : ordUnit K a ≤
        2 * (ramificationIndex K : Int) := by
      have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    by_cases hdUpper : 4 * beliParameterDefect K a ≤
        (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)
    · have hupper :=
        spinorNormImage_binaryModel_le_caseIIIMiddle_negative_full
          (K := K) a c ha hRneg hEven hdLower hdUpper htwo hdiag
      rw [beliSpinorGroupRepresentative_caseIII_middle
        K a ha hquarter hRupper hdLower hdUpper]
      exact hupper
    · have hupper :=
        spinorNormImage_binaryModel_le_caseIIIHigh_negative
          (K := K) a c ha hInterior hRneg hEven hdUpper htwo hdiag
      rw [beliSpinorGroupRepresentative_caseIII_high
        K a ha hquarter hRupper hdLower hdUpper]
      exact hupper

end BONG

end Bong
