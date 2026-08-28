/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalReflectionOrders
import Bong.Bong.BinarySpinorGroupFormula

/-!
# The upper spinor bound in the range `R > 2e`

The order alternatives for primitive integral reflections imply the first
closed-form containment in Xu (1993), Proposition 2.2.  At depth
`R - 2e`, every reflection value is either a principal-unit square class or
the parameter class times one, and every value belongs to the quadratic norm
group of `-a`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The positive depth `R - 2e` in Xu's middle-range calculation. -/
noncomputable def binaryMiddleSpinorDepth (a : Kˣ) : Nat :=
  Int.toNat (ordUnit K a - 2 * (ramificationIndex K : Int))

theorem binaryMiddleSpinorDepth_cast
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    (binaryMiddleSpinorDepth (K := K) a : Int) =
      ordUnit K a - 2 * (ramificationIndex K : Int) := by
  rw [binaryMiddleSpinorDepth, Int.toNat_of_nonneg]
  omega

theorem binaryMiddleSpinorDepth_pos
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    0 < binaryMiddleSpinorDepth (K := K) a := by
  have hcast := binaryMiddleSpinorDepth_cast (K := K) a hR
  have : (0 : Int) < binaryMiddleSpinorDepth (K := K) a := by
    rw [hcast]
    omega
  exact_mod_cast this

/-- Normalizing a value by a first coordinate of order at most `e` gives a
principal unit at depth `R - 2e`. -/
private theorem exists_first_normalized_principalUnit
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    {x y : K} (hx0 : x ≠ 0)
    (hxOrder : ordUnit K (Units.mk0 x hx0) ≤
      (ramificationIndex K : Int))
    (hyIntegral : y ∈ IntegerRing K)
    (hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0) :
    ∃ u : Kˣ,
      u ∈ principalUnitSubgroup K (binaryMiddleSpinorDepth (K := K) a) ∧
        squareClass K
            (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) =
          squareClass K u := by
  let xu : Kˣ := Units.mk0 x hx0
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  have hxOrder' : ordUnit K xu ≤ (ramificationIndex K : Int) := by
    simpa [xu] using hxOrder
  by_cases hy0 : y = 0
  · refine ⟨1, ?_, ?_⟩
    · exact (principalUnitSubgroup K
        (binaryMiddleSpinorDepth (K := K) a)).one_mem
    · have hqU : qU = xu ^ 2 := by
        apply Units.ext
        simp [qU, xu, hy0]
      change squareClass K qU = squareClass K (1 : Kˣ)
      rw [hqU]
      simpa [pow_two] using squareClass_mul_square K (1 : Kˣ) xu
  let yu : Kˣ := Units.mk0 y hy0
  have hyOrder : 0 ≤ ordUnit K yu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing yu
      (by simpa [yu] using hyIntegral)
  let uK : K := 1 + (a : K) * (y / x) ^ 2
  have hfactor :
      x ^ 2 + (a : K) * y ^ 2 = x ^ 2 * uK := by
    dsimp [uK]
    field_simp [hx0]
  have hu0 : uK ≠ 0 := by
    intro hu
    apply hq0
    rw [hfactor, hu, mul_zero]
  let u : Kˣ := Units.mk0 uK hu0
  let error : Kˣ := a * (yu / xu) ^ 2
  have herrorOrder :
      ordUnit K error = ordUnit K a +
        2 * ordUnit K yu - 2 * ordUnit K xu := by
    simp [error, div_eq_mul_inv]
    ring
  have huSub : (u : K) - 1 = (error : K) := by
    simp only [u, uK, error, xu, yu, Units.val_mk0,
      Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val]
    ring
  have hdepthOrder :
      (binaryMiddleSpinorDepth (K := K) a : Int) ≤
        ordUnit K error := by
    rw [binaryMiddleSpinorDepth_cast (K := K) a hR, herrorOrder]
    omega
  have herrorPositive : (0 : WithTop Int) < ord K (error : K) := by
    rw [← coe_ordUnit]
    exact_mod_cast (lt_of_lt_of_le
      (show (0 : Int) < binaryMiddleSpinorDepth (K := K) a by
        exact_mod_cast binaryMiddleSpinorDepth_pos (K := K) a hR)
      hdepthOrder)
  have huUnit : IsValuationUnit K (u : K) := by
    rw [IsValuationUnit]
    have honeLt : ord K (1 : K) < ord K (error : K) := by
      simpa only [ord_one] using herrorPositive
    have hsum := (ord K).map_add_eq_of_lt_left honeLt
    have huValue : (u : K) = 1 + (error : K) := by
      have := huSub
      linear_combination this
    rw [huValue, hsum, ord_one]
  have huPrincipal : u ∈ principalUnitSubgroup K
      (binaryMiddleSpinorDepth (K := K) a) := by
    rw [mem_principalUnitSubgroup_iff]
    refine ⟨huUnit, (Lattice.mem_powerIdeal_iff
      (K := K) (binaryMiddleSpinorDepth (K := K) a : Int)
      ((u : K) - 1)).2 ?_⟩
    rw [huSub, ← coe_ordUnit]
    exact_mod_cast hdepthOrder
  refine ⟨u, huPrincipal, ?_⟩
  have hqU : qU = u * xu ^ 2 := by
    apply Units.ext
    simpa only [qU, u, xu, Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val, mul_comm] using hfactor
  change squareClass K qU = squareClass K u
  rw [hqU]
  exact squareClass_mul_square K u xu

/-- Normalizing a value by `a` and a unit second coordinate, when the first
coordinate has order at least `R-e`, gives the same principal-unit depth. -/
private theorem exists_second_normalized_principalUnit
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hyUnit : IsValuationUnit K y)
    (hxOrder : ordUnit K a - (ramificationIndex K : Int) ≤
      ordUnit K (Units.mk0 x hx0))
    (hq0 : x ^ 2 + (a : K) * y ^ 2 ≠ 0) :
    ∃ u : Kˣ,
      u ∈ principalUnitSubgroup K (binaryMiddleSpinorDepth (K := K) a) ∧
        squareClass K
            (Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0) =
          squareClass K a * squareClass K u := by
  let xu : Kˣ := Units.mk0 x hx0
  let yu : Kˣ := Units.mk0 y hy0
  have hyOrder : ordUnit K yu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K yu).1
      (by simpa [yu] using hyUnit)
  let qU : Kˣ := Units.mk0 (x ^ 2 + (a : K) * y ^ 2) hq0
  let uK : K := 1 + (a : K)⁻¹ * (x / y) ^ 2
  have hfactor :
      x ^ 2 + (a : K) * y ^ 2 = (a : K) * y ^ 2 * uK := by
    dsimp [uK]
    field_simp [hy0, Units.ne_zero a]
    ring
  have hu0 : uK ≠ 0 := by
    intro hu
    apply hq0
    rw [hfactor, hu, mul_zero]
  let u : Kˣ := Units.mk0 uK hu0
  let error : Kˣ := a⁻¹ * (xu / yu) ^ 2
  have herrorOrder :
      ordUnit K error = -ordUnit K a +
        2 * ordUnit K xu - 2 * ordUnit K yu := by
    simp [error, div_eq_mul_inv]
    ring
  have huSub : (u : K) - 1 = (error : K) := by
    simp only [u, uK, error, xu, yu, Units.val_mk0,
      Units.val_inv_eq_inv_val, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
    ring
  have hdepthOrder :
      (binaryMiddleSpinorDepth (K := K) a : Int) ≤
        ordUnit K error := by
    have hxOrder' : ordUnit K a - (ramificationIndex K : Int) ≤
        ordUnit K xu := by simpa [xu] using hxOrder
    rw [binaryMiddleSpinorDepth_cast (K := K) a hR,
      herrorOrder, hyOrder]
    omega
  have herrorPositive : (0 : WithTop Int) < ord K (error : K) := by
    rw [← coe_ordUnit]
    exact_mod_cast (lt_of_lt_of_le
      (show (0 : Int) < binaryMiddleSpinorDepth (K := K) a by
        exact_mod_cast binaryMiddleSpinorDepth_pos (K := K) a hR)
      hdepthOrder)
  have huUnit : IsValuationUnit K (u : K) := by
    rw [IsValuationUnit]
    have honeLt : ord K (1 : K) < ord K (error : K) := by
      simpa only [ord_one] using herrorPositive
    have hsum := (ord K).map_add_eq_of_lt_left honeLt
    have huValue : (u : K) = 1 + (error : K) := by
      have := huSub
      linear_combination this
    rw [huValue, hsum, ord_one]
  have huPrincipal : u ∈ principalUnitSubgroup K
      (binaryMiddleSpinorDepth (K := K) a) := by
    rw [mem_principalUnitSubgroup_iff]
    refine ⟨huUnit, (Lattice.mem_powerIdeal_iff
      (K := K) (binaryMiddleSpinorDepth (K := K) a : Int)
      ((u : K) - 1)).2 ?_⟩
    rw [huSub, ← coe_ordUnit]
    exact_mod_cast hdepthOrder
  refine ⟨u, huPrincipal, ?_⟩
  have hqU : qU = (a * u) * yu ^ 2 := by
    apply Units.ext
    have hfactor' := hfactor
    simp only [qU, u, yu, Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val]
    rw [hfactor']
    ring
  change squareClass K qU = squareClass K a * squareClass K u
  rw [hqU, squareClass_mul_square]
  rfl

/-- Every nonzero diagonal value is a norm from the quadratic algebra with
parameter `-a`. -/
private theorem squareClass_diagonalValue_mem_quadraticNorm
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

/-- The parameter class itself belongs to the same quadratic norm group. -/
private theorem squareClass_parameter_mem_quadraticNorm (a : Kˣ) :
    squareClass K a ∈ quadraticNormSquareClassSubgroup K (-a) := by
  refine ⟨a, ?_, rfl⟩
  change IsQuadraticNorm K (-a) a
  refine ⟨0, 1, ?_⟩
  simp

/-- Xu's first middle-range containment: every proper integral spinor class
is generated by the parameter and a depth-`R-2e` principal unit which is
also a norm from `K(√(-a))`. -/
theorem spinorNormImage_binaryDiagonal_le_middleUpper
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) ⊆
      (cyclicSquareClassSubgroup K a ⊔
        (principalUnitSquareClassSubgroup K
            (binaryMiddleSpinorDepth (K := K) a) ⊓
          quadraticNormSquareClassSubgroup K (-a)) :
        Subgroup (SquareClass K)) := by
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have haOrderNonneg : 0 ≤ ordUnit K a := by omega
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
  have hqNorm := squareClass_diagonalValue_mem_quadraticNorm a hq0
  have haNorm := squareClass_parameter_mem_quadraticNorm a
  let U := principalUnitSquareClassSubgroup K
    (binaryMiddleSpinorDepth (K := K) a)
  let N := quadraticNormSquareClassSubgroup K (-a)
  let T := cyclicSquareClassSubgroup K a ⊔ (U ⊓ N)
  have hqNorm' : squareClass K
      (Units.mk0 ((QuadraticSpace.binaryModel a 0).quadratic z) hz) ∈ N := by
    simpa only [N, hqFormula] using hqNorm
  have haNorm' : squareClass K a ∈ N := by simpa [N] using haNorm
  have hcases :=
    primitive_integralReflection_binaryDiagonal_order_cases
      a hz hzMem hzPrimitive hzIntegral
  change A ∈ T
  rcases hcases with hsmall | ⟨hyUnit, hxCases⟩
  · rcases hsmall with ⟨hx0, hxOrder⟩
    obtain ⟨u, huPrincipal, hnormalized⟩ :=
      exists_first_normalized_principalUnit a hR hx0 hxOrder
        (mem_binaryModelLattice_iff z |>.1 hzMem 1) hq0
    have huU : squareClass K u ∈ U := by
      exact ⟨u, huPrincipal, rfl⟩
    have huN : squareClass K u ∈ N := by
      rw [← hnormalized]
      simpa only [hqFormula] using hqNorm'
    rw [← hclass]
    have hnormalized' :
        squareClass K
            (Units.mk0
              ((QuadraticSpace.binaryModel a 0).quadratic z) hz) =
          squareClass K u := by
      simpa only [hqFormula] using hnormalized
    rw [hnormalized']
    exact (le_sup_right : U ⊓ N ≤ T) ⟨huU, huN⟩
  · rcases hxCases with hxZero | ⟨hx0, hxSmall | hxHigh⟩
    · let yu : Kˣ := Units.mk0 (z 1) (by
        intro hy
        rw [hy, IsValuationUnit, ord_zero] at hyUnit
        exact WithTop.top_ne_zero hyUnit)
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
    · obtain ⟨u, huPrincipal, hnormalized⟩ :=
        exists_first_normalized_principalUnit a hR hx0 hxSmall
          (mem_binaryModelLattice_iff z |>.1 hzMem 1) hq0
      have huU : squareClass K u ∈ U := ⟨u, huPrincipal, rfl⟩
      have huN : squareClass K u ∈ N := by
        rw [← hnormalized]
        simpa only [hqFormula] using hqNorm'
      rw [← hclass]
      have hnormalized' :
          squareClass K
              (Units.mk0
                ((QuadraticSpace.binaryModel a 0).quadratic z) hz) =
            squareClass K u := by
        simpa only [hqFormula] using hnormalized
      rw [hnormalized']
      exact (le_sup_right : U ⊓ N ≤ T) ⟨huU, huN⟩
    · have hy0 : z 1 ≠ 0 := by
        intro hy
        rw [hy, IsValuationUnit, ord_zero] at hyUnit
        exact WithTop.top_ne_zero hyUnit
      obtain ⟨u, huPrincipal, hnormalized⟩ :=
        exists_second_normalized_principalUnit a hR hx0 hy0
          hyUnit hxHigh hq0
      have huU : squareClass K u ∈ U := ⟨u, huPrincipal, rfl⟩
      have huN : squareClass K u ∈ N := by
        have hquotientNorm := N.mul_mem hqNorm' (N.inv_mem haNorm')
        have hnormalized' :
            squareClass K
                (Units.mk0
                  ((QuadraticSpace.binaryModel a 0).quadratic z) hz) =
              squareClass K a * squareClass K u := by
          simpa only [hqFormula] using hnormalized
        rw [hnormalized'] at hquotientNorm
        simpa [mul_assoc, mul_comm, mul_left_comm] using hquotientNorm
      have haT : squareClass K a ∈ T :=
        (le_sup_left : cyclicSquareClassSubgroup K a ≤ T)
          (Subgroup.mem_zpowers _)
      have huT : squareClass K u ∈ T :=
        (le_sup_right : U ⊓ N ≤ T) ⟨huU, huN⟩
      rw [← hclass]
      have hnormalized' :
          squareClass K
              (Units.mk0
                ((QuadraticSpace.binaryModel a 0).quadratic z) hz) =
            squareClass K a * squareClass K u := by
        simpa only [hqFormula] using hnormalized
      rw [hnormalized']
      exact T.mul_mem haT huT

end BONG

end Bong
