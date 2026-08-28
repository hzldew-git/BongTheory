/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalMiddleSpinorUpper
import Bong.Bong.BinaryDiagonalHighSpinor
import Bong.Bong.BinaryAdmissibility
import Bong.Bong.ResidueDefectProductProof
import Bong.Dyadic.UnitDefectClassification

/-!
# The odd middle-range binary spinor formula

This file proves the odd-order branch of Xu (1993), Proposition 2.2.  The
first step replaces simultaneous membership in a principal-unit square-class
group and a quadratic norm square-class group by one representative which has
both properties.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A square class in the intersection of a principal-unit filtration and a
quadratic norm group has a single representative satisfying both conditions.
This removes the harmless square factor between the two representatives. -/
theorem exists_principalUnit_quadraticNorm_representative
    (a : Kˣ) (k : Nat) {A : SquareClass K}
    (hA : A ∈ principalUnitSquareClassSubgroup K k ⊓
      quadraticNormSquareClassSubgroup K (-a)) :
    ∃ u : Kˣ,
      u ∈ principalUnitSubgroup K k ∧
      IsQuadraticNorm K (-a) u ∧
      squareClass K u = A := by
  rcases hA.1 with ⟨u, huPrincipal, huClass⟩
  rcases hA.2 with ⟨v, hvNorm, hvClass⟩
  have huvClass : squareClass K u = squareClass K v :=
    huClass.trans hvClass.symm
  change QuotientGroup.mk' (Subgroup.square Kˣ) u =
    QuotientGroup.mk' (Subgroup.square Kˣ) v at huvClass
  rw [QuotientGroup.mk'_eq_mk'] at huvClass
  rcases huvClass with ⟨s, hsSquare, husv⟩
  change IsSquare s at hsSquare
  have hsNorm : s ∈ quadraticNormGroup K (-a) :=
    isQuadraticNorm_of_isSquare_right K hsSquare
  have huNorm : u ∈ quadraticNormGroup K (-a) := by
    have hproduct := (quadraticNormGroup K (-a)).mul_mem hvNorm
      ((quadraticNormGroup K (-a)).inv_mem hsNorm)
    have heq : v * s⁻¹ = u := by
      rw [← husv]
      simp
    rwa [heq] at hproduct
  exact ⟨u, huPrincipal, huNorm, huClass⟩

/-- In an odd positive-order diagonal norm representation of a valuation
unit, the first coordinate is a unit.  If the second coordinate is nonzero,
its diagonal summand has strictly positive order. -/
private theorem first_coordinate_unit_of_odd_norm_representation
    (a u : Kˣ)
    (hROdd : Odd (ordUnit K a))
    (huUnit : IsValuationUnit K (u : K))
    {x y : K} (hxy : x ^ 2 + (a : K) * y ^ 2 = (u : K)) :
    IsValuationUnit K x ∧
      (y = 0 ∨ ∃ hy0 : y ≠ 0,
        0 < ordUnit K a +
          2 * ordUnit K (Units.mk0 y hy0)) := by
  have hx0 : x ≠ 0 := by
    intro hx
    have hy0 : y ≠ 0 := by
      intro hy
      rw [hx, hy] at hxy
      have huZero : (u : K) = 0 := by simpa using hxy.symm
      exact Units.ne_zero u huZero
    let yu : Kˣ := Units.mk0 y hy0
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    have horder : ordUnit K a + 2 * ordUnit K yu = 0 := by
      apply WithTop.coe_injective
      calc
        ((ordUnit K a + 2 * ordUnit K yu : Int) : WithTop Int) =
            ord K ((a : K) * y ^ 2) := by
          rw [ord_mul, ord_pow, hyOrdTop, ← coe_ordUnit K a]
          norm_cast
        _ = ord K (u : K) := by rw [← hxy, hx]; simp
        _ = 0 := huUnit
    rcases hROdd with ⟨r, hr⟩
    omega
  let xu : Kˣ := Units.mk0 x hx0
  by_cases hy0 : y = 0
  · have hxu : xu ^ 2 = u := by
      apply Units.ext
      simpa [xu, hy0] using hxy
    have hxOrder : ordUnit K xu = 0 := by
      have horder := congrArg (ordUnit K) hxu
      have huOrder : ordUnit K u = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K u).1 huUnit
      rw [ordUnit_pow, huOrder] at horder
      omega
    refine ⟨?_, Or.inl hy0⟩
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxOrder
  · let yu : Kˣ := Units.mk0 y hy0
    have hxOrdTop : ord K x = (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
      simpa [yu] using (coe_ordUnit K yu).symm
    have htermNe : 2 * ordUnit K xu ≠
        ordUnit K a + 2 * ordUnit K yu := by
      intro heq
      rcases hROdd with ⟨r, hr⟩
      omega
    rcases lt_or_gt_of_ne htermNe with hlt | hgt
    · have hterms : ord K (x ^ 2) < ord K ((a : K) * y ^ 2) := by
        calc
          ord K (x ^ 2) =
              ((2 * ordUnit K xu : Int) : WithTop Int) := by
            rw [ord_pow, hxOrdTop]
            norm_cast
          _ < ((ordUnit K a + 2 * ordUnit K yu : Int) :
              WithTop Int) := by exact_mod_cast hlt
          _ = ord K ((a : K) * y ^ 2) := by
            rw [ord_mul, ord_pow, hyOrdTop, ← coe_ordUnit K a]
            norm_cast
      have hsum := (ord K).map_add_eq_of_lt_left hterms
      have hxOrder : ordUnit K xu = 0 := by
        have hzero : 2 * ordUnit K xu = 0 := by
          apply WithTop.coe_injective
          calc
            ((2 * ordUnit K xu : Int) : WithTop Int) =
                ord K (x ^ 2) := by
              rw [ord_pow, hxOrdTop]
              norm_cast
            _ = ord K (x ^ 2 + (a : K) * y ^ 2) := hsum.symm
            _ = ord K (u : K) := by rw [hxy]
            _ = 0 := huUnit
        omega
      refine ⟨?_, Or.inr ⟨hy0, ?_⟩⟩
      · simpa [xu] using
          (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxOrder
      · change 0 < ordUnit K a + 2 * ordUnit K yu
        omega
    · have hterms : ord K ((a : K) * y ^ 2) < ord K (x ^ 2) := by
        calc
          ord K ((a : K) * y ^ 2) =
              ((ordUnit K a + 2 * ordUnit K yu : Int) :
                WithTop Int) := by
            rw [ord_mul, ord_pow, hyOrdTop, ← coe_ordUnit K a]
            norm_cast
          _ < ((2 * ordUnit K xu : Int) : WithTop Int) := by
            exact_mod_cast hgt
          _ = ord K (x ^ 2) := by
            rw [ord_pow, hxOrdTop]
            norm_cast
      have hsum := (ord K).map_add_eq_of_lt_right hterms
      have hzero : ordUnit K a + 2 * ordUnit K yu = 0 := by
        apply WithTop.coe_injective
        calc
          ((ordUnit K a + 2 * ordUnit K yu : Int) : WithTop Int) =
              ord K ((a : K) * y ^ 2) := by
            rw [ord_mul, ord_pow, hyOrdTop, ← coe_ordUnit K a]
            norm_cast
          _ = ord K (x ^ 2 + (a : K) * y ^ 2) := hsum.symm
          _ = ord K (u : K) := by rw [hxy]
          _ = 0 := huUnit
      rcases hROdd with ⟨r, hr⟩
      omega

/-- An actual principal-unit representative has quadratic defect at least its
filtration depth. -/
private theorem principalUnit_defect_lowerBound
    (u : Kˣ) (k : Nat) (hu : u ∈ principalUnitSubgroup K k) :
    (k : ℕ∞) ≤ quadraticDefect K u := by
  apply natCast_le_quadraticDefect K
  refine ⟨1, ?_⟩
  have herror : ((k : Int) : WithTop Int) ≤ ord K ((u : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (k : Int) ((u : K) - 1)).1 hu.2
  have hfield : 1 - (1 : K) ^ 2 / (u : K) =
      ((u : K) - 1) / (u : K) := by
    field_simp [Units.ne_zero u]
  rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv, hu.1]
  simpa using herror

/-- In the odd middle range, a negative second-coordinate order cannot have
absolute value greater than `e`; otherwise the represented principal unit
would simultaneously have defect at least `R-2e` and exact smaller odd
defect `R+2 ord(y)`. -/
private theorem neg_second_coordinate_order_le_ramification
    (a u : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a))
    (huPrincipal : u ∈ principalUnitSubgroup K
      (binaryMiddleSpinorDepth (K := K) a))
    {x y : K} (hxy : x ^ 2 + (a : K) * y ^ 2 = (u : K))
    (hxUnit : IsValuationUnit K x)
    (hy0 : y ≠ 0)
    (hyTermPos : 0 < ordUnit K a +
      2 * ordUnit K (Units.mk0 y hy0))
    (hyNeg : ordUnit K (Units.mk0 y hy0) < 0) :
    -ordUnit K (Units.mk0 y hy0) ≤
      (ramificationIndex K : Int) := by
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, IsValuationUnit, ord_zero] at hxUnit
    exact WithTop.top_ne_zero hxUnit
  let xu : Kˣ := Units.mk0 x hx0
  let yu : Kˣ := Units.mk0 y hy0
  have hxOrder : ordUnit K xu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K xu).1
      (by simpa [xu] using hxUnit)
  have hyTermPos' : 0 < ordUnit K a + 2 * ordUnit K yu := by
    simpa [yu] using hyTermPos
  have hyNeg' : ordUnit K yu < 0 := by simpa [yu] using hyNeg
  by_contra hnot
  have hyBeyond : (ramificationIndex K : Int) < -ordUnit K yu :=
    lt_of_not_ge hnot
  let depthInt : Int := ordUnit K a + 2 * ordUnit K yu
  let d : Nat := Int.toNat depthInt
  have hdCast : (d : Int) = depthInt := by
    dsimp only [d]
    rw [Int.toNat_of_nonneg hyTermPos'.le]
  have hdPos : 0 < d := by
    have hdPosInt : (0 : Int) < (d : Int) := by rw [hdCast]; exact hyTermPos'
    exact_mod_cast hdPosInt
  have hdOddInt : Odd depthInt := by
    rcases hROdd with ⟨r, hr⟩
    refine ⟨r + ordUnit K yu, ?_⟩
    dsimp only [depthInt]
    omega
  have hdOdd : Odd d := by
    rcases hdOddInt with ⟨r, hr⟩
    have hrNonneg : 0 ≤ r := by
      rw [← hdCast] at hr
      omega
    refine ⟨Int.toNat r, ?_⟩
    have hrCast : (Int.toNat r : Int) = r :=
      Int.toNat_of_nonneg hrNonneg
    have hdEq : (d : Int) = 2 * r + 1 := by
      rw [hdCast]
      exact hr
    have hdEq' : (d : Int) = 2 * (Int.toNat r : Int) + 1 := by
      rwa [hrCast]
    exact_mod_cast hdEq'
  have hdLt : d < 2 * ramificationIndex K := by
    have hdLtInt : depthInt < 2 * (ramificationIndex K : Int) := by
      dsimp only [depthInt]
      omega
    have : (d : Int) < 2 * (ramificationIndex K : Int) := by
      rwa [hdCast]
    exact_mod_cast this
  let tU : Kˣ := a * (yu * xu⁻¹) ^ 2
  have htOrder : ordUnit K tU = depthInt := by
    dsimp only [tU, depthInt]
    simp only [ordUnit_mul, ordUnit_pow, ordUnit_inv, hxOrder]
    omega
  have hfactor : (u : K) = (xu : K) ^ 2 * (1 + (tU : K)) := by
    rw [← hxy]
    simp only [tU, xu, yu, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp [hx0]
  have honePlus : 1 + (tU : K) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact Units.ne_zero u hfactor
  let v : Kˣ := Units.mk0 (1 + (tU : K)) honePlus
  have hvField : (v : K) = 1 + (tU : K) := rfl
  have htFieldOrder : ord K (tU : K) =
      ((d : Int) : WithTop Int) := by
    rw [← coe_ordUnit, htOrder, hdCast]
  have hvDefect : quadraticDefect K v = (d : ℕ∞) :=
    quadraticDefect_eq_of_principal_exact_odd v (tU : K) d
      hvField htFieldOrder hdPos hdOdd hdLt
  have hunitFactor : xu ^ 2 * v = u := by
    apply Units.ext
    simpa only [v, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0] using hfactor.symm
  have huDefect : quadraticDefect K u = (d : ℕ∞) := by
    rw [← hunitFactor, mul_comm, quadraticDefect_mul_square, hvDefect]
  have hlower := principalUnit_defect_lowerBound u
    (binaryMiddleSpinorDepth (K := K) a) huPrincipal
  rw [huDefect] at hlower
  have hdepthLt : d < binaryMiddleSpinorDepth (K := K) a := by
    have hdepthCast := binaryMiddleSpinorDepth_cast (K := K) a hR
    have hltInt : (d : Int) <
        (binaryMiddleSpinorDepth (K := K) a : Int) := by
      rw [hdepthCast, hdCast]
      dsimp only [depthInt]
      omega
    exact_mod_cast hltInt
  have hnot : ¬(binaryMiddleSpinorDepth (K := K) a : ℕ∞) ≤
      (d : ℕ∞) := by
    exact_mod_cast (not_le_of_gt hdepthLt)
  exact hnot hlower

/-- A scaled norm representation gives an integral reflection as soon as the
two scaled coordinates are integral and primitive and the two reflection
coefficient orders are nonnegative. -/
private theorem scaled_norm_representation_class_mem_spinor
    (a u s : Kˣ)
    (haIntegral : (a : K) ∈ IntegerRing K)
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxUnit : IsValuationUnit K x)
    (huUnit : IsValuationUnit K (u : K))
    (hxy : x ^ 2 + (a : K) * y ^ 2 = (u : K))
    (hsNonneg : 0 ≤ ordUnit K s)
    (hyScaledNonneg : 0 ≤ ordUnit K s +
      ordUnit K (Units.mk0 y hy0))
    (hprimitiveOrder : ordUnit K s = 0 ∨
      ordUnit K s + ordUnit K (Units.mk0 y hy0) = 0)
    (hfirstBound : ordUnit K s ≤ (ramificationIndex K : Int))
    (hsecondBound : 0 ≤ (ramificationIndex K : Int) + ordUnit K a +
      ordUnit K (Units.mk0 y hy0) - ordUnit K s)
    {A : SquareClass K} (huClass : squareClass K u = A) :
    A ∈ Lattice.spinorNormImage
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) := by
  let xu : Kˣ := Units.mk0 x hx0
  let yu : Kˣ := Units.mk0 y hy0
  have hxOrder : ordUnit K xu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K xu).1
      (by simpa [xu] using hxUnit)
  have huOrder : ordUnit K u = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).1 huUnit
  have hyOrdTop : ord K y = (ordUnit K yu : WithTop Int) := by
    simpa [yu] using (coe_ordUnit K yu).symm
  let z : Fin 2 → K := ![(s : K) * x, (s : K) * y]
  have hz0 : z 0 = (s : K) * x := by simp [z]
  have hz1 : z 1 = (s : K) * y := by simp [z]
  have hvalue :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        (s : K) ^ 2 * (u : K) := by
    simp only [QuadraticSpace.binaryModel_quadratic_apply, z,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, zero_mul, zero_add]
    rw [← hxy]
    ring
  have hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z := by
    rw [QuadraticSpace.IsAnisotropic, hvalue]
    exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero s)) (Units.ne_zero u)
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((s : K) * x)
      rw [ord_mul, ← coe_ordUnit K s, hxUnit]
      have : (0 : Int) ≤ ordUnit K s + 0 := by omega
      exact_mod_cast this
    · apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K ((s : K) * y)
      rw [ord_mul, ← coe_ordUnit K s, hyOrdTop]
      exact_mod_cast hyScaledNonneg
  have hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)) := by
    apply (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).2
    rcases hprimitiveOrder with hsZero | hyZero
    · left
      rw [IsValuationUnit]
      change ord K ((s : K) * x) = 0
      rw [ord_mul, ← coe_ordUnit K s, hxUnit, hsZero]
      simp
    · right
      rw [IsValuationUnit]
      change ord K ((s : K) * y) = 0
      rw [ord_mul, ← coe_ordUnit K s, hyOrdTop]
      exact_mod_cast hyZero
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  let qU : Kˣ := s ^ 2 * u
  have hqOrder : ordUnit K qU = 2 * ordUnit K s := by
    simp only [qU, ordUnit_mul, ordUnit_pow, huOrder]
    omega
  let firstCoefficient : Kˣ := twoU * (s * xu) * qU⁻¹
  have hfirstOrder : ordUnit K firstCoefficient =
      (ramificationIndex K : Int) - ordUnit K s := by
    simp only [firstCoefficient, ordUnit_mul, ordUnit_inv, htwoOrder,
      hxOrder, hqOrder]
    omega
  have hfirstMem : (firstCoefficient : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (firstCoefficient : K)
    rw [← coe_ordUnit]
    exact_mod_cast (show 0 ≤ ordUnit K firstCoefficient by
      rw [hfirstOrder]
      omega)
  let secondCoefficient : Kˣ := twoU * a * (s * yu) * qU⁻¹
  have hsecondOrder : ordUnit K secondCoefficient =
      (ramificationIndex K : Int) + ordUnit K a + ordUnit K yu -
        ordUnit K s := by
    simp only [secondCoefficient, ordUnit_mul, ordUnit_inv, htwoOrder,
      hqOrder]
    omega
  have hsecondMem : (secondCoefficient : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (secondCoefficient : K)
    rw [← coe_ordUnit]
    exact_mod_cast (show 0 ≤ ordUnit K secondCoefficient by
      rw [hsecondOrder]
      simpa [yu] using hsecondBound)
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag]
  refine ⟨z, hz, hzMem, hzPrimitive, ?_, ?_, ?_⟩
  · have hcoefficient :
        2 * z 0 /
            (QuadraticSpace.binaryModel a 0).quadratic z =
          (firstCoefficient : K) := by
      simp only [z, firstCoefficient, twoU, qU, xu,
        Matrix.cons_val_zero, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_mk0, Units.val_pow_eq_pow_val]
      rw [hvalue]
      field_simp [Units.ne_zero s, Units.ne_zero u]
    rw [zero_mul, add_zero, hcoefficient]
    exact hfirstMem
  · have hcoefficient :
        2 * ((a : K) * z 1) /
            (QuadraticSpace.binaryModel a 0).quadratic z =
          (secondCoefficient : K) := by
      rw [hz1, hvalue]
      simp only [secondCoefficient, twoU, qU, yu,
        Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero s, Units.ne_zero u]
    norm_num only [zero_mul, zero_pow, zero_add, add_zero]
    rw [hcoefficient]
    exact hsecondMem
  · have hqUnit :
        Units.mk0 ((QuadraticSpace.binaryModel a 0).quadratic z) hz = qU := by
      apply Units.ext
      simpa only [qU, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_mk0] using hvalue
    rw [hqUnit]
    calc
      squareClass K qU = squareClass K (u * s ^ 2) := by
        apply congrArg (squareClass K)
        simp [qU, mul_comm]
      _ = squareClass K u := squareClass_mul_square K u s
      _ = A := huClass

/-- The second standard basis vector realizes the parameter square class in
the proper spinor image of every integral diagonal binary model. -/
theorem squareClass_parameter_mem_spinorNormImage_binaryDiagonal
    (a : Kˣ) (haIntegral : (a : K) ∈ IntegerRing K) :
    squareClass K a ∈ Lattice.spinorNormImageSubgroup
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) := by
  change squareClass K a ∈ Lattice.spinorNormImage
    (q := QuadraticSpace.binaryModel a 0)
    (L := binaryModelLattice (K := K))
  have htwo : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiag : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  rw [spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    a 0 htwo hdiag]
  let e₁ : Fin 2 → K := QuadraticSpace.binaryModelSecond
  have he₁ : (QuadraticSpace.binaryModel a 0).IsAnisotropic e₁ := by
    simp [e₁, QuadraticSpace.IsAnisotropic]
  have he₁Mem : e₁ ∈ binaryModelLattice (K := K) :=
    binaryModelSecond_mem a 0
  have he₁Primitive : e₁ ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)) := by
    apply (primitive_binaryModelLattice_iff_coordinate_unit e₁ he₁Mem).2
    right
    simp [e₁, QuadraticSpace.binaryModelSecond, IsValuationUnit]
  have htwoIntegral : (2 : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    exact (ord_two_pos K).le
  have he₁Zero : e₁ 0 = 0 := by
    simp [e₁, QuadraticSpace.binaryModelSecond]
  have he₁One : e₁ 1 = 1 := by
    simp [e₁, QuadraticSpace.binaryModelSecond]
  have hvalue :
      (QuadraticSpace.binaryModel a 0).quadratic e₁ = (a : K) := by
    simp [e₁]
  refine ⟨e₁, he₁, he₁Mem, he₁Primitive, ?_, ?_, ?_⟩
  · rw [he₁Zero, he₁One, hvalue]
    simp
  · rw [he₁Zero, he₁One, hvalue]
    simpa [Units.ne_zero a] using htwoIntegral
  · have hunit : Units.mk0
          ((QuadraticSpace.binaryModel a 0).quadratic e₁) he₁ = a := by
      apply Units.ext
      simpa only [Units.val_mk0] using hvalue
    rw [hunit]

/-- Reverse containment in Xu (1993), Proposition 2.2(i): every odd
middle-range principal-unit norm class is realized by an integral reflection.
-/
theorem principalUnit_inf_norm_le_spinorNormImage_of_middle_odd
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a)) :
    principalUnitSquareClassSubgroup K
          (binaryMiddleSpinorDepth (K := K) a) ⊓
        quadraticNormSquareClassSubgroup K (-a) ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) := by
  intro A hA
  rcases exists_principalUnit_quadraticNorm_representative a
      (binaryMiddleSpinorDepth (K := K) a) hA with
    ⟨u, huPrincipal, huNorm, huClass⟩
  have huUnit : IsValuationUnit K (u : K) := huPrincipal.1
  rcases huNorm with ⟨x, y, hxyNorm⟩
  have hxy : x ^ 2 + (a : K) * y ^ 2 = (u : K) := by
    simpa using hxyNorm
  rcases first_coordinate_unit_of_odd_norm_representation
      a u hROdd huUnit hxy with ⟨hxUnit, hyCases⟩
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, IsValuationUnit, ord_zero] at hxUnit
    exact WithTop.top_ne_zero hxUnit
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have haOrderNonneg : 0 ≤ ordUnit K a := by omega
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change (0 : WithTop Int) ≤ ord K (a : K)
    rw [← coe_ordUnit]
    exact_mod_cast haOrderNonneg
  rcases hyCases with hyZero | ⟨hy0, hyTermPos⟩
  · have huSquare : IsSquare u := by
      let xu : Kˣ := Units.mk0 x hx0
      refine ⟨xu, ?_⟩
      apply Units.ext
      simpa [xu, hyZero, pow_two] using hxy.symm
    have hAOne : A = 1 :=
      huClass.symm.trans (squareClass_eq_one_of_isSquare u huSquare)
    rw [hAOne]
    exact (Lattice.spinorNormImageSubgroup
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K))).one_mem
  · let yu : Kˣ := Units.mk0 y hy0
    have hyTermPos' : 0 < ordUnit K a + 2 * ordUnit K yu := by
      simpa [yu] using hyTermPos
    have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    by_cases hyNonneg : 0 ≤ ordUnit K yu
    · change A ∈ Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K))
      apply scaled_norm_representation_class_mem_spinor
        a u 1 haIntegral hx0 hy0 hxUnit huUnit hxy
      · rw [honeOrder]
      · rw [honeOrder]
        simpa [yu] using hyNonneg
      · exact Or.inl honeOrder
      · rw [honeOrder]
        exact heNonneg
      · rw [honeOrder]
        simpa [yu] using
          (show 0 ≤ (ramificationIndex K : Int) + ordUnit K a +
              ordUnit K yu by omega)
      · exact huClass
    · have hyNeg : ordUnit K yu < 0 := lt_of_not_ge hyNonneg
      have hyBound : -ordUnit K yu ≤
          (ramificationIndex K : Int) := by
        apply neg_second_coordinate_order_le_ramification
          a u hR hRhigh hROdd huPrincipal hxy hxUnit hy0
        · simpa [yu] using hyTermPos'
        · simpa [yu] using hyNeg
      let s : Kˣ := uniformizerPowerUnit K (-(ordUnit K yu))
      have hsOrder : ordUnit K s = -(ordUnit K yu) := by
        exact ordUnit_uniformizerPowerUnit (K := K) _
      change A ∈ Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K))
      apply scaled_norm_representation_class_mem_spinor
        a u s haIntegral hx0 hy0 hxUnit huUnit hxy
      · rw [hsOrder]
        omega
      · rw [hsOrder]
        change 0 ≤ -(ordUnit K yu) + ordUnit K yu
        omega
      · exact Or.inr (by rw [hsOrder]; change
          -(ordUnit K yu) + ordUnit K yu = 0; omega)
      · rwa [hsOrder]
      · rw [hsOrder]
        change 0 ≤ (ramificationIndex K : Int) + ordUnit K a +
          ordUnit K yu - (-(ordUnit K yu))
        omega
      · exact huClass

/-- Xu (1993), Proposition 2.2(i), in subgroup form. -/
theorem spinorNormImage_binaryDiagonal_eq_middle_odd
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a)) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) =
      ↑(cyclicSquareClassSubgroup K a ⊔
        (principalUnitSquareClassSubgroup K
            (binaryMiddleSpinorDepth (K := K) a) ⊓
          quadraticNormSquareClassSubgroup K (-a))) := by
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
  have haMem : squareClass K a ∈ S := by
    exact squareClass_parameter_mem_spinorNormImage_binaryDiagonal
      a haIntegral
  have hcyclic : cyclicSquareClassSubgroup K a ≤ S := by
    rw [cyclicSquareClassSubgroup, Subgroup.zpowers_le]
    exact haMem
  have hinf :
      principalUnitSquareClassSubgroup K
            (binaryMiddleSpinorDepth (K := K) a) ⊓
          quadraticNormSquareClassSubgroup K (-a) ≤ S := by
    exact principalUnit_inf_norm_le_spinorNormImage_of_middle_odd
      a hR hRhigh hROdd
  have hreverse : cyclicSquareClassSubgroup K a ⊔
        (principalUnitSquareClassSubgroup K
            (binaryMiddleSpinorDepth (K := K) a) ⊓
          quadraticNormSquareClassSubgroup K (-a)) ≤ S :=
    sup_le hcyclic hinf
  ext A
  constructor
  · intro hA
    exact spinorNormImage_binaryDiagonal_le_middleUpper a hR hA
  · intro hA
    change A ∈ S
    exact hreverse hA

/-- For odd parameter order, the defect branch of Beli's case II is the low
branch and its exponent is exactly `R - 2e`. -/
theorem beliSpinorCaseIILowExponent_eq_middleDepth_of_odd
    (a : Kˣ) (hROdd : Odd (ordUnit K a)) :
    beliSpinorCaseIILowExponent K a =
      binaryMiddleSpinorDepth (K := K) a := by
  have hnegOdd : Odd (ordUnit K (-a)) := by
    simpa only [ordUnit_neg] using hROdd
  have hdefect : quadraticDefect K (-a) = 0 :=
    quadraticDefect_eq_zero_of_odd_ordUnit (-a) hnegOdd
  simp [beliSpinorCaseIILowExponent, binaryMiddleSpinorDepth,
    beliParameterDefectNat, beliParameterDefect, hdefect]

/-- The exact odd middle-range formula is Beli (2003), Definition 4(II)(ii)
on the chosen representative. -/
theorem spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_middle_odd
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd (ordUnit K a)) :
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
  have hnegOdd : Odd (ordUnit K (-a)) := by
    simpa only [ordUnit_neg] using hROdd
  have hdefect : beliParameterDefect K a = 0 := by
    unfold beliParameterDefect
    exact quadraticDefect_eq_zero_of_odd_ordUnit (-a) hnegOdd
  have hlow : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞) := by
    rw [hdefect]
    simp
  have hexponent :=
    beliSpinorCaseIILowExponent_eq_middleDepth_of_odd (K := K) a hROdd
  rw [spinorNormImage_binaryDiagonal_eq_middle_odd a hR hRhigh hROdd]
  symm
  rw [beliSpinorGroupRepresentative_caseII_low K a haAdmissible
    hquarter hR hRhigh hlow, hexponent]

/-- Proposition 2.2(i) transported from the diagonal model to an arbitrary
binary BONG. -/
theorem spinorNormImage_eq_middle_odd
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hR : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hRhigh : b.binaryOrderGap ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      ↑(cyclicSquareClassSubgroup K b.binaryParameter ⊔
        (principalUnitSquareClassSubgroup K
            (binaryMiddleSpinorDepth (K := K) b.binaryParameter) ⊓
          quadraticNormSquareClassSubgroup K (-b.binaryParameter))) := by
  have hnonneg : 0 ≤ b.binaryOrderGap := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  rw [b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hnonneg]
  apply spinorNormImage_binaryDiagonal_eq_middle_odd
  · change 2 * (ramificationIndex K : Int) < b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change b.binaryParameterOrder ≤ 4 * (ramificationIndex K : Int)
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change Odd b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]

/-- The odd middle-range BONG formula closes the corresponding branch of
Beli (2003), Lemma 3.7 without a `BinarySpinorLocalLaws` hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_middle_odd
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hR : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hRhigh : b.binaryOrderGap ≤ 4 * (ramificationIndex K : Int))
    (hROdd : Odd b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  have hnonneg : 0 ≤ b.binaryOrderGap := by
    have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  rw [b.spinorNormImage_eq_diagonal_of_binaryOrderGap_nonneg hnonneg]
  apply spinorNormImage_binaryDiagonal_eq_beliSpinorGroupRepresentative_of_middle_odd
  · change 2 * (ramificationIndex K : Int) < b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change b.binaryParameterOrder ≤ 4 * (ramificationIndex K : Int)
    rwa [b.binaryParameterOrder_eq_orderGap]
  · change Odd b.binaryParameterOrder
    rwa [b.binaryParameterOrder_eq_orderGap]

end BONG

end Bong
