/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryPrimitiveCoordinates

/-!
# Order alternatives for primitive diagonal binary reflections

This is the elementary reflection-order calculation cited as Hsia (1975),
Proposition 3.2 in Xu's binary spinor-norm proofs.  A primitive integral
reflection in `X² + aY²` either has first-coordinate order at most `e`, or
has unit second coordinate and first-coordinate order at least `R-e`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Hsia's order alternatives for a primitive integral reflection in a
diagonal binary lattice. -/
theorem primitive_integralReflection_binaryDiagonal_order_cases
    (a : Kˣ) {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)))
    (hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz) :
    (∃ hx0 : z 0 ≠ 0,
        ordUnit K (Units.mk0 (z 0) hx0) ≤
          (ramificationIndex K : Int)) ∨
      (IsValuationUnit K (z 1) ∧
        (z 0 = 0 ∨ ∃ hx0 : z 0 ≠ 0,
          ordUnit K (Units.mk0 (z 0) hx0) ≤
              (ramificationIndex K : Int) ∨
            ordUnit K a - (ramificationIndex K : Int) ≤
              ordUnit K (Units.mk0 (z 0) hx0))) := by
  have hzCoords := (mem_binaryModelLattice_iff z).1 hzMem
  have hprimitive :=
    (primitive_binaryModelLattice_iff_coordinate_unit z hzMem).1
      hzPrimitive
  have hcoefficients :=
    (isIntegralReflection_binaryDiagonal_iff_of_primitive
      a hz hzMem hzPrimitive).1 hzIntegral
  have hqFormula :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        z 0 ^ 2 + (a : K) * z 1 ^ 2 := by
    simp [QuadraticSpace.binaryModel_quadratic_apply]
  have hq0 : z 0 ^ 2 + (a : K) * z 1 ^ 2 ≠ 0 := by
    rw [← hqFormula]
    exact hz
  rcases hprimitive with hxUnit | hyUnit
  · have hx0 : z 0 ≠ 0 := by
      intro hx
      rw [hx, IsValuationUnit, ord_zero] at hxUnit
      exact WithTop.top_ne_zero hxUnit
    left
    refine ⟨hx0, ?_⟩
    have hxOrder : ordUnit K (Units.mk0 (z 0) hx0) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K
        (Units.mk0 (z 0) hx0)).1 (by simpa using hxUnit)
    rw [hxOrder]
    positivity
  · right
    refine ⟨hyUnit, ?_⟩
    by_cases hx0 : z 0 = 0
    · exact Or.inl hx0
    right
    let xu : Kˣ := Units.mk0 (z 0) hx0
    let qU : Kˣ := Units.mk0
      (z 0 ^ 2 + (a : K) * z 1 ^ 2) hq0
    have hxOrdTop : ord K (z 0) =
        (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hqOrdTop : ord K (z 0 ^ 2 + (a : K) * z 1 ^ 2) =
        (ordUnit K qU : WithTop Int) := by
      simpa [qU] using (coe_ordUnit K qU).symm
    by_cases hxSmall : ordUnit K xu ≤ (ramificationIndex K : Int)
    · exact ⟨hx0, Or.inl (by simpa [xu] using hxSmall)⟩
    have hxLarge : (ramificationIndex K : Int) < ordUnit K xu :=
      lt_of_not_ge hxSmall
    let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
    let coefficient : Kˣ := twoU * xu * qU⁻¹
    have hcoefficientMem : (coefficient : K) ∈ IntegerRing K := by
      have hfirst := hcoefficients.1
      rw [hqFormula] at hfirst
      simpa only [coefficient, twoU, xu, qU,
        Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val,
        div_eq_mul_inv, mul_assoc] using hfirst
    have hcoefficientNonneg : 0 ≤ ordUnit K coefficient :=
      Lattice.ordUnit_nonneg_of_mem_integerRing coefficient
        hcoefficientMem
    have htwoOrder :
        ordUnit K twoU = (ramificationIndex K : Int) := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, ramificationIndex_spec]
      rfl
    have hcoefficientOrder :
        ordUnit K coefficient =
          (ramificationIndex K : Int) + ordUnit K xu -
            ordUnit K qU := by
      simp only [coefficient, ordUnit_mul, ordUnit_inv, htwoOrder]
      omega
    have hqUpper :
        ordUnit K qU ≤
          (ramificationIndex K : Int) + ordUnit K xu := by
      rw [hcoefficientOrder] at hcoefficientNonneg
      omega
    refine ⟨hx0, Or.inr ?_⟩
    change ordUnit K a - (ramificationIndex K : Int) ≤
      ordUnit K xu
    by_contra hnot
    have hxBelow : ordUnit K xu <
        ordUnit K a - (ramificationIndex K : Int) :=
      lt_of_not_ge hnot
    rcases lt_trichotomy (2 * ordUnit K xu) (ordUnit K a) with
      hlt | heq | hgt
    · have hterms :
          ord K (z 0 ^ 2) < ord K ((a : K) * z 1 ^ 2) := by
        calc
          ord K (z 0 ^ 2) =
              ((2 * ordUnit K xu : Int) : WithTop Int) := by
            rw [ord_pow, hxOrdTop]
            norm_cast
          _ < (ordUnit K a : WithTop Int) := by
            exact_mod_cast hlt
          _ = ord K ((a : K) * z 1 ^ 2) := by
            rw [ord_mul, ord_pow, hyUnit, ← coe_ordUnit K a]
            simp
      have hsum := (ord K).map_add_eq_of_lt_left hterms
      have hqOrder : ordUnit K qU = 2 * ordUnit K xu := by
        apply WithTop.coe_injective
        rw [← hqOrdTop, hsum, ord_pow, hxOrdTop]
        norm_cast
      rw [hqOrder] at hqUpper
      omega
    · have hminimum :=
          min_ord_le_ord_add K (z 0 ^ 2) ((a : K) * z 1 ^ 2)
      have hqLower : ordUnit K a ≤ ordUnit K qU := by
        apply WithTop.coe_le_coe.mp
        calc
          (ordUnit K a : WithTop Int) =
              min (ord K (z 0 ^ 2))
                (ord K ((a : K) * z 1 ^ 2)) := by
            rw [ord_pow, ord_mul, ord_pow, hyUnit,
              hxOrdTop, ← coe_ordUnit K a]
            norm_cast
            simp [heq]
          _ ≤ ord K (z 0 ^ 2 + (a : K) * z 1 ^ 2) := hminimum
          _ = (ordUnit K qU : WithTop Int) := hqOrdTop
      omega
    · have hterms :
          ord K ((a : K) * z 1 ^ 2) < ord K (z 0 ^ 2) := by
        calc
          ord K ((a : K) * z 1 ^ 2) =
              (ordUnit K a : WithTop Int) := by
            rw [ord_mul, ord_pow, hyUnit, ← coe_ordUnit K a]
            simp
          _ < ((2 * ordUnit K xu : Int) : WithTop Int) := by
            exact_mod_cast hgt
          _ = ord K (z 0 ^ 2) := by
            rw [ord_pow, hxOrdTop]
            norm_cast
      have hsum := (ord K).map_add_eq_of_lt_right hterms
      have hqOrder : ordUnit K qU = ordUnit K a := by
        apply WithTop.coe_injective
        rw [← hqOrdTop, hsum, ord_mul, ord_pow, hyUnit,
          ← coe_ordUnit K a]
        simp
      rw [hqOrder] at hqUpper
      omega

end BONG

end Bong
