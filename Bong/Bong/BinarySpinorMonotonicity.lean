/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization
import Bong.Bong.BinaryIntegralSquare
import Bong.Bong.BinarySpinorGroup

/-!
# Monotonicity of Beli's binary spinor group

This file combines the integral-square sublattice construction with Lemma 3.7
to prove Beli (2003), Lemma 3.8 first for an arbitrary integral square and then
in the paper's order-and-parity formulation.
-/

namespace Bong

open Dyadic

/-- If `R ≤ R'` and `R' ≡ R (mod 2)`, then `R' = R + 2k` for a natural
number `k`. -/
theorem exists_nat_eq_add_two_mul_of_le_modEq_two
    {R R' : Int} (hle : R ≤ R') (hmod : R' ≡ R [ZMOD 2]) :
    ∃ k : Nat, R' = R + 2 * (k : Int) := by
  rcases (Int.modEq_iff_dvd.mp hmod.symm) with ⟨k, hk⟩
  have hkNonneg : 0 ≤ k := by omega
  refine ⟨k.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hkNonneg]
  omega

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Dyadic

/-- A nonnegative power of the selected uniformizer is integral. -/
theorem uniformizerPowerUnit_nat_mem_integerRing (k : Nat) :
    (uniformizerPowerUnit K (k : Int) : K) ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  rw [IsIntegral, ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  exact_mod_cast Nat.zero_le k

/-- Multiplying `πᴿ ε` by the square of `πᵏ` shifts the exponent by `2k`. -/
theorem uniformizerParameter_mul_square
    (ε : Kˣ) (R : Int) (k : Nat) :
    uniformizerPowerUnit K R * ε *
        uniformizerPowerUnit K (k : Int) ^ 2 =
      uniformizerPowerUnit K (R + 2 * (k : Int)) * ε := by
  unfold uniformizerPowerUnit
  have hpow : (uniformizerUnit K ^ (k : Int)) ^ 2 =
      uniformizerUnit K ^ (2 * (k : Int)) := by
    calc
      (uniformizerUnit K ^ (k : Int)) ^ 2 =
          uniformizerUnit K ^ (k : Int) *
            uniformizerUnit K ^ (k : Int) := by rw [pow_two]
      _ = uniformizerUnit K ^ ((k : Int) + (k : Int)) := by
        rw [← zpow_add]
      _ = uniformizerUnit K ^ (2 * (k : Int)) := by
        congr 1
        omega
  rw [hpow]
  calc
    uniformizerUnit K ^ R * ε *
          uniformizerUnit K ^ (2 * (k : Int)) =
        (uniformizerUnit K ^ R *
          uniformizerUnit K ^ (2 * (k : Int))) * ε := by
      ac_rfl
    _ = uniformizerUnit K ^ (R + 2 * (k : Int)) * ε := by
      rw [← zpow_add]

/-- The order of `πᴿ ε` is `R` when `ε` is a valuation unit. -/
theorem ordUnit_uniformizerPower_mul_valuationUnit
    (ε : Kˣ) (hε : IsValuationUnit K (ε : K)) (R : Int) :
    ordUnit K (uniformizerPowerUnit K R * ε) = R := by
  rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hε, add_zero]

end Dyadic

namespace BONG

variable [BinarySpinorLocalLaws.{u, v} K]

/-- Integral-square form of Lemma 3.8, starting from a concrete binary BONG. -/
theorem beliSpinorGroup_mul_integral_square_le
    (b : BONG V q L 2) (s : Kˣ)
    (hs : (s : K) ∈ IntegerRing K) :
    beliSpinorGroup K
        (unitSquareClass K (b.binaryParameter * s ^ 2)) ≤
      beliSpinorGroup K b.binaryUnitSquareClass := by
  let M := b.binaryIntegralSquareSubLattice s hs
  let c : BONG V q M 2 := b.binaryIntegralSquareSubBONG s hs
  have hsubset :=
    b.spinorNormImage_binaryIntegralSquareSubLattice_subset s hs
  have hc := c.spinorNormImage_eq_beliSpinorGroup
  have hb := b.spinorNormImage_eq_beliSpinorGroup
  rw [hc, hb] at hsubset
  have hclass : c.binaryUnitSquareClass =
      unitSquareClass K (b.binaryParameter * s ^ 2) := by
    unfold binaryUnitSquareClass
    rw [show c.binaryParameter = b.binaryParameter * s ^ 2 by
      exact b.binaryIntegralSquareSubBONG_binaryParameter s hs]
  intro x hx
  apply hsubset
  rwa [hclass]

end BONG

namespace BONG

variable [BinarySpinorLocalLaws.{u, u} K]

/-- Integral-square form of Lemma 3.8 for any admissible scalar parameter. -/
theorem beliSpinorGroup_mul_integral_square_le_of_admissible
    {a : Kˣ} (ha : IsBinaryParameterAdmissible a)
    (s : Kˣ) (hs : (s : K) ∈ IntegerRing K) :
    beliSpinorGroup K (unitSquareClass K (a * s ^ 2)) ≤
      beliSpinorGroup K (unitSquareClass K a) := by
  rcases ha.exists_exactModelBONG with
    ⟨c, htwo, hdiag, _, _, hparameter⟩
  let b := binaryExactModelBONG a c htwo hdiag
  have hle := b.beliSpinorGroup_mul_integral_square_le s hs
  have hbParameter : b.binaryParameter = a := hparameter
  have hbClass : b.binaryUnitSquareClass = unitSquareClass K a := by
    unfold binaryUnitSquareClass
    rw [hbParameter]
  rw [hbParameter, hbClass] at hle
  exact hle

/-- Beli (2003), Lemma 3.8 in its order-and-parity formulation. -/
theorem beliSpinorGroup_uniformizer_order_mono
    (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    {R R' : Int}
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hle : R ≤ R') (hmod : R' ≡ R [ZMOD 2]) :
    IsBinaryParameterAdmissible (uniformizerPowerUnit K R' * ε) ∧
      ordUnit K (uniformizerPowerUnit K R * ε) = R ∧
      ordUnit K (uniformizerPowerUnit K R' * ε) = R' ∧
      beliSpinorGroup K
          (unitSquareClass K (uniformizerPowerUnit K R' * ε)) ≤
        beliSpinorGroup K
          (unitSquareClass K (uniformizerPowerUnit K R * ε)) := by
  rcases exists_nat_eq_add_two_mul_of_le_modEq_two hle hmod with
    ⟨k, hR'⟩
  let s : Kˣ := uniformizerPowerUnit K (k : Int)
  have hs : (s : K) ∈ IntegerRing K :=
    uniformizerPowerUnit_nat_mem_integerRing k
  have hparameter :
      (uniformizerPowerUnit K R * ε) * s ^ 2 =
        uniformizerPowerUnit K R' * ε := by
    dsimp [s]
    rw [uniformizerParameter_mul_square, hR']
  have ha' := ha.mul_integral_square hs
  rw [hparameter] at ha'
  have hgroup :=
    beliSpinorGroup_mul_integral_square_le_of_admissible ha s hs
  rw [hparameter] at hgroup
  exact ⟨ha',
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R,
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R', hgroup⟩

end BONG

end Bong
