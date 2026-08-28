/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointStandardModel
import Bong.Bong.BeliLemma317
import Bong.Lattice.ScaledHyperbolicMaximal

/-!
# The hyperbolic binary endpoint

The standard binary model with parameter `-1/4` and shear `1/2` has
quadratic polynomial

`u * (x₀² + x₀x₁)`.

The integral change of coordinates

`(x₀, x₁) ↦ (x₀, ε * (x₀ + x₁))`

identifies its standard lattice with a uniformizer-scaled hyperbolic plane;
here `ε` is the valuation-unit part of `u / 2`.  This gives a concrete
lattice theorem, not only an ambient Witt-space statement.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The integral coordinate change from the standard `-1/4` endpoint model
to a hyperbolic plane. -/
noncomputable def negativeQuarterHyperbolicLinearEquiv (ε : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x 0, (ε : K) * (x 0 + x 1)]
  invFun y := ![y 0, ((ε⁻¹ : Kˣ) : K) * y 1 - y 0]
  left_inv x := by
    funext i
    fin_cases i
    · rfl
    · simp [Units.ne_zero]
  right_inv y := by
    funext i
    fin_cases i
    · rfl
    · simp [Units.ne_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem negativeQuarterHyperbolicLinearEquiv_apply_zero
    (ε : Kˣ) (x : Fin 2 → K) :
    negativeQuarterHyperbolicLinearEquiv ε x 0 = x 0 :=
  rfl

@[simp]
theorem negativeQuarterHyperbolicLinearEquiv_apply_one
    (ε : Kˣ) (x : Fin 2 → K) :
    negativeQuarterHyperbolicLinearEquiv ε x 1 =
      (ε : K) * (x 0 + x 1) :=
  rfl

/-- The fixed `-1/4` endpoint model is integrally isometric to the
hyperbolic plane at the exact scale `ord(a) - e`. -/
theorem standardEndpointModel_negativeQuarter_isIsometric_hyperbolicPlane
    (a : Kˣ) :
    Lattice.IsIsometric
      (QuadraticSpace.rescaleUnit a
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K) (standardEndpointShear (K := K))))
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K
          (ordUnit K a - ramificationIndex K)))
      (binaryModelLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let s : Kˣ := a * two⁻¹
  let R : Int := ordUnit K a - ramificationIndex K
  let ε : Kˣ := normalizedUnitPart K s
  have hε : IsValuationUnit K (ε : K) :=
    normalizedUnitPart_isValuationUnit K s
  have hεInv : IsValuationUnit K ((ε⁻¹ : Kˣ) : K) := by
    change ord K ((ε⁻¹ : Kˣ) : K) = 0
    rw [Units.val_inv_eq_inv_val, AddValuation.map_inv, hε]
    simp
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (2 : K) =
      (((ramificationIndex K : Nat) : Int) : WithTop Int)
    exact (ramificationIndex_spec K).symm
  have hsOrder : ordUnit K s = R := by
    dsimp [s, R]
    rw [ordUnit_mul, ordUnit_inv, htwoOrder]
    omega
  have hfactor : uniformizerPowerUnit K R * ε = s := by
    rw [← hsOrder]
    exact uniformizerPower_mul_normalizedUnitPart K s
  refine ⟨{
    toLinearEquiv := negativeQuarterHyperbolicLinearEquiv ε
    map_bilin := ?_
    map_mem := ?_
  }⟩
  · intro x y
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [negativeQuarterHyperbolicLinearEquiv_apply_zero,
      negativeQuarterHyperbolicLinearEquiv_apply_one,
      QuadraticSpace.rescaleUnit_bilin_apply]
    rw [QuadraticSpace.binaryModel, Matrix.toBilin'_apply]
    simp only [Fin.sum_univ_two,
      QuadraticSpace.binaryModelMatrix_zero_zero,
      QuadraticSpace.binaryModelMatrix_zero_one,
      QuadraticSpace.binaryModelMatrix_one_zero,
      QuadraticSpace.binaryModelMatrix_one_one]
    have hfactorK :
        (uniformizerPowerUnit K R : K) * (ε : K) = (s : K) :=
      congrArg Units.val hfactor
    have hs : (s : K) * 2 = (a : K) := by
      dsimp [s, two]
      norm_num
      field_simp
    simp only [standardEndpointShear, negativeQuarterUnit]
    have hnegativeQuarter :
        ((Units.mk0 (-(4 : K)⁻¹) (by norm_num)) : K) = -(4 : K)⁻¹ :=
      rfl
    have hdiag : (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0 := by
      norm_num [show (4 : K) = 2 * 2 by norm_num]
    rw [hnegativeQuarter, hdiag]
    calc
      (uniformizerPowerUnit K R : K) *
          (x 0 * ((ε : K) * (y 0 + y 1)) +
            (ε : K) * (x 0 + x 1) * y 0) =
          ((uniformizerPowerUnit K R : K) * (ε : K)) *
            (2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0) := by ring
      _ = (s : K) *
            (2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0) := by
        rw [hfactorK]
      _ = _ := by
        rw [← hs]
        field_simp
        ring
  · intro x
    rw [binaryModelLattice, Lattice.hyperbolicPlaneLattice,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp only [Pi.basisFun_repr]
    change (∀ i, x i ∈ IntegerRing K) ↔
      ∀ i, negativeQuarterHyperbolicLinearEquiv ε x i ∈ IntegerRing K
    have hεInt : (ε : K) ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change 0 ≤ ord K (ε : K)
      rw [hε]
    have hεInvInt : ((ε⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change 0 ≤ ord K ((ε⁻¹ : Kˣ) : K)
      rw [hεInv]
    constructor
    · intro hx i
      fin_cases i
      · exact hx 0
      · exact (IntegerRing K).mul_mem _ _ hεInt
          ((IntegerRing K).add_mem _ _ (hx 0) (hx 1))
    · intro hy i
      fin_cases i
      · simpa using hy 0
      · have hzero : x 0 ∈ IntegerRing K := by
          simpa using hy 0
        have hone := hy 1
        change (ε : K) * (x 0 + x 1) ∈ IntegerRing K at hone
        have hsum : x 0 + x 1 ∈ IntegerRing K := by
          have := (IntegerRing K).mul_mem _ _ hεInvInt hone
          simpa [Units.ne_zero] using this
        simpa [add_sub_cancel_left] using
          (IntegerRing K).sub_mem hsum hzero

/-- Predicate-valued wrapper for the exact endpoint calculation. -/
theorem standardEndpointModel_negativeQuarter_isScaledHyperbolicLattice
    (a : Kˣ) :
    Lattice.IsScaledHyperbolicLattice
      (QuadraticSpace.rescaleUnit a
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K) (standardEndpointShear (K := K))))
      (binaryModelLattice (K := K)) :=
  ⟨ordUnit K a - ramificationIndex K,
    standardEndpointModel_negativeQuarter_isIsometric_hyperbolicPlane a⟩

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Exact-scale form of the binary endpoint theorem. -/
theorem isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
    (b : BONG V q L 2)
    (hclass : b.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K)) :
    Lattice.IsIsometric q
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K
          (b.order 0 - ramificationIndex K)))
      L (Lattice.hyperbolicPlaneLattice (K := K)) := by
  rcases b.isIsometric_standardEndpointModel
      (negativeQuarterUnit K) hclass
      standardEndpointShear_two_integral
      negativeQuarter_standardEndpointShear_diagonal_integral with ⟨f⟩
  have hendpoint :=
    standardEndpointModel_negativeQuarter_isIsometric_hyperbolicPlane
      (b.valueUnit 0)
  rw [← b.order_eq_ordUnit 0] at hendpoint
  rcases hendpoint with ⟨g⟩
  exact ⟨f.trans g⟩

/-- A binary BONG in the refined square class `-1/4` is a scaled
hyperbolic lattice. -/
theorem isScaledHyperbolicLattice_of_binaryUnitSquareClass_eq_negativeQuarter
    (b : BONG V q L 2)
    (hclass : b.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K)) :
    Lattice.IsScaledHyperbolicLattice q L := by
  exact ⟨b.order 0 - ramificationIndex K,
    b.isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
      hclass⟩

end BONG

end Bong
