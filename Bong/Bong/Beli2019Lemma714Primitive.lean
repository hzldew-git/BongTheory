/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714NonNormProduct
import Bong.Bong.BinaryEndpointStandardModel
import Bong.Lattice.FormRescale
import Bong.Lattice.NormGeneratorIsometry

/-!
# Beli (2019), Lemma 7.14(ii): primitive vectors in the discriminant plane

For the endpoint plane with parameter `-Delta/4`, the standard integral
model has quadratic polynomial

`X^2 + X*Y + rho*Y^2`, where `Delta = 1 - 4*rho` and `d(Delta) = 2e`.

The exact defect of `Delta` prevents this polynomial from lying in the
maximal ideal at a primitive integral pair.  Hence every primitive vector is
a norm generator.  This removes the corresponding paper sentence as an
extra hypothesis from the type-I branch of Lemma 7.14.
-/

namespace Bong

open Dyadic

universe u v w

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A lattice isometry detects divisibility by the same field scalar. -/
theorem Isometry.map_mem_rescale_iff (f : Isometry q r L M) (a : Kˣ)
    (x : V) :
    f.toLinearEquiv x ∈ rescale a M ↔ x ∈ rescale a L := by
  constructor
  · rw [mem_rescale_iff]
    rintro ⟨y, hy, hxy⟩
    rw [mem_rescale_iff]
    refine ⟨f.toLinearEquiv.symm y, (f.symm.map_mem y).1 hy, ?_⟩
    apply f.toLinearEquiv.injective
    simpa using hxy
  · rw [mem_rescale_iff]
    rintro ⟨y, hy, rfl⟩
    rw [mem_rescale_iff]
    exact ⟨f.toLinearEquiv y, (f.map_mem y).1 hy, by simp⟩

/-- The assertion that every primitive vector is a norm generator is
preserved by a lattice isometry. -/
theorem EveryPrimitiveIsNormGenerator.mapLatticeIsometry
    (h : EveryPrimitiveIsNormGenerator q L) (f : Isometry q r L M) :
    EveryPrimitiveIsNormGenerator r M := by
  intro y hy hyPrimitive
  let x : V := f.toLinearEquiv.symm y
  have hx : x ∈ L := (f.symm.map_mem y).1 hy
  have hxPrimitive : x ∉ rescale (uniformizerUnit K) L := by
    intro hxScaled
    apply hyPrimitive
    have hmapped := (f.map_mem_rescale_iff (uniformizerUnit K) x).2 hxScaled
    simpa [x] using hmapped
  have hxGenerator := h x hx hxPrimitive
  have hmapped := hxGenerator.mapLatticeIsometry f
  simpa [x] using hmapped

end Lattice

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem one_le_ord_of_isInMaximalIdeal {z : K}
    (hz : IsInMaximalIdeal K z) :
    (1 : WithTop Int) ≤ ord K z := by
  change (0 : WithTop Int) < ord K z at hz
  by_cases hzZero : z = 0
  · subst z
    simp
  · let zU : Kˣ := Units.mk0 z hzZero
    have hzOrder : (0 : Int) < ordUnit K zU := by
      apply WithTop.coe_lt_coe.mp
      simpa [zU] using hz
    calc
      (1 : WithTop Int) ≤ (ordUnit K zU : Int) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hzOrder)
      _ = ord K z := by simpa [zU] using coe_ordUnit K zU

private theorem uniformizer_inv_mul_mem_integerRing_of_isInMaximalIdeal
    {z : K} (hz : IsInMaximalIdeal K z) :
    (uniformizer K)⁻¹ * z ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  rw [Dyadic.IsIntegral, ord_mul, AddValuation.map_inv, ord_uniformizer]
  have hzOne := one_le_ord_of_isInMaximalIdeal (K := K) hz
  simpa [add_comm] using add_le_add_left hzOne (-1 : WithTop Int)

private theorem mem_rescale_binaryModelLattice_of_coordinates_maximal
    (x : Fin 2 → K)
    (hx0 : IsInMaximalIdeal K (x 0))
    (hx1 : IsInMaximalIdeal K (x 1)) :
    x ∈ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)) := by
  let y : Fin 2 → K := fun i ↦ (uniformizer K)⁻¹ * x i
  have hy : y ∈ binaryModelLattice (K := K) := by
    change y ∈ Lattice.basisLattice (binaryModelBasis (K := K))
    rw [Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    intro i
    fin_cases i
    · simpa [y, binaryModelBasis] using
        uniformizer_inv_mul_mem_integerRing_of_isInMaximalIdeal
          (K := K) hx0
    · simpa [y, binaryModelBasis] using
        uniformizer_inv_mul_mem_integerRing_of_isInMaximalIdeal
          (K := K) hx1
  rw [Lattice.mem_rescale_iff]
  refine ⟨y, hy, ?_⟩
  funext i
  simp only [coe_uniformizerUnit, Pi.smul_apply, smul_eq_mul, y]
  field_simp [uniformizer_ne_zero K]

theorem discriminantEndpoint_quadratic_apply
    [laws : DyadicDiscriminantClassLaws K] (x : Fin 2 → K) :
    (QuadraticSpace.binaryModel
      (negativeQuarterUnit K * laws.discriminantUnit)
      (standardEndpointShear (K := K))).quadratic x =
      x 0 ^ 2 + x 0 * x 1 + laws.rho * x 1 ^ 2 := by
  rw [QuadraticSpace.binaryModel_quadratic_apply]
  have htwo : (2 : K) * standardEndpointShear (K := K) = 1 := by
    dsimp [standardEndpointShear]
    field_simp
  have hdiag : standardEndpointShear (K := K) ^ 2 +
      ((negativeQuarterUnit K * laws.discriminantUnit : Kˣ) : K) =
        laws.rho := by
    rw [Units.val_mul, laws.discriminant_eq_one_sub_four_mul_rho]
    dsimp [standardEndpointShear, negativeQuarterUnit]
    change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ *
      (1 - 4 * laws.rho) = laws.rho
    norm_num [show (4 : K) = 2 * 2 by norm_num]
    field_simp
    ring
  rw [htwo, hdiag]
  ring

theorem discriminantEndpoint_quadratic_isValuationUnit
    [laws : DyadicDiscriminantClassLaws K]
    (x : Fin 2 → K) (hx : x ∈ binaryModelLattice (K := K))
    (hxPrimitive : x ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    IsValuationUnit K
      ((QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K))).quadratic x) := by
  have hxCoords :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing
      (binaryModelBasis (K := K)) x).1 hx
  have hx0Integral : x 0 ∈ IntegerRing K := by
    simpa [binaryModelBasis] using hxCoords 0
  have hx1Integral : x 1 ∈ IntegerRing K := by
    simpa [binaryModelBasis] using hxCoords 1
  have hx0Nonneg : (0 : WithTop Int) ≤ ord K (x 0) :=
    (mem_integerRing_iff K).1 hx0Integral
  have hx1Nonneg : (0 : WithTop Int) ≤ ord K (x 1) :=
    (mem_integerRing_iff K).1 hx1Integral
  let Q : K := x 0 ^ 2 + x 0 * x 1 + laws.rho * x 1 ^ 2
  have hquadratic :
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K))).quadratic x = Q := by
    exact discriminantEndpoint_quadratic_apply (K := K) x
  by_cases hx1Maximal : IsInMaximalIdeal K (x 1)
  · have hx0NotMaximal : ¬IsInMaximalIdeal K (x 0) := by
      intro hx0Maximal
      exact hxPrimitive
        (mem_rescale_binaryModelLattice_of_coordinates_maximal
          (K := K) x hx0Maximal hx1Maximal)
    have hx0Unit : IsValuationUnit K (x 0) := by
      rw [IsValuationUnit]
      exact le_antisymm (not_lt.mp hx0NotMaximal) hx0Nonneg
    have hx1SqIntegral : Dyadic.IsIntegral K (x 1 ^ 2) :=
      (mem_integerRing_iff K).1 ((IntegerRing K).pow_mem hx1Integral 2)
    have hrhoIntegral : Dyadic.IsIntegral K laws.rho := by
      change (0 : WithTop Int) ≤ ord K laws.rho
      rw [laws.rho_isValuationUnit]
    have hcross : IsInMaximalIdeal K (x 0 * x 1) :=
      isIntegral_mul_isInMaximalIdeal K hx0Nonneg hx1Maximal
    have hlast : IsInMaximalIdeal K (laws.rho * x 1 ^ 2) := by
      have hx1SqMaximal : IsInMaximalIdeal K (x 1 ^ 2) := by
        rw [pow_two]
        exact isInMaximalIdeal_mul_isIntegral K hx1Maximal hx1Nonneg
      exact isIntegral_mul_isInMaximalIdeal K hrhoIntegral hx1SqMaximal
    have hcorrection : IsInMaximalIdeal K
        (x 0 * x 1 + laws.rho * x 1 ^ 2) :=
      isInMaximalIdeal_add K hcross hlast
    rw [IsValuationUnit, hquadratic]
    have hfirst : ord K (x 0 ^ 2) = 0 := by
      rw [ord_pow, hx0Unit]
      simp
    have hlt : ord K (x 0 ^ 2) <
        ord K (x 0 * x 1 + laws.rho * x 1 ^ 2) := by
      rw [hfirst]
      exact hcorrection
    rw [show Q = x 0 ^ 2 +
        (x 0 * x 1 + laws.rho * x 1 ^ 2) by simp [Q, add_assoc],
      AddValuation.map_add_eq_of_lt_left (ord K) hlt, hfirst]
  · have hx1Unit : IsValuationUnit K (x 1) := by
      rw [IsValuationUnit]
      exact le_antisymm (not_lt.mp hx1Maximal) hx1Nonneg
    have hrhoIntegral : laws.rho ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      change (0 : WithTop Int) ≤ ord K laws.rho
      rw [laws.rho_isValuationUnit]
    have hQIntegral : Q ∈ IntegerRing K := by
      dsimp [Q]
      exact (IntegerRing K).add_mem _ _
        ((IntegerRing K).add_mem _ _
          ((IntegerRing K).pow_mem hx0Integral 2)
          ((IntegerRing K).mul_mem _ _ hx0Integral hx1Integral))
        ((IntegerRing K).mul_mem _ _ hrhoIntegral
          ((IntegerRing K).pow_mem hx1Integral 2))
    have hQNonneg : (0 : WithTop Int) ≤ ord K Q :=
      (mem_integerRing_iff K).1 hQIntegral
    rw [IsValuationUnit, hquadratic]
    by_contra hQNotZeroOrder
    have hQMaximal : IsInMaximalIdeal K Q :=
      lt_of_le_of_ne hQNonneg (Ne.symm hQNotZeroOrder)
    have hx1Ne : x 1 ≠ 0 := by
      intro hzero
      rw [hzero, IsValuationUnit, ord_zero] at hx1Unit
      exact WithTop.top_ne_coe hx1Unit
    let t : K := (2 : K) * x 0 / x 1 + 1
    have herror :
        1 - t ^ 2 / (laws.discriminantUnit : K) =
          -(4 * Q / ((laws.discriminantUnit : K) * x 1 ^ 2)) := by
      dsimp [t, Q]
      field_simp [hx1Ne, Units.ne_zero laws.discriminantUnit]
      rw [laws.discriminant_eq_one_sub_four_mul_rho]
      ring
    have hfourOrder : ord K (4 : K) =
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
      rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
        ← ramificationIndex_spec]
      norm_cast
      ring
    have hdenominatorOrder :
        ord K ((laws.discriminantUnit : K) * x 1 ^ 2) = 0 := by
      rw [ord_mul, laws.discriminant_isValuationUnit, ord_pow, hx1Unit]
      simp
    have herrorOrder :
        ord K (1 - t ^ 2 / (laws.discriminantUnit : K)) =
          (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) +
            ord K Q := by
      calc
        ord K (1 - t ^ 2 / (laws.discriminantUnit : K)) =
            ord K (4 * Q /
              ((laws.discriminantUnit : K) * x 1 ^ 2)) := by
          rw [herror, ord_neg]
        _ = ord K (4 * Q) +
            -(ord K ((laws.discriminantUnit : K) * x 1 ^ 2)) := by
          rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv]
        _ = (ord K (4 : K) + ord K Q) + -0 := by
          rw [ord_mul, hdenominatorOrder]
        _ = (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) +
            ord K Q := by rw [hfourOrder]; simp
    have hQOne := one_le_ord_of_isInMaximalIdeal (K := K) hQMaximal
    have hdepth :
        (((2 * ramificationIndex K + 1 : Nat) : Int) : WithTop Int) ≤
          ord K (1 - t ^ 2 / (laws.discriminantUnit : K)) := by
      rw [herrorOrder]
      have hadd := add_le_add_left hQOne
        ((((2 * ramificationIndex K : Nat) : Int) : WithTop Int))
      norm_num at hadd ⊢
      simpa [add_comm, add_left_comm, add_assoc] using hadd
    have happrox : IsQuadraticApproximation K laws.discriminantUnit
        (2 * ramificationIndex K + 1) := ⟨t, hdepth⟩
    have htooDeep := natCast_le_quadraticDefect K happrox
    rw [laws.discriminant_defect] at htooDeep
    exact (by
      have : 2 * ramificationIndex K + 1 ≤ 2 * ramificationIndex K := by
        exact_mod_cast htooDeep
      omega)

/-- Every primitive vector of the unscaled discriminant endpoint model is a
norm generator. -/
theorem discriminantEndpointModel_everyPrimitiveIsNormGenerator
    [laws : DyadicDiscriminantClassLaws K] :
    Lattice.EveryPrimitiveIsNormGenerator
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K)))
      (binaryModelLattice (K := K)) := by
  intro x hx hxPrimitive
  have hunit := discriminantEndpoint_quadratic_isValuationUnit
    (K := K) x hx hxPrimitive
  have hanisotropic :
      (QuadraticSpace.binaryModel
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K))).IsAnisotropic x := by
    rw [QuadraticSpace.IsAnisotropic]
    intro hzero
    rw [hzero, IsValuationUnit, ord_zero] at hunit
    exact WithTop.top_ne_coe hunit
  apply ((binaryModelFirst_isNormGenerator
    (negativeQuarterUnit K * laws.discriminantUnit)
    (standardEndpointShear (K := K))
    standardEndpointShear_two_integral
    discriminant_standardEndpointShear_diagonal_integral).iff_isValuationUnit_quadratic_of_value_one
      (binaryModelFirst_isAnisotropic
        (negativeQuarterUnit K * laws.discriminantUnit)
        (standardEndpointShear (K := K)))
      (QuadraticSpace.binaryModel_quadratic_first _ _)
      hx hanisotropic).2
  exact hunit

/-- Rescaling the discriminant endpoint form does not change the primitive
vectors and preserves their norm-generator property. -/
theorem standardDiscriminantEndpoint_everyPrimitiveIsNormGenerator
    [laws : DyadicDiscriminantClassLaws K] (a : Kˣ) :
    Lattice.EveryPrimitiveIsNormGenerator
      (QuadraticSpace.rescaleUnit a
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K * laws.discriminantUnit)
          (standardEndpointShear (K := K))))
      (binaryModelLattice (K := K)) := by
  intro x hx hxPrimitive
  exact (discriminantEndpointModel_everyPrimitiveIsNormGenerator
    (K := K) x hx hxPrimitive).rescaleQuadraticUnit a

/-- A binary BONG in the discriminant endpoint square class has the
primitive-vector property used in Beli (2019), Lemma 7.14(ii). -/
theorem everyPrimitiveIsNormGenerator_of_binaryUnitSquareClass_discriminant
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2)
    (hclass : b.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit)) :
    Lattice.EveryPrimitiveIsNormGenerator q L := by
  rcases b.isIsometric_standardEndpointModel
      (negativeQuarterUnit K * laws.discriminantUnit) hclass
      standardEndpointShear_two_integral
      discriminant_standardEndpointShear_diagonal_integral with ⟨f⟩
  have hmodel :=
    standardDiscriminantEndpoint_everyPrimitiveIsNormGenerator
      (K := K) (b.valueUnit 0)
  have hmodel' : Lattice.EveryPrimitiveIsNormGenerator
      (b.standardEndpointModelSpace
        (negativeQuarterUnit K * laws.discriminantUnit))
      (binaryModelLattice (K := K)) := by
    simpa [standardEndpointModelSpace] using hmodel
  exact hmodel'.mapLatticeIsometry f.symm

end BONG

end Bong
