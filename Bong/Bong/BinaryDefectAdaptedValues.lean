/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDefectAdaptedShear
import Bong.Bong.BinaryModelIsometry
import Bong.Bong.BinaryShearIsometry
import Bong.Dyadic.BeliGroups
import Bong.Lattice.PowerIdeal

/-!
# Defect-adapted binary value estimates

Beli (2003), paragraph 3.9 chooses an integral shear in which the mixed
coefficient has order `R/2` and the second diagonal coefficient has order
`R + d`.  Corollary 3.10(b,c) is derived from that proved existential choice,
not from an arbitrary lift of the projected BONG vector.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The cutoff `e - R/2` in Corollary 3.10(b,c). -/
noncomputable def binaryCorollaryDefectCutoff
    (b : BONG V q L 2) : Nat :=
  Int.toNat
    ((ramificationIndex K : Int) - b.binaryOrderGap / 2)

/-- The exponent `R/2 + e` in Corollary 3.10(b). -/
noncomputable def binaryCorollaryHighExponent
    (b : BONG V q L 2) : Nat :=
  Int.toNat
    ((ramificationIndex K : Int) + b.binaryOrderGap / 2)

/-- The exponent `R + d` in Corollary 3.10(c). -/
noncomputable def binaryCorollaryLowExponent
    (b : BONG V q L 2) : Nat :=
  Int.toNat
    (b.binaryOrderGap +
      (beliParameterDefectNat K b.binaryParameter : Int))

/-- Every binary BONG parameter has order at least `-2e`. -/
theorem binaryOrderGap_ge_neg_two_mul_e (b : BONG V q L 2) :
    -(2 * (ramificationIndex K : Int)) ≤ b.binaryOrderGap := by
  have hlower :=
    b.binaryParameter_isBinaryParameterAdmissible.ordUnit_ge_neg_two_mul_e
  change -(2 * (ramificationIndex K : Int)) ≤
    b.binaryParameterOrder at hlower
  rwa [b.binaryParameterOrder_eq_orderGap] at hlower

/-- For even `R` in the range `-2e ≤ R ≤ 2e`, the two exponents involving
`R/2` are nonnegative and `Int.toNat` is exact. -/
theorem binaryCorollary_high_cutoff_casts
    (b : BONG V q L 2) (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤ 2 * (ramificationIndex K : Int)) :
    (binaryCorollaryHighExponent b : Int) =
        (ramificationIndex K : Int) + b.binaryOrderGap / 2 ∧
      (binaryCorollaryDefectCutoff b : Int) =
        (ramificationIndex K : Int) - b.binaryOrderGap / 2 := by
  rcases hEven with ⟨r, hr⟩
  have hlower := b.binaryOrderGap_ge_neg_two_mul_e
  constructor
  · unfold binaryCorollaryHighExponent
    rw [Int.toNat_of_nonneg]
    omega
  · unfold binaryCorollaryDefectCutoff
    rw [Int.toNat_of_nonneg]
    omega

end BONG

namespace BONG

/-- Membership in the standard binary model lattice is coordinatewise
integrality. -/
theorem mem_binaryModelLattice_iff_coordinates (x : Fin 2 → K) :
    x ∈ binaryModelLattice (K := K) ↔
      ∀ i, x i ∈ IntegerRing K := by
  rw [binaryModelLattice,
    Lattice.mem_basisLattice_iff_repr_mem_integerRing]
  simp [binaryModelBasis]

/-- Coordinate calculation underlying the defect-adapted binary value
estimate. -/
theorem binaryModel_quadraticValueSet_subset_integralSquareResidueSet_of_ord_le
    (a : Kˣ) (c t : K) (ht : t ≠ 0)
    (hcross : ord K t ≤ ord K ((2 : K) * c))
    (hdiag : ord K t ≤ ord K (c ^ 2 + (a : K))) :
    Lattice.quadraticValueSet (QuadraticSpace.binaryModel a c)
        (binaryModelLattice (K := K)) ⊆
      Lattice.integralSquareResidueSet
        (Lattice.principalIdeal (K := K) t) := by
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxCoords := (mem_binaryModelLattice_iff_coordinates x).1 hx
  let x₀ : IntegerRing K := ⟨x 0, hxCoords 0⟩
  let x₁ : IntegerRing K := ⟨x 1, hxCoords 1⟩
  refine ⟨x₀, ?_⟩
  have hcrossGenerator : (2 : K) * c ∈
      Lattice.principalIdeal (K := K) t :=
    Lattice.mem_principalIdeal_of_ord_le ht hcross
  have hcrossTerm :=
    (Lattice.principalIdeal (K := K) t).smul_mem
      (x₀ * x₁) hcrossGenerator
  change ((x₀ : K) * (x₁ : K)) * ((2 : K) * c) ∈
    Lattice.principalIdeal (K := K) t at hcrossTerm
  have hdiagGenerator : c ^ 2 + (a : K) ∈
      Lattice.principalIdeal (K := K) t :=
    Lattice.mem_principalIdeal_of_ord_le ht hdiag
  have hdiagTerm :=
    (Lattice.principalIdeal (K := K) t).smul_mem
      (x₁ ^ 2) hdiagGenerator
  change (x₁ : K) ^ 2 * (c ^ 2 + (a : K)) ∈
    Lattice.principalIdeal (K := K) t at hdiagTerm
  rw [QuadraticSpace.binaryModel_quadratic_apply]
  convert (Lattice.principalIdeal (K := K) t).add_mem
    hcrossTerm hdiagTerm using 1 <;> ring

/-- Transport a value estimate from a defect-adapted shear model without
normalizing the first BONG value.  The error generator is multiplied by the
first value unit, exactly as required when Corollary 3.10 is scaled back to
an arbitrary binary BONG. -/
theorem quadraticValueSet_scaled_subset_of_defectAdaptedShear
    (b : BONG V q L 2) (c t : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiagIntegral : c ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K)
    (ht : t ≠ 0)
    (hcross : ord K t ≤ ord K ((2 : K) * c))
    (hdiag : ord K t ≤
      ord K (c ^ 2 + (b.binaryParameter : K))) :
    ∀ z ∈ Lattice.quadraticValueSet q L,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.principalIdeal (K := K)
            ((b.valueUnit 0 : K) * t) := by
  let c₀ : K := b.binaryModelCoefficient
  have hc₀ := b.binaryModelCoefficient_isAdmissibleWitness
  have hsub : c - c₀ ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing b.binaryParameter c c₀
      htwo hdiagIntegral hc₀.1 hc₀.2
  rcases rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (b.valueUnit 0) b.binaryParameter c c₀ hsub with ⟨g⟩
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  let F : Lattice.Isometry
      (QuadraticSpace.rescaleUnit (b.valueUnit 0)
        (QuadraticSpace.binaryModel b.binaryParameter c)) q
      (binaryModelLattice (K := K)) L :=
    g.trans f
  have hmodel :=
    binaryModel_quadraticValueSet_subset_integralSquareResidueSet_of_ord_le
      b.binaryParameter c t ht hcross hdiag
  intro z hz
  rw [Lattice.mem_quadraticValueSet_iff] at hz
  rcases hz with ⟨y, hy, rfl⟩
  let x : Fin 2 → K := F.toLinearEquiv.symm y
  have hx : x ∈ binaryModelLattice (K := K) := by
    apply (F.map_mem x).mpr
    simpa [x]
  rcases hmodel
      ((Lattice.mem_quadraticValueSet_iff _ _ _).2 ⟨x, hx, rfl⟩) with
    ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  have hmap := F.map_quadratic x
  change q.quadratic (F.toLinearEquiv x) =
    (b.valueUnit 0 : K) *
      (QuadraticSpace.binaryModel b.binaryParameter c).quadratic x at hmap
  have hFx : F.toLinearEquiv x = y := by simp [x]
  rw [← hFx, hmap]
  rw [Lattice.principalIdeal, Submodule.mem_span_singleton] at hx₀ ⊢
  rcases hx₀ with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  have hd' : (d : K) * t =
      (QuadraticSpace.binaryModel b.binaryParameter c).quadratic x -
        (x₀ : K) ^ 2 := by
    simpa [Algebra.smul_def] using hd
  rw [b.coe_valueUnit]
  change (d : K) * (b.value 0 * t) =
    b.value 0 *
        (QuadraticSpace.binaryModel b.binaryParameter c).quadratic x -
      b.value 0 * (x₀ : K) ^ 2
  calc
    (d : K) * (b.value 0 * t) = b.value 0 * ((d : K) * t) := by ring
    _ = b.value 0 *
        ((QuadraticSpace.binaryModel b.binaryParameter c).quadratic x -
          (x₀ : K) ^ 2) := by rw [hd']
    _ = b.value 0 *
          (QuadraticSpace.binaryModel b.binaryParameter c).quadratic x -
        b.value 0 * (x₀ : K) ^ 2 := by ring

/-- Transport a value estimate from a defect-adapted shear model to the
original normalized binary BONG. -/
theorem quadraticValueSet_subset_integralSquareResidueSet_of_defectAdaptedShear
    (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (c t : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiagIntegral : c ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K)
    (ht : t ≠ 0)
    (hcross : ord K t ≤ ord K ((2 : K) * c))
    (hdiag : ord K t ≤
      ord K (c ^ 2 + (b.binaryParameter : K))) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.principalIdeal (K := K) t) := by
  intro z hz
  rcases b.quadraticValueSet_scaled_subset_of_defectAdaptedShear
      c t htwo hdiagIntegral ht hcross hdiag z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [b.coe_valueUnit, hvalue] using hx

/-- Beli (2003), Corollary 3.10(b). -/
theorem quadraticValueSet_subset_powerIdeal_of_high_defect
    (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : (binaryCorollaryDefectCutoff b : ℕ∞) ≤
      beliParameterDefect K b.binaryParameter) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K)
          (binaryCorollaryHighExponent b : Int)) := by
  have hEvenParameter : Even (ordUnit K b.binaryParameter) := by
    change Even b.binaryParameterOrder
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hEven
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hEvenParameter with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hsecond⟩
  rw [hparameterOrder] at hcrossEq hsecond
  rcases b.binaryCorollary_high_cutoff_casts hEven hupper with
    ⟨hhighCast, hcutoffCast⟩
  let t : Kˣ := uniformizerPowerUnit K
    (binaryCorollaryHighExponent b : Int)
  have htOrder : ord K (t : K) =
      (((ramificationIndex K : Int) +
        b.binaryOrderGap / 2 : Int) : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit, hhighCast]
  have hcross : ord K (t : K) ≤
      ord K ((2 : K) * c) := by
    rw [htOrder, hcrossEq]
  have hdiag : ord K (t : K) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) := by
    rcases hsecond with htop | hfinite
    · rw [htop.2, ord_zero]
      exact le_top
    · have hcutoffLe : binaryCorollaryDefectCutoff b ≤
          beliParameterDefectNat K b.binaryParameter := by
        have hnat := ENat.toNat_le_toNat hdefect hfinite.1
        simpa [beliParameterDefectNat] using hnat
      have hsum : b.binaryOrderGap +
            (binaryCorollaryDefectCutoff b : Int) =
          (ramificationIndex K : Int) +
            b.binaryOrderGap / 2 := by
        rw [hcutoffCast]
        rcases hEven with ⟨r, hr⟩
        omega
      rw [htOrder, hfinite.2, ← hsum]
      have hcutoffLeInt : (binaryCorollaryDefectCutoff b : Int) ≤
          (beliParameterDefectNat K b.binaryParameter : Int) := by
        exact_mod_cast hcutoffLe
      have hadd : b.binaryOrderGap +
            (binaryCorollaryDefectCutoff b : Int) ≤
          b.binaryOrderGap +
            (beliParameterDefectNat K b.binaryParameter : Int) := by
        omega
      exact_mod_cast hadd
  have hsubset :=
    b.quadraticValueSet_subset_integralSquareResidueSet_of_defectAdaptedShear
      hvalue c (t : K) htwo hdiagIntegral (Units.ne_zero t) hcross hdiag
  have hideal : Lattice.principalIdeal (K := K) (t : K) =
      Lattice.powerIdeal (K := K)
        (binaryCorollaryHighExponent b : Int) := by
    simpa [t, ordUnit_uniformizerPowerUnit] using
      (Lattice.principalIdeal_eq_powerIdeal t)
  rwa [hideal] at hsubset

/-- Scaled form of Corollary 3.10(b): no normalization of the first binary
value is imposed.  The absolute error exponent is the first BONG order plus
the normalized binary exponent. -/
theorem quadraticValueSet_scaled_subset_powerIdeal_of_high_defect
    (b : BONG V q L 2)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : (binaryCorollaryDefectCutoff b : ℕ∞) ≤
      beliParameterDefect K b.binaryParameter) :
    ∀ z ∈ Lattice.quadraticValueSet q L,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K)
            (b.order 0 + ((ramificationIndex K : Int) +
              b.binaryOrderGap / 2)) := by
  have hEvenParameter : Even (ordUnit K b.binaryParameter) := by
    change Even b.binaryParameterOrder
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hEven
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hEvenParameter with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hsecond⟩
  rw [hparameterOrder] at hcrossEq hsecond
  rcases b.binaryCorollary_high_cutoff_casts hEven hupper with
    ⟨hhighCast, hcutoffCast⟩
  let t : Kˣ := uniformizerPowerUnit K
    (binaryCorollaryHighExponent b : Int)
  have htOrder : ord K (t : K) =
      (((ramificationIndex K : Int) +
        b.binaryOrderGap / 2 : Int) : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit, hhighCast]
  have hcross : ord K (t : K) ≤
      ord K ((2 : K) * c) := by
    rw [htOrder, hcrossEq]
  have hdiag : ord K (t : K) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) := by
    rcases hsecond with htop | hfinite
    · rw [htop.2, ord_zero]
      exact le_top
    · have hcutoffLe : binaryCorollaryDefectCutoff b ≤
          beliParameterDefectNat K b.binaryParameter := by
        have hnat := ENat.toNat_le_toNat hdefect hfinite.1
        simpa [beliParameterDefectNat] using hnat
      have hsum : b.binaryOrderGap +
            (binaryCorollaryDefectCutoff b : Int) =
          (ramificationIndex K : Int) +
            b.binaryOrderGap / 2 := by
        rw [hcutoffCast]
        rcases hEven with ⟨r, hr⟩
        omega
      rw [htOrder, hfinite.2, ← hsum]
      have hcutoffLeInt : (binaryCorollaryDefectCutoff b : Int) ≤
          (beliParameterDefectNat K b.binaryParameter : Int) := by
        exact_mod_cast hcutoffLe
      exact_mod_cast (show b.binaryOrderGap +
          (binaryCorollaryDefectCutoff b : Int) ≤
            b.binaryOrderGap +
              (beliParameterDefectNat K b.binaryParameter : Int) by omega)
  have hsubset :=
    b.quadraticValueSet_scaled_subset_of_defectAdaptedShear
      c (t : K) htwo hdiagIntegral (Units.ne_zero t) hcross hdiag
  have hideal : Lattice.principalIdeal (K := K)
        (((b.valueUnit 0) * t : Kˣ) : K) =
      Lattice.powerIdeal (K := K)
        (b.order 0 + ((ramificationIndex K : Int) +
          b.binaryOrderGap / 2)) := by
    have hprincipal :=
      Lattice.principalIdeal_eq_powerIdeal ((b.valueUnit 0) * t)
    rw [ordUnit_mul, ← b.order_eq_ordUnit,
      ordUnit_uniformizerPowerUnit, hhighCast] at hprincipal
    exact hprincipal
  intro z hz
  rcases hsubset z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change z - b.value 0 * (x : K) ^ 2 ∈
    Lattice.principalIdeal (K := K)
      (((b.valueUnit 0) * t : Kˣ) : K) at hx
  rwa [hideal] at hx

/-- Beli (2003), Corollary 3.10(c). -/
theorem quadraticValueSet_subset_powerIdeal_of_low_defect
    (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K b.binaryParameter ≤
      (binaryCorollaryDefectCutoff b : ℕ∞)) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K)
          (binaryCorollaryLowExponent b : Int)) := by
  have hEvenParameter : Even (ordUnit K b.binaryParameter) := by
    change Even b.binaryParameterOrder
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hEven
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hEvenParameter with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hsecond⟩
  rw [hparameterOrder] at hcrossEq hsecond
  rcases b.binaryCorollary_high_cutoff_casts hEven hupper with
    ⟨_, hcutoffCast⟩
  have hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤ := by
    intro htop
    rw [htop] at hdefect
    exact ENat.coe_ne_top _ (top_unique hdefect)
  have hsecondEq : ord K (c ^ 2 + (b.binaryParameter : K)) =
      ((b.binaryOrderGap +
          (beliParameterDefectNat K
            b.binaryParameter : Int) : Int) : WithTop Int) := by
    rcases hsecond with htop | hfiniteCase
    · exact (hfinite htop.1).elim
    · exact hfiniteCase.2
  have hqNonneg : (0 : WithTop Int) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) :=
    (mem_integerRing_iff K).1 hdiagIntegral
  have hlowNonneg : 0 ≤ b.binaryOrderGap +
      (beliParameterDefectNat K b.binaryParameter : Int) := by
    rw [hsecondEq] at hqNonneg
    exact_mod_cast hqNonneg
  have hlowCast : (binaryCorollaryLowExponent b : Int) =
      b.binaryOrderGap +
        (beliParameterDefectNat K b.binaryParameter : Int) := by
    unfold binaryCorollaryLowExponent
    rw [Int.toNat_of_nonneg hlowNonneg]
  have hdefectNatLe :
      beliParameterDefectNat K b.binaryParameter ≤
        binaryCorollaryDefectCutoff b := by
    have hnat := ENat.toNat_le_toNat hdefect (by simp)
    simpa [beliParameterDefectNat] using hnat
  have htargetLeCross :
      b.binaryOrderGap +
          (beliParameterDefectNat K b.binaryParameter : Int) ≤
        (ramificationIndex K : Int) + b.binaryOrderGap / 2 := by
    have hdefectNatLeInt :
        (beliParameterDefectNat K b.binaryParameter : Int) ≤
          (binaryCorollaryDefectCutoff b : Int) := by
      exact_mod_cast hdefectNatLe
    rw [hcutoffCast] at hdefectNatLeInt
    rcases hEven with ⟨r, hr⟩
    omega
  let t : Kˣ := uniformizerPowerUnit K
    (binaryCorollaryLowExponent b : Int)
  have htOrder : ord K (t : K) =
      ((b.binaryOrderGap +
          (beliParameterDefectNat K
            b.binaryParameter : Int) : Int) : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit, hlowCast]
  have hcross : ord K (t : K) ≤
      ord K ((2 : K) * c) := by
    rw [htOrder, hcrossEq]
    exact_mod_cast htargetLeCross
  have hdiag : ord K (t : K) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) := by
    rw [htOrder, hsecondEq]
  have hsubset :=
    b.quadraticValueSet_subset_integralSquareResidueSet_of_defectAdaptedShear
      hvalue c (t : K) htwo hdiagIntegral (Units.ne_zero t) hcross hdiag
  have hideal : Lattice.principalIdeal (K := K) (t : K) =
      Lattice.powerIdeal (K := K)
        (binaryCorollaryLowExponent b : Int) := by
    simpa [t, ordUnit_uniformizerPowerUnit] using
      (Lattice.principalIdeal_eq_powerIdeal t)
  rwa [hideal] at hsubset

/-- Scaled form of Corollary 3.10(c): no normalization of the first binary
value is imposed. -/
theorem quadraticValueSet_scaled_subset_powerIdeal_of_low_defect
    (b : BONG V q L 2)
    (hEven : Even b.binaryOrderGap)
    (hupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hdefect : beliParameterDefect K b.binaryParameter ≤
      (binaryCorollaryDefectCutoff b : ℕ∞)) :
    ∀ z ∈ Lattice.quadraticValueSet q L,
      ∃ x : IntegerRing K,
        z - b.value 0 * (x : K) ^ 2 ∈
          Lattice.powerIdeal (K := K)
            (b.order 0 + (b.binaryOrderGap +
              (beliParameterDefectNat K b.binaryParameter : Int))) := by
  have hEvenParameter : Even (ordUnit K b.binaryParameter) := by
    change Even b.binaryParameterOrder
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hEven
  have hparameterOrder : ordUnit K b.binaryParameter = b.binaryOrderGap := by
    change b.binaryParameterOrder = b.binaryOrderGap
    exact b.binaryParameterOrder_eq_orderGap
  rcases exists_defectAdaptedShear b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hEvenParameter with
    ⟨c, htwo, hdiagIntegral, hcrossEq, hsecond⟩
  rw [hparameterOrder] at hcrossEq hsecond
  rcases b.binaryCorollary_high_cutoff_casts hEven hupper with
    ⟨_, hcutoffCast⟩
  have hfinite : beliParameterDefect K b.binaryParameter ≠ ⊤ := by
    intro htop
    rw [htop] at hdefect
    exact ENat.coe_ne_top _ (top_unique hdefect)
  have hsecondEq : ord K (c ^ 2 + (b.binaryParameter : K)) =
      ((b.binaryOrderGap +
          (beliParameterDefectNat K
            b.binaryParameter : Int) : Int) : WithTop Int) := by
    rcases hsecond with htop | hfiniteCase
    · exact (hfinite htop.1).elim
    · exact hfiniteCase.2
  have hqNonneg : (0 : WithTop Int) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) :=
    (mem_integerRing_iff K).1 hdiagIntegral
  have hlowNonneg : 0 ≤ b.binaryOrderGap +
      (beliParameterDefectNat K b.binaryParameter : Int) := by
    rw [hsecondEq] at hqNonneg
    exact_mod_cast hqNonneg
  have hlowCast : (binaryCorollaryLowExponent b : Int) =
      b.binaryOrderGap +
        (beliParameterDefectNat K b.binaryParameter : Int) := by
    unfold binaryCorollaryLowExponent
    rw [Int.toNat_of_nonneg hlowNonneg]
  have hdefectNatLe :
      beliParameterDefectNat K b.binaryParameter ≤
        binaryCorollaryDefectCutoff b := by
    have hnat := ENat.toNat_le_toNat hdefect (by simp)
    simpa [beliParameterDefectNat] using hnat
  have htargetLeCross :
      b.binaryOrderGap +
          (beliParameterDefectNat K b.binaryParameter : Int) ≤
        (ramificationIndex K : Int) + b.binaryOrderGap / 2 := by
    have hdefectNatLeInt :
        (beliParameterDefectNat K b.binaryParameter : Int) ≤
          (binaryCorollaryDefectCutoff b : Int) := by
      exact_mod_cast hdefectNatLe
    rw [hcutoffCast] at hdefectNatLeInt
    rcases hEven with ⟨r, hr⟩
    omega
  let t : Kˣ := uniformizerPowerUnit K
    (binaryCorollaryLowExponent b : Int)
  have htOrder : ord K (t : K) =
      ((b.binaryOrderGap +
          (beliParameterDefectNat K
            b.binaryParameter : Int) : Int) : WithTop Int) := by
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit, hlowCast]
  have hcross : ord K (t : K) ≤
      ord K ((2 : K) * c) := by
    rw [htOrder, hcrossEq]
    exact_mod_cast htargetLeCross
  have hdiag : ord K (t : K) ≤
      ord K (c ^ 2 + (b.binaryParameter : K)) := by
    rw [htOrder, hsecondEq]
  have hsubset :=
    b.quadraticValueSet_scaled_subset_of_defectAdaptedShear
      c (t : K) htwo hdiagIntegral (Units.ne_zero t) hcross hdiag
  have hideal : Lattice.principalIdeal (K := K)
        (((b.valueUnit 0) * t : Kˣ) : K) =
      Lattice.powerIdeal (K := K)
        (b.order 0 + (b.binaryOrderGap +
          (beliParameterDefectNat K b.binaryParameter : Int))) := by
    have hprincipal :=
      Lattice.principalIdeal_eq_powerIdeal ((b.valueUnit 0) * t)
    rw [ordUnit_mul, ← b.order_eq_ordUnit,
      ordUnit_uniformizerPowerUnit, hlowCast] at hprincipal
    exact hprincipal
  intro z hz
  rcases hsubset z hz with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change z - b.value 0 * (x : K) ^ 2 ∈
    Lattice.principalIdeal (K := K)
      (((b.valueUnit 0) * t : Kˣ) : K) at hx
  rwa [hideal] at hx

end BONG

end Bong
