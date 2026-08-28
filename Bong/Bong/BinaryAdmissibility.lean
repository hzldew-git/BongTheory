/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryExactRealization
import Bong.Bong.Structural

/-!
# Stability of binary admissibility

Beli's set of binary parameters lives modulo squares of valuation units.
This file proves that the operational integrality predicate descends to that
quotient and also records its monotonicity under integral square factors.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The adjacent binary parameter `a_(i+1) / a_i`. -/
noncomputable def adjacentParameter {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) : Kˣ :=
  b.valueUnit ⟨i.1 + 1, hi⟩ / b.valueUnit i

/-- The adjacent parameter modulo valuation-unit squares. -/
noncomputable def adjacentUnitSquareClass
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    UnitSquareClass K :=
  unitSquareClass K (b.adjacentParameter i hi)

/-- The adjacent parameter has order `Rᵢ₊₁ - Rᵢ`. -/
theorem ordUnit_adjacentParameter
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    ordUnit K (b.adjacentParameter i hi) =
      b.order ⟨i.1 + 1, hi⟩ - b.order i := by
  unfold adjacentParameter
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    ← b.order_eq_ordUnit, ← b.order_eq_ordUnit]
  abel

/-- Decompose an adjacent parameter into its uniformizer power and normalized
unit quotient. -/
theorem adjacentParameter_eq_uniformizerPower_mul_normalized
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    b.adjacentParameter i hi =
      uniformizerUnit K ^
          (b.order ⟨i.1 + 1, hi⟩ - b.order i) *
        (b.normalizedValue ⟨i.1 + 1, hi⟩ / b.normalizedValue i) := by
  unfold adjacentParameter
  rw [← b.uniformizer_zpow_mul_normalizedValue ⟨i.1 + 1, hi⟩,
    ← b.uniformizer_zpow_mul_normalizedValue i]
  simp only [div_eq_mul_inv, mul_inv_rev, zpow_sub]
  let A : Kˣ := uniformizerUnit K ^ b.order ⟨i.1 + 1, hi⟩
  let B : Kˣ := b.normalizedValue ⟨i.1 + 1, hi⟩
  let C : Kˣ := uniformizerUnit K ^ b.order i
  let D : Kˣ := b.normalizedValue i
  change A * B * (D⁻¹ * C⁻¹) = A * C⁻¹ * (B * D⁻¹)
  calc
    A * B * (D⁻¹ * C⁻¹) = A * (B * (C⁻¹ * D⁻¹)) := by
      rw [mul_comm D⁻¹ C⁻¹, mul_assoc]
    _ = A * (C⁻¹ * (B * D⁻¹)) := by
      rw [mul_left_comm B C⁻¹ D⁻¹]
    _ = A * C⁻¹ * (B * D⁻¹) := by rw [mul_assoc]

/-- For an even adjacent order gap, the negative adjacent parameter and
Beli's normalized adjacent product differ by a square. -/
theorem negative_adjacentParameter_eq_normalizedProduct_mul_square_of_even
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc)) :
    ∃ s : Kˣ,
      -(b.adjacentParameter i.castSucc (by simpa using i.isLt)) =
        b.normalizedAdjacentProduct i * s ^ 2 := by
  rcases heven with ⟨r, hr⟩
  let εi : Kˣ := b.normalizedValue i.castSucc
  let εj : Kˣ := b.normalizedValue i.succ
  let s : Kˣ := uniformizerUnit K ^ r * εi⁻¹
  refine ⟨s, ?_⟩
  rw [adjacentParameter_eq_uniformizerPower_mul_normalized]
  have hindex : (⟨i.castSucc.1 + 1, by simpa using i.isLt⟩ : Fin (n + 1)) =
      i.succ := by ext; simp
  rw [hindex]
  have hpower : uniformizerUnit K ^
        (b.order i.succ - b.order i.castSucc) =
      (uniformizerUnit K ^ r) ^ 2 := by
    rw [hr]
    rw [pow_two, ← zpow_add]
  rw [hpower]
  unfold normalizedAdjacentProduct
  change -((uniformizerUnit K ^ r) ^ 2 * (εj / εi)) =
    -(εi * εj) * s ^ 2
  dsimp only [s]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero εi]

/-- Consequently, the two versions of the adjacent quadratic defect agree. -/
theorem quadraticDefect_negative_adjacentParameter_eq_normalizedProduct_of_even
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n)
    (heven : Even (b.order i.succ - b.order i.castSucc)) :
    quadraticDefect K
        (-(b.adjacentParameter i.castSucc (by simpa using i.isLt))) =
      quadraticDefect K (b.normalizedAdjacentProduct i) := by
  rcases b.negative_adjacentParameter_eq_normalizedProduct_mul_square_of_even
      i heven with ⟨s, hs⟩
  rw [hs, quadraticDefect_mul_square]

/-- Every adjacent parameter of a BONG is an admissible binary parameter. -/
theorem adjacentParameter_isBinaryParameterAdmissible
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) (hi : i.1 + 1 < n) :
    IsBinaryParameterAdmissible (b.adjacentParameter i hi) := by
  have hbound : i.1 + 2 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 2 hbound with ⟨w⟩
  have hparameter : w.bong.binaryParameter =
      b.adjacentParameter i hi := by
    unfold binaryParameter adjacentParameter
    rw [w.valueUnit_eq, w.valueUnit_eq]
    congr 2
  rw [← hparameter]
  exact w.bong.binaryParameter_isBinaryParameterAdmissible

/-- Every integral parameter is binary-admissible; the witness in the
elementary binary model is `c = 0`. -/
theorem isBinaryParameterAdmissible_of_ordUnit_nonneg
    {a : Kˣ} (ha : 0 ≤ ordUnit K a) :
    IsBinaryParameterAdmissible a := by
  refine ⟨0, by simp, ?_⟩
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    exact_mod_cast ha
  simpa using haIntegral

/-- Multiplication by the square of an integral nonzero scalar preserves
binary admissibility. -/
theorem IsBinaryParameterAdmissible.mul_integral_square
    {a s : Kˣ} (ha : IsBinaryParameterAdmissible a)
    (hs : (s : K) ∈ IntegerRing K) :
    IsBinaryParameterAdmissible (a * s ^ 2) := by
  rcases ha with ⟨c, htwo, hdiag⟩
  refine ⟨c * (s : K), ?_, ?_⟩
  · have hproduct := (IntegerRing K).mul_mem _ _ htwo hs
    convert hproduct using 1 <;> ring
  · have hsSq := (IntegerRing K).pow_mem hs 2
    have hproduct := (IntegerRing K).mul_mem _ _ hdiag hsSq
    convert hproduct using 1
    change
      (c * (s : K)) ^ 2 + (a : K) * (s : K) ^ 2 =
        (c ^ 2 + (a : K)) * (s : K) ^ 2
    ring

/-- A valuation unit and its inverse both belong to the integer ring. -/
theorem valuationUnit_mem_integerRing_and_inv
    (s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    (s : K) ∈ IntegerRing K ∧
      ((s⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
  constructor
  · apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hs]
  · apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, Units.val_inv_eq_inv_val,
      AddValuation.map_inv, hs]
    simp

/-- Multiplication by a valuation-unit square does not change admissibility. -/
theorem isBinaryParameterAdmissible_mul_valuationUnit_square_iff
    (a s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    IsBinaryParameterAdmissible (a * s ^ 2) ↔
      IsBinaryParameterAdmissible a := by
  constructor
  · intro hscaled
    have hinv := (valuationUnit_mem_integerRing_and_inv s hs).2
    have h := hscaled.mul_integral_square (s := s⁻¹) hinv
    convert h using 1
    group
  · intro ha
    exact ha.mul_integral_square
      (valuationUnit_mem_integerRing_and_inv s hs).1

/-- Equal refined unit-square classes have equivalent admissibility. -/
theorem isBinaryParameterAdmissible_iff_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    IsBinaryParameterAdmissible a ↔
      IsBinaryParameterAdmissible b := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) a =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) b at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨z, hz, haz⟩
  rw [mem_valuationUnitSquareSubgroup_iff] at hz
  rcases hz with ⟨s, hs, rfl⟩
  rw [← haz]
  exact (isBinaryParameterAdmissible_mul_valuationUnit_square_iff
    a s hs).symm

/-- The existential class predicate is equivalent to checking any chosen
representative. -/
theorem isBinaryInvariantClassAdmissible_unitSquareClass_iff
    (a : Kˣ) :
    IsBinaryInvariantClassAdmissible (unitSquareClass K a) ↔
      IsBinaryParameterAdmissible a := by
  constructor
  · rintro ⟨b, hbClass, hb⟩
    exact (isBinaryParameterAdmissible_iff_of_unitSquareClass_eq
      hbClass).1 hb
  · intro ha
    exact ⟨a, rfl, ha⟩

/-- Integral square multiplication gives the admissibility half of Beli
2003, Lemma 3.8. -/
theorem isBinaryInvariantClassAdmissible_mul_integral_square
    {a s : Kˣ} (ha :
      IsBinaryInvariantClassAdmissible (unitSquareClass K a))
    (hs : (s : K) ∈ IntegerRing K) :
    IsBinaryInvariantClassAdmissible
      (unitSquareClass K (a * s ^ 2)) := by
  rw [isBinaryInvariantClassAdmissible_unitSquareClass_iff] at ha ⊢
  exact ha.mul_integral_square hs

end BONG

end Bong
