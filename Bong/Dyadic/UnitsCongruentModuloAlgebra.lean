/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328Conditions

/-!
# Algebra of square-class congruence modulo a coefficient ideal

The determinant congruence in O'Meara 93:28 is unchanged by replacing either
representative by a valuation-unit square multiple, and a common nonzero
factor cancels.  These elementary facts are used when a prefix determinant
is split into head and tail factors.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Congruence modulo a smaller coefficient ideal implies congruence modulo
every larger coefficient ideal. -/
theorem UnitsCongruentModulo.mono
    {x y : Kˣ} {I J : Lattice.CoefficientIdeal (K := K)}
    (h : UnitsCongruentModulo x y I) (hIJ : I ≤ J) :
    UnitsCongruentModulo x y J := by
  rcases h with ⟨s, hs⟩
  exact ⟨s, hIJ hs⟩

/-- If a representative differs from one by an element of `I`, then its
refined square class is congruent to one modulo `I`.  The inverse of the
representative is the square multiplier which puts the quotient in the
orientation used by `UnitsCongruentModulo`. -/
theorem unitsCongruentModulo_one_of_sub_one_mem
    (x : Kˣ) (I : Lattice.CoefficientIdeal (K := K))
    (hx : (x : K) - 1 ∈ I) :
    UnitsCongruentModulo x (1 : Kˣ) I := by
  refine ⟨x⁻¹, ?_⟩
  convert hx using 1
  simp only [Units.val_one, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero x]

/-- If a nonzero scalar is the negative of a valuation-unit square modulo
`I`, then its refined square class is congruent to `-1` modulo `I`. -/
theorem unitsCongruentModulo_neg_one_of_add_sq_mem
    (d t : Kˣ) (I : Lattice.CoefficientIdeal (K := K))
    (hd : IsValuationUnit K (d : K))
    (h : (d : K) + (t : K) ^ 2 ∈ I) :
    UnitsCongruentModulo d (-1 : Kˣ) I := by
  have hdInvIntegral : Dyadic.IsIntegral K ((d : K)⁻¹) := by
    rw [Dyadic.IsIntegral, AddValuation.map_inv, hd]
    simp
  let dInvO : IntegerRing K := ⟨(d : K)⁻¹,
    (mem_integerRing_iff K).2 hdInvIntegral⟩
  have hmul := I.smul_mem dInvO (I.neg_mem h)
  change (d : K)⁻¹ * (-((d : K) + (t : K) ^ 2)) ∈ I at hmul
  refine ⟨t⁻¹, ?_⟩
  convert hmul using 1
  simp only [Units.val_neg, Units.val_one, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero d, Units.ne_zero t]
  ring

/-- Equality in the refined unit square-class group has an actual square
multiplier representative. -/
theorem exists_square_mul_eq_of_unitSquareClass_eq
    (x y : Kˣ) (h : unitSquareClass K x = unitSquareClass K y) :
    ∃ s : Kˣ, x * s ^ 2 = y := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) x =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) y at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hxy⟩
  rw [mem_valuationUnitSquareSubgroup_iff] at hz
  rcases hz with ⟨s, _, rfl⟩
  exact ⟨s, hxy⟩

/-- Square-class congruence is independent of the representatives chosen in
the refined determinant classes. -/
theorem unitsCongruentModulo_of_unitSquareClass_eq
    (x x' y y' : Kˣ) (I : Lattice.CoefficientIdeal (K := K))
    (hx : unitSquareClass K x = unitSquareClass K x')
    (hy : unitSquareClass K y = unitSquareClass K y')
    (h : UnitsCongruentModulo x y I) :
    UnitsCongruentModulo x' y' I := by
  rcases exists_square_mul_eq_of_unitSquareClass_eq x x' hx with ⟨u, hu⟩
  rcases exists_square_mul_eq_of_unitSquareClass_eq y y' hy with ⟨v, hv⟩
  rcases h with ⟨s, hs⟩
  refine ⟨s * v / u, ?_⟩
  have huK := congrArg (fun z : Kˣ => (z : K)) hu
  have hvK := congrArg (fun z : Kˣ => (z : K)) hv
  rw [← huK, ← hvK]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_div_eq_div_val]
  convert hs using 1
  field_simp [Units.ne_zero x, Units.ne_zero y, Units.ne_zero s,
    Units.ne_zero u, Units.ne_zero v]
  <;> ring

/-- Representative independence, in equivalence form. -/
theorem unitsCongruentModulo_congr_unitSquareClass_iff
    (x x' y y' : Kˣ) (I : Lattice.CoefficientIdeal (K := K))
    (hx : unitSquareClass K x = unitSquareClass K x')
    (hy : unitSquareClass K y = unitSquareClass K y') :
    UnitsCongruentModulo x y I ↔ UnitsCongruentModulo x' y' I := by
  constructor
  · exact unitsCongruentModulo_of_unitSquareClass_eq x x' y y' I hx hy
  · exact unitsCongruentModulo_of_unitSquareClass_eq x' x y' y I
      hx.symm hy.symm

/-- A common nonzero determinant factor cancels from O'Meara's congruence. -/
theorem unitsCongruentModulo_mul_left_iff
    (a x y : Kˣ) (I : Lattice.CoefficientIdeal (K := K)) :
    UnitsCongruentModulo (a * x) (a * y) I ↔
      UnitsCongruentModulo x y I := by
  constructor <;> rintro ⟨s, hs⟩ <;> refine ⟨s, ?_⟩
  · simp only [Units.val_mul] at hs
    convert hs using 1
    field_simp [Units.ne_zero a, Units.ne_zero x, Units.ne_zero y,
      Units.ne_zero s]
    <;> ring
  · simp only [Units.val_mul]
    convert hs using 1
    field_simp [Units.ne_zero a, Units.ne_zero x, Units.ne_zero y,
      Units.ne_zero s]
    <;> ring

/-- Square-class congruences may be multiplied when the modulus is an
integral coefficient ideal.  This is the multiplicative algebra used for
orthogonal determinant blocks. -/
theorem unitsCongruentModulo_mul
    {x₁ y₁ x₂ y₂ : Kˣ} {I : Lattice.CoefficientIdeal (K := K)}
    (hI : I ≤ Lattice.unitIdeal (K := K))
    (h₁ : UnitsCongruentModulo x₁ y₁ I)
    (h₂ : UnitsCongruentModulo x₂ y₂ I) :
    UnitsCongruentModulo (x₁ * x₂) (y₁ * y₂) I := by
  rcases h₁ with ⟨s₁, hs₁⟩
  rcases h₂ with ⟨s₂, hs₂⟩
  let e₁ : K := (y₁ : K) / (x₁ : K) / (s₁ : K) ^ 2 - 1
  let e₂ : K := (y₂ : K) / (x₂ : K) / (s₂ : K) ^ 2 - 1
  have he₁ : e₁ ∈ I := by simpa only [e₁] using hs₁
  have he₂ : e₂ ∈ I := by simpa only [e₂] using hs₂
  have he₁Integral : Dyadic.IsIntegral K e₁ :=
    (Lattice.mem_unitIdeal_iff_isIntegral (K := K)).1 (hI he₁)
  let e₁O : IntegerRing K :=
    ⟨e₁, (mem_integerRing_iff K).2 he₁Integral⟩
  have he₁e₂ : e₁ * e₂ ∈ I := by
    have h := I.smul_mem e₁O he₂
    change e₁ * e₂ ∈ I at h
    exact h
  have hsum : e₁ + e₂ + e₁ * e₂ ∈ I :=
    I.add_mem (I.add_mem he₁ he₂) he₁e₂
  refine ⟨s₁ * s₂, ?_⟩
  convert hsum using 1
  simp only [e₁, e₂, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp [Units.ne_zero x₁, Units.ne_zero y₁,
    Units.ne_zero x₂, Units.ne_zero y₂,
    Units.ne_zero s₁, Units.ne_zero s₂]
  ring

/-- Inverting both representatives reverses the arguments but leaves the
normalized quotient unchanged. -/
theorem unitsCongruentModulo_inv_swap_iff
    (x y : Kˣ) (I : Lattice.CoefficientIdeal (K := K)) :
    UnitsCongruentModulo x⁻¹ y⁻¹ I ↔
      UnitsCongruentModulo y x I := by
  constructor <;> rintro ⟨s, hs⟩ <;> refine ⟨s, ?_⟩
  · convert hs using 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero x, Units.ne_zero y, Units.ne_zero s]
  · convert hs using 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero x, Units.ne_zero y, Units.ne_zero s]

end BONG.GoodBONG

end Bong
