/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormGenerator
import Bong.Lattice.QuadraticValues

/-!
# Values of norm generators

This file isolates the ideal-theoretic reduction at the start of Beli (2003),
Lemma 3.11.  Relative to a norm generator of value `1`, another lattice vector
is a norm generator exactly when its quadratic value is a valuation unit.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- Two nonzero generators define the same principal ideal exactly when their
quotient is a valuation unit. -/
theorem principalIdeal_eq_iff_isValuationUnit_div (a b : Kˣ) :
    principalIdeal (K := K) (a : K) =
        principalIdeal (K := K) (b : K) ↔
      IsValuationUnit K ((a / b : Kˣ) : K) := by
  constructor
  · intro h
    have hba : ord K (b : K) ≤ ord K (a : K) :=
      (principalIdeal_le_iff_ord_ge (Units.ne_zero a)
        (Units.ne_zero b)).1 h.le
    have hab : ord K (a : K) ≤ ord K (b : K) :=
      (principalIdeal_le_iff_ord_ge (Units.ne_zero b)
        (Units.ne_zero a)).1 h.ge
    have hord : ordUnit K a = ordUnit K b := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      exact le_antisymm hab hba
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    simp [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hord]
  · intro h
    rw [isValuationUnit_iff_ordUnit_eq_zero] at h
    have hord : ordUnit K a = ordUnit K b := by
      simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv] at h
      omega
    apply le_antisymm
    · apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (Units.ne_zero b)).2
      rw [← coe_ordUnit K b, ← coe_ordUnit K a, hord]
    · apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero b) (Units.ne_zero a)).2
      rw [← coe_ordUnit K a, ← coe_ordUnit K b, hord]

/-- Two nonzero elements generate the same principal ideal exactly when
their finite additive valuations agree. -/
theorem principalIdeal_eq_iff_ordUnit_eq (a b : Kˣ) :
    principalIdeal (K := K) (a : K) =
        principalIdeal (K := K) (b : K) ↔
      ordUnit K a = ordUnit K b := by
  rw [principalIdeal_eq_iff_isValuationUnit_div,
    isValuationUnit_iff_ordUnit_eq_zero]
  simp only [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
  omega

/-- The generator of the sum of two nonzero principal ideals has valuation
the minimum of the two generator valuations. -/
theorem ordUnit_eq_min_of_principalIdeal_eq_sup (a b c : Kˣ)
    (h : principalIdeal (K := K) (c : K) =
      principalIdeal (K := K) (a : K) ⊔
        principalIdeal (K := K) (b : K)) :
    ordUnit K c = min (ordUnit K a) (ordUnit K b) := by
  rcases le_total (ordUnit K a) (ordUnit K b) with hab | hba
  · have hideal : principalIdeal (K := K) (b : K) ≤
        principalIdeal (K := K) (a : K) := by
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero b) (Units.ne_zero a)).2
      simpa only [coe_ordUnit] using WithTop.coe_le_coe.mpr hab
    rw [sup_eq_left.mpr hideal] at h
    rw [min_eq_left hab]
    exact (principalIdeal_eq_iff_ordUnit_eq c a).mp h
  · have hideal : principalIdeal (K := K) (a : K) ≤
        principalIdeal (K := K) (b : K) := by
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero a) (Units.ne_zero b)).2
      simpa only [coe_ordUnit] using WithTop.coe_le_coe.mpr hba
    rw [sup_eq_right.mpr hideal] at h
    rw [min_eq_right hba]
    exact (principalIdeal_eq_iff_ordUnit_eq c b).mp h

/-- Comparison with one fixed anisotropic norm generator turns the norm
generator condition into a valuation-unit condition on value ratios. -/
theorem IsNormGenerator.iff_isValuationUnit_valueRatio
    {x y : V} (generator : IsNormGenerator q L x)
    (hx : q.IsAnisotropic x) (hyL : y ∈ L)
    (hy : q.IsAnisotropic y) :
    IsNormGenerator q L y ↔
      IsValuationUnit K
        (((Units.mk0 (q.quadratic y) hy) /
          (Units.mk0 (q.quadratic x) hx) : Kˣ) : K) := by
  rw [← principalIdeal_eq_iff_isValuationUnit_div]
  constructor
  · intro hyGenerator
    exact hyGenerator.normIdeal_eq.symm.trans generator.normIdeal_eq
  · intro hideal
    exact ⟨hyL, generator.normIdeal_eq.trans hideal.symm⟩

/-- With a norm generator of value `1`, norm generators are exactly the
lattice vectors having valuation-unit quadratic value. -/
theorem IsNormGenerator.iff_isValuationUnit_quadratic_of_value_one
    {x y : V} (generator : IsNormGenerator q L x)
    (hx : q.IsAnisotropic x) (hvalue : q.quadratic x = 1)
    (hyL : y ∈ L) (hy : q.IsAnisotropic y) :
    IsNormGenerator q L y ↔ IsValuationUnit K (q.quadratic y) := by
  simpa [hvalue] using
    generator.iff_isValuationUnit_valueRatio hx hyL hy

/-- Scaling a norm generator by a valuation unit preserves the norm-generator
property. -/
theorem IsNormGenerator.smul_valuationUnit
    {x : V} (generator : IsNormGenerator q L x)
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    IsNormGenerator q L ((u : K) • x) := by
  have huIntegral : (u : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hu]
  let uO : IntegerRing K := ⟨(u : K), huIntegral⟩
  constructor
  · exact L.smul_mem uO generator.mem
  · have huSq : IsValuationUnit K ((u ^ 2 : Kˣ) : K) := by
      rw [isValuationUnit_iff_ordUnit_eq_zero,
        ordUnit_pow,
        (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu]
      norm_num
    have hideal := principalIdeal_mul_eq_of_isValuationUnit
      (q.quadratic x) (u ^ 2) huSq
    rw [q.quadratic_smul]
    apply generator.normIdeal_eq.trans
    simpa [mul_comm] using hideal.symm

/-- The scalar values represented by norm generators of `L`. -/
def normGeneratorValueSet (q : QuadraticSpace K V)
    (L : Lattice K V) : Set K :=
  {a | ∃ x : V, IsNormGenerator q L x ∧ q.quadratic x = a}

@[simp]
theorem mem_normGeneratorValueSet_iff
    (q : QuadraticSpace K V) (L : Lattice K V) (a : K) :
    a ∈ normGeneratorValueSet q L ↔
      ∃ x : V, IsNormGenerator q L x ∧ q.quadratic x = a :=
  Iff.rfl

/-- Beli 2003, Lemma 3.11, first reduction: after normalizing one norm
generator to value `1`, norm-generator values are precisely the valuation-unit
part of `Q(L)`. -/
theorem normGeneratorValueSet_eq_quadraticValueSet_inter
    {x : V} (generator : IsNormGenerator q L x)
    (hx : q.IsAnisotropic x) (hvalue : q.quadratic x = 1) :
    normGeneratorValueSet q L =
      quadraticValueSet q L ∩ {a | IsValuationUnit K a} := by
  ext a
  constructor
  · rintro ⟨y, hyGenerator, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (mem_quadraticValueSet_iff q L _).2
        ⟨y, hyGenerator.mem, rfl⟩
    · have hy : q.IsAnisotropic y := by
        intro hyZero
        have hxMem := quadratic_mem_normIdeal_of_mem
          q L generator.mem
        rw [hyGenerator.normIdeal_eq, hyZero, principalIdeal] at hxMem
        exact hx (by simpa using hxMem)
      exact (generator.iff_isValuationUnit_quadratic_of_value_one
        hx hvalue hyGenerator.mem hy).1 hyGenerator
  · rintro ⟨haValue, haUnit⟩
    rcases (mem_quadraticValueSet_iff q L a).1 haValue with
      ⟨y, hyL, hqy⟩
    have haNe : a ≠ 0 := by
      intro ha
      change IsValuationUnit K a at haUnit
      rw [ha, IsValuationUnit, ord_zero] at haUnit
      exact WithTop.top_ne_zero haUnit
    have hy : q.IsAnisotropic y := by
      change q.quadratic y ≠ 0
      rw [hqy]
      exact haNe
    refine ⟨y, ?_, hqy⟩
    apply (generator.iff_isValuationUnit_quadratic_of_value_one
      hx hvalue hyL hy).2
    rwa [hqy]

end Lattice

end Bong
