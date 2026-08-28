/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals
import Bong.Lattice.Isometry

/-!
# Quadratic value sets modulo coefficient ideals

This file packages the notation used in Beli (2003), Section 3.  The set
`quadraticValueSet q L` is `Q(L)`.  Membership in
`integralSquareResidueSet I` means congruence modulo `I` to the square of an
element of the valuation ring, i.e. membership in `𝓞² + I`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The set `Q(L)` of scalar quadratic values represented by a lattice. -/
def quadraticValueSet (q : QuadraticSpace K V) (L : Lattice K V) : Set K :=
  normGenerators q L

theorem mem_quadraticValueSet_iff
    (q : QuadraticSpace K V) (L : Lattice K V) (a : K) :
    a ∈ quadraticValueSet q L ↔
      ∃ x : V, x ∈ L ∧ q.quadratic x = a := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Integral quadratic isometries preserve the represented value set. -/
theorem quadraticValueSet_eq_of_latticeIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) :
    quadraticValueSet r M = quadraticValueSet q L := by
  ext c
  rw [mem_quadraticValueSet_iff, mem_quadraticValueSet_iff]
  constructor
  · rintro ⟨y, hy, hqy⟩
    refine ⟨f.toLinearEquiv.symm y,
      (f.symm.map_mem y).mp hy, ?_⟩
    have h := f.symm.map_quadratic y
    change q.quadratic (f.toLinearEquiv.symm y) = r.quadratic y at h
    exact h.trans hqy
  · rintro ⟨x, hx, hqx⟩
    refine ⟨f.toLinearEquiv x, (f.map_mem x).mp hx, ?_⟩
    rw [f.map_quadratic]
    exact hqx

/-- A scalar is congruent modulo `I` to an integral square. -/
def IsIntegralSquareModulo (I : CoefficientIdeal (K := K)) (a : K) : Prop :=
  ∃ x : IntegerRing K, a - (x : K) ^ 2 ∈ I

/-- Beli's set `𝓞² + I`, expressed by a congruence to an integral square. -/
def integralSquareResidueSet
    (I : CoefficientIdeal (K := K)) : Set K :=
  {a | IsIntegralSquareModulo I a}

@[simp]
theorem mem_integralSquareResidueSet_iff
    (I : CoefficientIdeal (K := K)) (a : K) :
    a ∈ integralSquareResidueSet I ↔
      ∃ x : IntegerRing K, a - (x : K) ^ 2 ∈ I :=
  Iff.rfl

/-- Enlarging the error ideal enlarges the integral-square residue set. -/
theorem integralSquareResidueSet_mono
    {I J : CoefficientIdeal (K := K)} (hIJ : I ≤ J) :
    integralSquareResidueSet I ⊆ integralSquareResidueSet J := by
  rintro a ⟨x, hx⟩
  exact ⟨x, hIJ hx⟩

/-- Every integral square belongs to every integral-square residue set. -/
theorem integral_square_mem_integralSquareResidueSet
    (I : CoefficientIdeal (K := K)) (x : IntegerRing K) :
    (x : K) ^ 2 ∈ integralSquareResidueSet I := by
  exact ⟨x, by simp⟩

end Lattice

end Bong
