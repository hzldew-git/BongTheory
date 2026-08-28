/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Modular
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Integral basis lattices under scalar changes

An ambient basis may be multiplied by one field unit globally, or by a
valuation unit in each coordinate.  The first operation rescales its integral
basis lattice; the second does not change that lattice.
-/

namespace Bong

open Dyadic
open Module
open scoped Pointwise

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- A nonzero field element lying in the valuation ring has nonnegative
integral order. -/
theorem ordUnit_nonneg_of_mem_integerRing (a : Kˣ)
    (ha : (a : K) ∈ IntegerRing K) : 0 ≤ ordUnit K a := by
  have h := (mem_integerRing_iff K).1 ha
  change (0 : WithTop Int) ≤ ord K (a : K) at h
  rw [← coe_ordUnit] at h
  exact_mod_cast h

/-- Globally scaling a field basis scales its integral basis lattice. -/
theorem rescale_basisLattice {ι : Type w} [Finite ι]
    (a : Kˣ) (b : Basis ι K V) :
    rescale a (basisLattice b) = basisLattice (a • b) := by
  apply Lattice.ext
  ext x
  constructor
  · intro hx
    change x ∈ rescale a (basisLattice b) at hx
    rw [mem_rescale_iff] at hx
    rcases hx with ⟨y, hy, rfl⟩
    change y ∈ Submodule.span (IntegerRing K) (Set.range b) at hy
    refine Submodule.span_induction
      (p := fun y _ => (a : K) • y ∈
        Submodule.span (IntegerRing K) (Set.range (a • b))) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, Basis.smul_apply a b i⟩
    · simp
    · intro y z _ _ hy hz
      simpa only [smul_add] using
        (Submodule.span (IntegerRing K)
          (Set.range (a • b))).add_mem hy hz
    · intro c y _ hy
      have hmem := (Submodule.span (IntegerRing K)
        (Set.range (a • b))).smul_mem c hy
      change (c : K) • ((a : K) • y) ∈
        Submodule.span (IntegerRing K) (Set.range (a • b)) at hmem
      change (a : K) • ((c : K) • y) ∈
        Submodule.span (IntegerRing K) (Set.range (a • b))
      rw [smul_comm (a : K) (c : K) y]
      exact hmem
  · intro hx
    change x ∈ Submodule.span (IntegerRing K) (Set.range (a • b)) at hx
    refine Submodule.span_induction
      (p := fun x _ => x ∈ rescale a (basisLattice b)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      rw [Basis.smul_apply]
      exact smul_mem_rescale a (basisLattice b)
        (Submodule.subset_span ⟨i, rfl⟩)
    · exact (rescale a (basisLattice b)).zero_mem
    · intro y z _ _ hy hz
      exact (rescale a (basisLattice b)).add_mem hy hz
    · intro c y _ hy
      exact (rescale a (basisLattice b)).smul_mem c hy

/-- Multiplying each basis vector by a valuation unit leaves its integral
basis lattice unchanged. -/
theorem basisLattice_unitsSMul_eq {ι : Type w} [Finite ι]
    (b : Basis ι K V) (a : ι → Kˣ)
    (ha : ∀ i, IsValuationUnit K (a i : K)) :
    basisLattice (b.unitsSMul a) = basisLattice b := by
  apply Lattice.ext
  change Submodule.span (IntegerRing K)
      (Set.range (b.unitsSMul a)) =
    Submodule.span (IntegerRing K) (Set.range b)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Basis.unitsSMul_apply]
    let aO : IntegerRing K :=
      ⟨(a i : K), (mem_integerRing_iff K).2 (by
        show 0 ≤ ord K (a i : K)
        rw [ha i])⟩
    have hmem := (Submodule.span (IntegerRing K)
      (Set.range b)).smul_mem aO
        (Submodule.subset_span ⟨i, rfl⟩)
    change (a i : K) • b i ∈
      Submodule.span (IntegerRing K) (Set.range b) at hmem
    exact hmem
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have haInv : IsValuationUnit K ((a i)⁻¹ : K) := by
      rw [IsValuationUnit, AddValuation.map_inv, ha i]
      rfl
    let aInvO : IntegerRing K :=
      ⟨((a i)⁻¹ : K), (mem_integerRing_iff K).2 (by
        show 0 ≤ ord K ((a i)⁻¹ : K)
        rw [haInv])⟩
    have hmem := (Submodule.span (IntegerRing K)
      (Set.range (b.unitsSMul a))).smul_mem aInvO
        (Submodule.subset_span ⟨i, rfl⟩)
    rw [Basis.unitsSMul_apply] at hmem
    change ((a i : K)⁻¹) • ((a i : K) • b i) ∈
      Submodule.span (IntegerRing K)
        (Set.range (b.unitsSMul a)) at hmem
    simpa [smul_smul, Units.ne_zero] using hmem

/-- Membership in a basis lattice is equivalent to integrality of all field
coordinates. -/
theorem mem_basisLattice_iff_repr_mem_integerRing
    {ι : Type w} [Finite ι] (b : Basis ι K V) (x : V) :
    x ∈ basisLattice b ↔ ∀ i, b.repr x i ∈ IntegerRing K := by
  rw [show x ∈ basisLattice b ↔
      x ∈ Submodule.span (IntegerRing K) (Set.range b) by rfl,
    b.mem_span_iff_repr_mem (IntegerRing K)]
  constructor
  · intro h i
    rcases h i with ⟨a, ha⟩
    change b.repr x i ∈ IntegerRing K
    rw [← ha]
    exact a.property
  · intro h i
    exact ⟨⟨b.repr x i, h i⟩, rfl⟩

end Lattice

end Bong
