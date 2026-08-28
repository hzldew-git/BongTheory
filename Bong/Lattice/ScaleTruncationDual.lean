/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ScaleTruncation
import Bong.Lattice.ModularParameter

/-!
# Scale truncation and integral duality

This file proves the intrinsic lattice identity underlying O'Meara 93:24.
If `L^r = L ⊓ π^r L♯`, then

`(L♯)^(-r) = π^(-r) L^r`.

The statement is independent of a Jordan splitting.  It is the lattice-level
input for reversing the fundamental invariants of a Jordan chain.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Lattice rescaling distributes over the intersection of full lattices. -/
theorem rescale_inf (a : Kˣ) (L M : Lattice K V) :
    rescale a (inf L M) = inf (rescale a L) (rescale a M) := by
  apply Lattice.ext
  apply Submodule.ext
  intro x
  change x ∈ rescale a (inf L M) ↔
    x ∈ inf (rescale a L) (rescale a M)
  rw [mem_rescale_iff, mem_inf_iff]
  constructor
  · rintro ⟨y, ⟨hyL, hyM⟩, rfl⟩
    exact ⟨smul_mem_rescale a L hyL, smul_mem_rescale a M hyM⟩
  · rintro ⟨hxL, hxM⟩
    rw [mem_rescale_iff] at hxL hxM
    rcases hxL with ⟨y, hyL, hay⟩
    rcases hxM with ⟨z, hzM, haz⟩
    have hyz : y = z := by
      apply smul_right_injective V (Units.ne_zero a)
      exact hay.trans haz.symm
    subst z
    exact ⟨y, ⟨hyL, hzM⟩, hay⟩

/-- Intersection of full lattices is commutative. -/
theorem inf_comm (L M : Lattice K V) : inf L M = inf M L := by
  apply Lattice.ext
  apply Submodule.ext
  intro x
  simp only [toSubmodule_inf, Submodule.mem_inf, and_comm]

/-- Intrinsic duality formula for O'Meara scale truncations:
`(L♯)^(-r) = π^(-r) L^r`. -/
theorem scaleTruncation_dual_neg
    (q : QuadraticSpace K V) (L : Lattice K V) (r : Int) :
    scaleTruncation q (dualLattice q L) (-r) =
      rescale (scaleTruncationUnit (K := K) (-r))
        (scaleTruncation q L r) := by
  let c : Kˣ := scaleTruncationUnit (K := K) (-r)
  let d : Kˣ := scaleTruncationUnit (K := K) r
  have hcdOrder : ordUnit K (c * d) = 0 := by
    simp only [c, d, scaleTruncationUnit, ordUnit_mul,
      ordUnit_uniformizerPowerUnit]
    omega
  have hcdUnit : IsValuationUnit K ((c * d : Kˣ) : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero (K := K) (c * d)).2 hcdOrder
  have hcd : rescale (c * d) (dualLattice q L) = dualLattice q L :=
    rescale_eq_self_of_isValuationUnit (dualLattice q L) (c * d) hcdUnit
  symm
  change rescale c (inf L (rescale d (dualLattice q L))) =
    inf (dualLattice q L) (rescale c (dualLattice q (dualLattice q L)))
  calc
    rescale c (inf L (rescale d (dualLattice q L))) =
        inf (rescale c L) (rescale c (rescale d (dualLattice q L))) :=
      rescale_inf c L (rescale d (dualLattice q L))
    _ = inf (rescale c L) (rescale (c * d) (dualLattice q L)) := by
      rw [rescale_mul]
    _ = inf (rescale c L) (dualLattice q L) := by rw [hcd]
    _ = inf (dualLattice q L) (rescale c L) := inf_comm _ _
    _ = inf (dualLattice q L)
        (rescale c (dualLattice q (dualLattice q L))) := by simp

end Lattice

end Bong
