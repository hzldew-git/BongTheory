/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Lattice.QuadraticValues

/-!
# Integral and universal quadratic lattices

This file formalizes the paper-level meanings of `Q(L) \subseteq O`,
`Q(L) = O`, and `n`-universality.  The definitions use the represented
quadratic-value set itself; the norm-ideal formulation is proved equivalent
and is not built into the meaning of universality.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A scalar is represented by a quadratic lattice. -/
def RepresentsScalar (q : QuadraticSpace K V) (L : Lattice K V) (a : K) : Prop :=
  a ∈ quadraticValueSet q L

/-- A quadratic lattice is integral when all its quadratic values lie in `O`. -/
def IsIntegral (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  quadraticValueSet q L ⊆ (unitIdeal (K := K) : Set K)

/-- A quadratic lattice is universal when its represented value set is exactly `O`. -/
def IsUniversal (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  quadraticValueSet q L = (unitIdeal (K := K) : Set K)

/-- An integral lattice is `n`-universal when it represents every integral
rank-`n` quadratic lattice over the same dyadic field. -/
def IsNUniversal (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  IsIntegral q L ∧
    ∀ {W : Type w} [AddCommGroup W] [Module K W]
      (r : QuadraticSpace K W) (M : Lattice K W),
      Module.finrank K W = n → IsIntegral r M → Represents q r L M

theorem representsScalar_iff (q : QuadraticSpace K V) (L : Lattice K V) (a : K) :
    RepresentsScalar q L a ↔ ∃ x : V, x ∈ L ∧ q.quadratic x = a :=
  mem_quadraticValueSet_iff q L a

theorem isIntegral_iff_forall (q : QuadraticSpace K V) (L : Lattice K V) :
    IsIntegral q L ↔ ∀ x : V, x ∈ L → Dyadic.IsIntegral K (q.quadratic x) := by
  rw [IsIntegral]
  constructor
  · intro h x hx
    rw [← mem_unitIdeal_iff_isIntegral]
    exact h ((mem_quadraticValueSet_iff q L _).2 ⟨x, hx, rfl⟩)
  · intro h a ha
    rw [mem_quadraticValueSet_iff] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact mem_unitIdeal_iff_isIntegral.mpr (h x hx)

/-- Beli's `Q(L) \subseteq O` is equivalent to `nL \subseteq O`. -/
theorem isIntegral_iff_normIdeal_le (q : QuadraticSpace K V) (L : Lattice K V) :
    IsIntegral q L ↔ normIdeal q L ≤ unitIdeal (K := K) := by
  constructor
  · intro h
    apply normIdeal_le_of_quadratic_mem
    intro x hx
    exact h ((mem_quadraticValueSet_iff q L _).2 ⟨x, hx, rfl⟩)
  · intro h a ha
    rw [mem_quadraticValueSet_iff] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact h (quadratic_mem_normIdeal_of_mem q L hx)

theorem IsUniversal.isIntegral {q : QuadraticSpace K V} {L : Lattice K V}
    (h : IsUniversal q L) : IsIntegral q L := by
  rw [IsUniversal] at h
  exact h.le

theorem IsUniversal.representsScalar {q : QuadraticSpace K V} {L : Lattice K V}
    (h : IsUniversal q L) {a : K} (ha : Dyadic.IsIntegral K a) :
    RepresentsScalar q L a := by
  unfold IsUniversal at h
  unfold RepresentsScalar
  rw [h]
  exact mem_unitIdeal_iff_isIntegral.mpr ha

/-- The set equality `Q(L) = O` is equivalent to integrality together with
representation of every integral scalar. -/
theorem isUniversal_iff (q : QuadraticSpace K V) (L : Lattice K V) :
    IsUniversal q L ↔
      IsIntegral q L ∧ ∀ a : K, Dyadic.IsIntegral K a → RepresentsScalar q L a := by
  constructor
  · intro h
    exact ⟨h.isIntegral, fun _ ha ↦ h.representsScalar ha⟩
  · rintro ⟨hintegral, hrepresents⟩
    apply Set.Subset.antisymm hintegral
    intro a ha
    exact hrepresents a (mem_unitIdeal_iff_isIntegral.mp ha)

/-- Integral isometries preserve integrality. -/
theorem isIntegral_iff_of_latticeIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} (f : Isometry q r L M) :
    IsIntegral q L ↔ IsIntegral r M := by
  rw [IsIntegral, IsIntegral, quadraticValueSet_eq_of_latticeIsometry f]

/-- Integral isometries preserve universality. -/
theorem isUniversal_iff_of_latticeIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} (f : Isometry q r L M) :
    IsUniversal q L ↔ IsUniversal r M := by
  rw [IsUniversal, IsUniversal, quadraticValueSet_eq_of_latticeIsometry f]

end Lattice

end Bong
