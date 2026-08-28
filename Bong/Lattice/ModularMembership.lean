/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularScale

/-!
# O'Meara's membership criterion for modular lattices

This file formalizes the local result used in the proof of the modular
splitting theorem: a vector belongs to an `a`-modular lattice exactly when
all of its pairings with the lattice are divisible by `a`.  This is the
content used from O'Meara, Section 82:14a.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- O'Meara 82:14a: membership in an `a`-modular lattice is detected by
pairing divisibility by `a`. -/
theorem IsModular.mem_iff_pairing_mem_principal
    {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}
    (hmodular : IsModular q L a) (x : V) :
    x ∈ L ↔
      ∀ y : V, y ∈ L →
        q.bilin x y ∈ principalIdeal (K := K) (a : K) := by
  constructor
  · intro hx y hy
    exact hmodular.scaleIdeal_le_principal
      (bilin_mem_scaleIdeal_of_mem q L hx hy)
  · intro hpair
    have hdual : ((a⁻¹ : Kˣ) : K) • x ∈ dualLattice q L := by
      rw [mem_dualLattice_iff]
      intro y hy
      have hxy := hpair y hy
      rw [principalIdeal, Submodule.mem_span_singleton] at hxy
      rcases hxy with ⟨c, hc⟩
      have hcField : algebraMap (IntegerRing K) K c * (a : K) =
          q.bilin x y := by
        simpa only [Algebra.smul_def] using hc
      change q.bilin (((a⁻¹ : Kˣ) : K) • x) y ∈ IntegerRing K
      rw [LinearMap.BilinForm.smul_left, ← hcField]
      convert c.property using 1
      simp [mul_comm]
    rw [hmodular, mem_rescale_iff] at hdual
    rcases hdual with ⟨z, hz, hzx⟩
    have hzx' : z = x := by
      apply smul_right_injective V (Units.ne_zero (a⁻¹ : Kˣ))
      exact hzx
    simpa [hzx'] using hz

end Lattice

end Bong
