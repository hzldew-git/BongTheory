/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormGeneratorValues
import Bong.Lattice.NormRescale

/-!
# Order bounds from inclusions of norm ideals

This file converts lattice inclusions into the finite valuation inequalities
used for norm generators in Beli's local Jordan calculations.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

namespace Lattice

/-- Inclusion of lattices reverses the finite orders of generators of their
norm ideals. -/
theorem ordUnit_normIdealGenerator_antitone
    (hLM : L ≤ M) (a b : Kˣ)
    (ha : normIdeal q L = principalIdeal (K := K) (a : K))
    (hb : normIdeal q M = principalIdeal (K := K) (b : K)) :
    ordUnit K b ≤ ordUnit K a := by
  have hideal : principalIdeal (K := K) (a : K) ≤
      principalIdeal (K := K) (b : K) := by
    rw [← ha, ← hb]
    exact normIdeal_mono q hLM
  have hord := (principalIdeal_le_iff_ord_ge
    (Units.ne_zero a) (Units.ne_zero b)).mp hideal
  apply WithTop.coe_le_coe.mp
  simpa only [coe_ordUnit] using hord

/-- If `c M ≤ L`, then the norm order of `L` is bounded above by the norm
order of `M` plus twice the order of `c`. -/
theorem ordUnit_normIdealGenerator_le_add_two_mul_of_rescale_le
    (c : Kˣ) (hML : rescale c M ≤ L)
    (hMpos : 0 < finrank K V) (a b : Kˣ)
    (ha : normIdeal q L = principalIdeal (K := K) (a : K))
    (hb : normIdeal q M = principalIdeal (K := K) (b : K)) :
    ordUnit K a ≤ ordUnit K b + 2 * ordUnit K c := by
  obtain ⟨x, hx, hxAnisotropic⟩ :=
    exists_isNormGenerator_of_finrank_pos q M hMpos
  let d : Kˣ := Units.mk0 (q.quadratic x) hxAnisotropic
  have hd : normIdeal q M = principalIdeal (K := K) (d : K) := by
    exact hx.normIdeal_eq
  have hdb : ordUnit K d = ordUnit K b :=
    (principalIdeal_eq_iff_ordUnit_eq d b).mp (hd.symm.trans hb)
  have hxScaled := hx.rescale c
  have hxScaledAnisotropic : q.IsAnisotropic ((c : K) • x) := by
    intro hzero
    rw [q.quadratic_smul] at hzero
    exact hxAnisotropic (mul_eq_zero.mp hzero |>.resolve_left
      (pow_ne_zero 2 (Units.ne_zero c)))
  let e : Kˣ := Units.mk0
    (q.quadratic ((c : K) • x)) hxScaledAnisotropic
  have he : normIdeal q (rescale c M) =
      principalIdeal (K := K) (e : K) := by
    exact hxScaled.normIdeal_eq
  have heq : e = c ^ 2 * d := by
    apply Units.ext
    change q.quadratic ((c : K) • x) =
      (c : K) ^ 2 * q.quadratic x
    exact q.quadratic_smul (c : K) x
  have horder : ordUnit K a ≤ ordUnit K e :=
    ordUnit_normIdealGenerator_antitone hML e a he ha
  rw [heq, ordUnit_mul, ordUnit_pow, hdb] at horder
  omega

end Lattice
end Bong
