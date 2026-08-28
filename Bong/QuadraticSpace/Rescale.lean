/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Basic

/-!
# Rescaling quadratic spaces

Multiplying a nondegenerate symmetric bilinear form by a nonzero field unit
again gives a quadratic space.  This is the ambient-space operation behind
the scaled binary lattices used throughout Beli's classification.
-/

namespace Bong

namespace QuadraticSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Rescale a quadratic space by a nonzero field scalar. -/
def rescaleUnit (a : Kˣ) (q : QuadraticSpace K V) : QuadraticSpace K V where
  bilin := (a : K) • q.bilin
  isSymm := by
    constructor
    intro x y
    change (a : K) * q.bilin x y = (a : K) * q.bilin y x
    rw [q.isSymm.eq]
  nondegenerate := by
    constructor
    · intro x hx
      apply q.nondegenerate.1 x
      intro y
      have h := hx y
      change (a : K) * q.bilin x y = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero a)
    · intro y hy
      apply q.nondegenerate.2 y
      intro x
      have h := hy x
      change (a : K) * q.bilin x y = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero a)

@[simp]
theorem rescaleUnit_bilin_apply (a : Kˣ) (q : QuadraticSpace K V) (x y : V) :
    (rescaleUnit a q).bilin x y = (a : K) * q.bilin x y :=
  rfl

@[simp]
theorem rescaleUnit_quadratic (a : Kˣ) (q : QuadraticSpace K V) (x : V) :
    (rescaleUnit a q).quadratic x = (a : K) * q.quadratic x :=
  rfl

end QuadraticSpace

end Bong
