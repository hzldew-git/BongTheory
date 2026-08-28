/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Basic

/-!
# Orthogonal sums and scaled lines

Coordinate-free orthogonal sums and the one-dimensional form `[a]`.
-/

namespace Bong

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- The orthogonal sum of two quadratic spaces. -/
def orthogonalSum (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    QuadraticSpace K (V × W) where
  bilin := LinearMap.mk₂ K
    (fun x y => q.bilin x.1 y.1 + r.bilin x.2 y.2)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
  isSymm := ⟨by
    intro x y
    simp only [LinearMap.mk₂_apply]
    rw [q.isSymm.eq x.1 y.1, r.isSymm.eq x.2 y.2]
  ⟩
  nondegenerate := by
    constructor
    · intro x hx
      apply Prod.ext
      · apply q.nondegenerate.1 x.1
        intro y
        have h := hx (y, 0)
        simpa only [LinearMap.mk₂_apply, Prod.fst_zero, Prod.snd_zero,
          map_zero, LinearMap.zero_apply, add_zero] using h
      · apply r.nondegenerate.1 x.2
        intro y
        have h := hx (0, y)
        simpa only [LinearMap.mk₂_apply, Prod.fst_zero, Prod.snd_zero,
          map_zero, LinearMap.zero_apply, zero_add] using h
    · intro x hx
      apply Prod.ext
      · apply q.nondegenerate.2 x.1
        intro y
        have h := hx (y, 0)
        simpa only [LinearMap.mk₂_apply, Prod.fst_zero, Prod.snd_zero,
          map_zero, LinearMap.zero_apply, add_zero] using h
      · apply r.nondegenerate.2 x.2
        intro y
        have h := hx (0, y)
        simpa only [LinearMap.mk₂_apply, Prod.fst_zero, Prod.snd_zero,
          map_zero, LinearMap.zero_apply, zero_add] using h

@[simp]
theorem orthogonalSum_bilin_apply
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (x y : V × W) :
    (orthogonalSum q r).bilin x y =
      q.bilin x.1 y.1 + r.bilin x.2 y.2 :=
  rfl

@[simp]
theorem orthogonalSum_quadratic_apply
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (x : V × W) :
    (orthogonalSum q r).quadratic x = q.quadratic x.1 + r.quadratic x.2 :=
  rfl

/-- The one-dimensional form `[a]`. -/
def scaledLine (a : Kˣ) : QuadraticSpace K K where
  bilin := LinearMap.mk₂ K (fun x y => (a : K) * x * y)
    (by intros; ring)
    (by intros; simp; ring)
    (by intros; ring)
    (by intros; simp; ring)
  isSymm := ⟨by
    intro x y
    simp only [LinearMap.mk₂_apply]
    ring
  ⟩
  nondegenerate := by
    constructor <;> intro x hx
    · have h := hx 1
      simp only [LinearMap.mk₂_apply, mul_one] at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero a)
    · have h := hx 1
      simp only [LinearMap.mk₂_apply, mul_one] at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero a)

@[simp]
theorem scaledLine_bilin_apply (a : Kˣ) (x y : K) :
    (scaledLine a).bilin x y = (a : K) * x * y :=
  rfl

@[simp]
theorem scaledLine_quadratic_apply (a : Kˣ) (x : K) :
    (scaledLine a).quadratic x = (a : K) * x ^ 2 := by
  change (a : K) * x * x = (a : K) * x ^ 2
  simp [pow_two, mul_assoc]

end QuadraticSpace

end Bong
