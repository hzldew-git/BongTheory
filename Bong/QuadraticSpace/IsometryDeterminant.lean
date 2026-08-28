/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.ReflectionGeneration

/-!
# Determinant sign of a quadratic isometry

Cartan--Dieudonne generation immediately implies that the determinant of
an isometry of a finite-dimensional nondegenerate quadratic space is `1`
or `-1`.  This small interface is useful when separating the two blocks of
an orthogonal product automorphism.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- A reflection word has determinant sign `1` or `-1`. -/
theorem ReflectionWord.det_eval_eq_one_or_neg_one
    [FiniteDimensional K V] (w : ReflectionWord q) :
    LinearEquiv.det w.eval.toLinearEquiv = 1 ∨
      LinearEquiv.det w.eval.toLinearEquiv = (-1 : Kˣ) := by
  induction w with
  | nil =>
      left
      exact LinearEquiv.det_refl
  | snoc w x hx ih =>
      rw [ReflectionWord.eval_snoc]
      change LinearEquiv.det
          (w.eval.toLinearEquiv.trans
            (q.reflectionLinearEquiv x hx)) = 1 ∨
        LinearEquiv.det
          (w.eval.toLinearEquiv.trans
            (q.reflectionLinearEquiv x hx)) = (-1 : Kˣ)
      rw [LinearEquiv.det_trans, q.det_reflectionLinearEquiv hx]
      rcases ih with h | h
      · right
        rw [h]
        norm_num
      · left
        rw [h]
        norm_num

/-- The determinant of every finite-dimensional quadratic-space isometry
is one of the two signs. -/
theorem Isometry.det_eq_one_or_neg_one
    [FiniteDimensional K V] (f : Isometry q q) :
    LinearEquiv.det f.toLinearEquiv = 1 ∨
      LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ) := by
  obtain ⟨w, hw⟩ := exists_reflectionWord f
  rw [← hw]
  exact w.det_eval_eq_one_or_neg_one

end QuadraticSpace

end Bong
