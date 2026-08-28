/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.ReflectionGeneration
import Bong.QuadraticSpace.SpinorNormReflectionMultiplication

/-!
# Multiplicativity of the Wall spinor norm

The determinant of the Wall form gives a multiplicative square class under
composition of isometries.  We prove this from Wall's one-reflection
reduction and reflection generation.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticSpace K V}

private theorem spinorNorm_trans_reflectionWord
    (f : Isometry q q) (w : ReflectionWord q) :
    spinorNorm (f.trans w.eval) = spinorNorm f * spinorNorm w.eval := by
  induction w generalizing f with
  | nil =>
      rw [ReflectionWord.eval_nil, Isometry.trans_refl,
        spinorNorm_refl, mul_one]
  | snoc w x hx ih =>
      have hcomp :
          f.trans (ReflectionWord.snoc w x hx).eval =
            reflectAfter (f.trans w.eval) x hx := by
        apply Isometry.ext
        intro y
        rfl
      rw [hcomp,
        spinorNorm_reflectAfter (f.trans w.eval) x hx, ih,
        ReflectionWord.eval_snoc,
        spinorNorm_reflectAfter w.eval x hx, mul_assoc]

/-- The Wall spinor norm is multiplicative under composition. -/
theorem spinorNorm_trans (f g : Isometry q q) :
    spinorNorm (f.trans g) = spinorNorm f * spinorNorm g := by
  obtain ⟨w, hw⟩ := exists_reflectionWord g
  rw [← hw]
  exact spinorNorm_trans_reflectionWord f w

end QuadraticSpace

end Bong
