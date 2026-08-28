/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertDuality

/-!
# M79 Beli 2003, Lemmas 1.2(iii) and 1.3 smoke test
-/

namespace BongTest.M79

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [BeliHilbertCongruenceLaws K]

example (a : Kˣ) (k : Nat) (hk : 0 < k) :
    principalUnitSquareClassSubgroup K k ≤
        quadraticNormSquareClassSubgroup K a ↔
      ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + k :=
  principalUnitSquareClassSubgroup_le_quadraticNorm_iff K a k hk

example (a b : Kˣ) (H : Subgroup (SquareClass K)) :
    quadraticNormSquareClassSubgroup K a ⊓ H ≤
        quadraticNormSquareClassSubgroup K b ↔
      H ≤ quadraticNormSquareClassSubgroup K b ∨
        H ≤ quadraticNormSquareClassSubgroup K (a * b) :=
  quadraticNorm_inf_le_quadraticNorm_iff K a b H

example (a b : Kˣ) (H : Subgroup (SquareClass K)) :
    H ⊓ quadraticNormSquareClassSubgroup K a =
        H ⊓ quadraticNormSquareClassSubgroup K b ↔
      H ≤ quadraticNormSquareClassSubgroup K (a * b) :=
  quadraticNorm_inf_eq_quadraticNorm_inf_iff K a b H

#print axioms Bong.Dyadic.quadraticNorm_inf_le_quadraticNorm_iff
#print axioms Bong.Dyadic.quadraticNorm_inf_eq_quadraticNorm_inf_iff

end

end BongTest.M79
