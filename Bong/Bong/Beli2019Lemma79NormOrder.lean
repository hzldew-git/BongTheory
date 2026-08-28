/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIMiddle

/-!
# Beli (2019), Lemma 7.9: strict norm ideals and first orders

The hypothesis `n(K) ⊊ n(M)` is most useful in the coordinate proof as the
integer inequality `R₁ + 1 ≤ T₁`.  This file proves that translation from
the concrete power-ideal model of norm ideals.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

end Lattice

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {m n : Nat}

/-- Proper containment of nonempty BONG norm ideals is equivalent to strict
comparison of their first orders. -/
theorem normIdeal_lt_iff_order_zero_lt
    (a : BONG V q L (m + 1)) (c : BONG V q N (n + 1)) :
    Lattice.normIdeal q N < Lattice.normIdeal q L ↔
      a.order 0 < c.order 0 := by
  rw [a.normIdeal_eq_powerIdeal_order_zero,
    c.normIdeal_eq_powerIdeal_order_zero,
    Lattice.powerIdeal_lt_iff]

/-- The discrete form of the strict norm-ideal hypothesis used at the left
boundary in Lemma 7.9(i). -/
theorem order_zero_add_one_le_of_normIdeal_lt
    (a : BONG V q L (m + 1)) (c : BONG V q N (n + 1))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    a.order 0 + 1 ≤ c.order 0 := by
  have hstrict := (a.normIdeal_lt_iff_order_zero_lt c).mp hnorm
  omega

end BONG

end Bong
