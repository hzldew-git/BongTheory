/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69CappedPropagationRight
import Bong.Bong.Beli2019PrefixChange

/-!
# Beli (2019): the full-rank comparison defect

Two good BONGs in the same quadratic space have full value products whose
product is a square.  At the full-rank boundary both alpha caps are infinite,
so the corresponding capped comparison defect is infinite as well.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  {r : QuadraticSpace K W} {P : Lattice K W} {k : Nat}

/-- Replacing a complete left prefix by the complete prefix of another
good BONG in the same quadratic space does not change a capped mixed-prefix
defect.  This endpoint form is used repeatedly in Sections 7 and 9. -/
theorem truncatedPrefixDefect_fullLeft_invariant
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG r P (k + 1)) (epsilon : Kˣ) (j : Nat) :
    b.truncatedPrefixDefect c epsilon (n + 1) j =
      a.truncatedPrefixDefect c epsilon (n + 1) j := by
  rcases BONG.exists_valueProduct_eq_mul_square
    a.toBONG b.toBONG with ⟨p, hp⟩
  have hraw : epsilon * b.toBONG.valueProduct * c.prefixProduct j =
      (epsilon * a.toBONG.valueProduct * c.prefixProduct j) * p ^ 2 := by
    rw [hp]
    ac_rfl
  unfold truncatedPrefixDefect
  rw [a.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
    b.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
    hraw, defectOrder_mul_square, a.prefixAlphaCap_last,
    b.prefixAlphaCap_last]

/-- The capped comparison defect at the common full rank is infinite. -/
theorem truncatedPrefixDefect_full_eq_top
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) :
    a.truncatedPrefixDefect b 1 (n + 1) (n + 1) = ⊤ := by
  unfold truncatedPrefixDefect
  rw [a.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
    b.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
    a.prefixAlphaCap_last, b.prefixAlphaCap_last]
  simp only [one_mul, min_top_right]
  exact a.defectOrder_fullPrefixProduct_mul_eq_top b

end BONG.GoodBONG

end Bong
