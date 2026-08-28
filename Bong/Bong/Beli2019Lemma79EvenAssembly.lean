/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenCappedLeft
import Bong.Bong.DefectArithmetic

/-!
# Beli (2019), Lemma 7.9(ii): assembling an even prefix

The product of the two equally signed self prefixes differs from the
comparison prefix only by the square of the sign.  Defect domination and
the two endpoint caps therefore combine lower bounds for the two capped
self-prefix defects into condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The minimum of two equally signed capped self-prefix defects is bounded
by the corresponding comparison-prefix defect. -/
theorem min_alternatingSelfCapped_le_comparison
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : Nat) :
    min
        (b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i)
        (c.truncatedPrefixDefect c ((-1) ^ (i / 2)) 0 i) ≤
      b.truncatedPrefixDefect c 1 i i := by
  let sign : Kˣ := (-1) ^ (i / 2)
  have hraw :
      min
          (b.truncatedPrefixDefect b sign 0 i)
          (c.truncatedPrefixDefect c sign 0 i) ≤
        defectOrder (K := K)
          ((1 : Kˣ) * b.prefixProduct i * c.prefixProduct i) := by
    calc
      min
          (b.truncatedPrefixDefect b sign 0 i)
          (c.truncatedPrefixDefect c sign 0 i) ≤
          min
            (defectOrder (K := K)
              (sign * b.prefixProduct 0 * b.prefixProduct i))
            (defectOrder (K := K)
              (sign * c.prefixProduct 0 * c.prefixProduct i)) :=
        min_le_min
          (b.truncatedPrefixDefect_le_defect b sign 0 i)
          (c.truncatedPrefixDefect_le_defect c sign 0 i)
      _ ≤ defectOrder (K := K)
          ((sign * b.prefixProduct 0 * b.prefixProduct i) *
            (sign * c.prefixProduct 0 * c.prefixProduct i)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          ((1 : Kˣ) * b.prefixProduct i * c.prefixProduct i) := by
        apply congrArg (defectOrder (K := K))
        simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero,
          mul_one, one_mul]
        dsimp only [sign]
        have hsign :
            ((-1 : Kˣ) ^ (i / 2)) * ((-1 : Kˣ) ^ (i / 2)) = 1 := by
          rw [← pow_add, show i / 2 + i / 2 = 2 * (i / 2) by omega,
            pow_mul]
          norm_num
        calc
          _ = (((-1 : Kˣ) ^ (i / 2)) * ((-1 : Kˣ) ^ (i / 2))) *
              (b.toBONG.prefixProduct i * c.toBONG.prefixProduct i) := by
            ac_rfl
          _ = b.toBONG.prefixProduct i * c.toBONG.prefixProduct i := by
            rw [hsign, one_mul]
  have hleft :
      min
          (b.truncatedPrefixDefect b sign 0 i)
          (c.truncatedPrefixDefect c sign 0 i) ≤
        b.prefixAlphaCap i :=
    (min_le_left _ _).trans
      (b.truncatedPrefixDefect_le_rightCap b sign 0 i)
  have hright :
      min
          (b.truncatedPrefixDefect b sign 0 i)
          (c.truncatedPrefixDefect c sign 0 i) ≤
        c.prefixAlphaCap i :=
    (min_le_right _ _).trans
      (c.truncatedPrefixDefect_le_rightCap c sign 0 i)
  change min _ _ ≤ min _ (min (b.prefixAlphaCap i) (c.prefixAlphaCap i))
  exact le_min hraw (le_min hleft hright)

/-- If both capped self-prefix estimates in the even-coordinate argument
hold, then condition 2.1(ii) holds at that coordinate. -/
theorem lemma79_ii_of_even_selfCapped_bounds
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsource : (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val)
    (htarget : (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  exact (le_min hsource htarget).trans
    (min_alternatingSelfCapped_le_comparison b c i.val)

end BONG.GoodBONG

end Bong
