/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionFourInvariants

/-!
# Domination for two self-prefix defects

This file records the endpoint-safe form of the domination principle used
when two self-prefix defects are combined into a mixed-prefix defect.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Two self-prefix defects dominate the mixed-prefix defect obtained by
multiplying their signs.  The proof retains both endpoint alpha caps. -/
theorem truncatedPrefixDefect_selfPrefixes_domination
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon eta : Kˣ) (i j : Nat) :
    min (a.truncatedPrefixDefect a epsilon 0 i)
        (b.truncatedPrefixDefect b eta 0 j) ≤
      a.truncatedPrefixDefect b (epsilon * eta) i j := by
  have hdefect :
      min (a.truncatedPrefixDefect a epsilon 0 i)
          (b.truncatedPrefixDefect b eta 0 j) ≤
        defectOrder (K := K)
          ((epsilon * eta) * a.prefixProduct i * b.prefixProduct j) := by
    calc
      min (a.truncatedPrefixDefect a epsilon 0 i)
            (b.truncatedPrefixDefect b eta 0 j) ≤
          min
            (defectOrder (K := K)
              (epsilon * a.prefixProduct 0 * a.prefixProduct i))
            (defectOrder (K := K)
              (eta * b.prefixProduct 0 * b.prefixProduct j)) :=
        min_le_min
          (a.truncatedPrefixDefect_le_defect a epsilon 0 i)
          (b.truncatedPrefixDefect_le_defect b eta 0 j)
      _ ≤ defectOrder (K := K)
          ((epsilon * a.prefixProduct 0 * a.prefixProduct i) *
            (eta * b.prefixProduct 0 * b.prefixProduct j)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          ((epsilon * eta) * a.prefixProduct i * b.prefixProduct j) := by
        apply congrArg (defectOrder (K := K))
        simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
        ac_rfl
  have hleft :
      min (a.truncatedPrefixDefect a epsilon 0 i)
          (b.truncatedPrefixDefect b eta 0 j) ≤ a.prefixAlphaCap i :=
    (min_le_left _ _).trans
      (a.truncatedPrefixDefect_le_rightCap a epsilon 0 i)
  have hright :
      min (a.truncatedPrefixDefect a epsilon 0 i)
          (b.truncatedPrefixDefect b eta 0 j) ≤ b.prefixAlphaCap j :=
    (min_le_right _ _).trans
      (b.truncatedPrefixDefect_le_rightCap b eta 0 j)
  change _ ≤ min _ (min (a.prefixAlphaCap i) (b.prefixAlphaCap j))
  exact le_min hdefect (le_min hleft hright)

end BONG.GoodBONG

end Bong
