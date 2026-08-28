/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddOrder
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Lemma 7.9(ii), case 8: separated odd prefixes

For odd `i`, the two alternating self-prefix scalars multiply to `-1`.
If their capped defects differ, sharp defect multiplication therefore
bounds the mixed primary defect by the central one.  This is the formal
content of lines 5953--5957 before the numerical order estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Unequal odd-index self-prefix defects force the mixed primary defect
to be no larger than the target self-prefix defect. -/
theorem caseEight_gapTwo_odd_mixedDefect_le_of_comparisonPrefix_ne
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (hiOdd : Odd i.val)
    (central : WithTop Rat)
    (htarget : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) = central)
    (hcomparisonNe : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) ≠ central) :
    b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) <= central := by
  let target := b.truncatedPrefixDefect b
    ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1)
  let comparison := c.truncatedPrefixDefect c
    ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1)
  have hne : target ≠ comparison := by
    intro heq
    apply hcomparisonNe
    calc
      comparison = target := heq.symm
      _ = central := htarget
  have hsum : (i.val + 1) / 2 + (i.val - 1) / 2 = i.val := by
    rcases hiOdd with ⟨d, hd⟩
    omega
  have hscalar :
      ((-1 : Kˣ) ^ ((i.val + 1) / 2)) *
          ((-1) ^ ((i.val - 1) / 2)) = -1 := by
    calc
      ((-1 : Kˣ) ^ ((i.val + 1) / 2)) *
          ((-1) ^ ((i.val - 1) / 2)) =
          (-1) ^ ((i.val + 1) / 2 + (i.val - 1) / 2) := by
            rw [pow_add]
      _ = (-1) ^ i.val := by rw [hsum]
      _ = -1 := hiOdd.neg_one_pow
  rcases lt_or_gt_of_ne hne with htargetLt | hcomparisonLt
  · have hseparation : b.truncatedPrefixDefect b
        ((-1) ^ ((i.val + 1) / 2)) (i.val + 1) 0 <
      b.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) := by
      rw [b.truncatedPrefixDefect_comm b
          ((-1) ^ ((i.val + 1) / 2)) (i.val + 1) 0,
        b.truncatedPrefixDefect_zero_left_eq_self c
          ((-1) ^ ((i.val - 1) / 2)) (i.val - 1)]
      exact htargetLt
    have hsharp := b.truncatedPrefixDefect_mul_eq_left_of_lt_right
      b c ((-1) ^ ((i.val + 1) / 2))
        ((-1) ^ ((i.val - 1) / 2)) (i.val + 1) 0 (i.val - 1)
          hseparation
    rw [hscalar,
      b.truncatedPrefixDefect_comm b
        ((-1) ^ ((i.val + 1) / 2)) (i.val + 1) 0,
      htarget] at hsharp
    exact hsharp.le
  · have hseparation : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) (i.val - 1) 0 <
      c.truncatedPrefixDefect b
        ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) := by
      rw [c.truncatedPrefixDefect_comm c
          ((-1) ^ ((i.val - 1) / 2)) (i.val - 1) 0,
        c.truncatedPrefixDefect_zero_left_eq_self b
          ((-1) ^ ((i.val + 1) / 2)) (i.val + 1)]
      exact hcomparisonLt
    have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
      c b ((-1) ^ ((i.val - 1) / 2))
        ((-1) ^ ((i.val + 1) / 2)) (i.val - 1) 0 (i.val + 1)
          hseparation
    have hscalarComm :
        ((-1 : Kˣ) ^ ((i.val - 1) / 2)) *
            ((-1) ^ ((i.val + 1) / 2)) = -1 := by
      rw [mul_comm]
      exact hscalar
    have hmixedComm := b.truncatedPrefixDefect_comm c (-1)
      (i.val + 1) (i.val - 1)
    rw [hscalarComm,
      c.truncatedPrefixDefect_comm c
        ((-1) ^ ((i.val - 1) / 2)) (i.val - 1) 0] at hsharp
    calc
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) =
          c.truncatedPrefixDefect b (-1) (i.val - 1) (i.val + 1) :=
        hmixedComm
      _ = comparison := hsharp
      _ ≤ target := hcomparisonLt.le
      _ = central := htarget

end BONG.GoodBONG

end Bong
