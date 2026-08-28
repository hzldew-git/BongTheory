/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIAssembled
import Bong.Bong.Beli2019Lemma69TypeIICoreAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 5: the comparison alpha

If the source pair has constant order `T`, the preceding comparison order
is at most `T`, and condition 2.1(i) holds, then the comparison alpha cannot
vanish.  Otherwise P2 lowers the next comparison order by `2e`, contradicting
the adjacent-pair inequality.  Hence the comparison alpha is at least one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The comparison alpha is at least one under a constant source-pair
bound. -/
theorem one_le_previousAlpha_of_constant_pair
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 1) (n + 1)) (T : Int)
    (hbPrevious : b.orderSequence.entryOrZero (i.val - 1) = T)
    (hbCurrent : b.orderSequence.entryOrZero i.val = T)
    (hcPrevious : c.orderSequence.entryOrZero (i.val - 1) ≤ T) :
    (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have := i.pos
      have := i.lt_large
      omega⟩ := by
  have hiPrevious : i.val - 1 < n + 1 := by
    have := i.lt_large
    omega
  have hpairRaw :=
    ((b.representationOrderCondition_iff c le_rfl).mp hbc).pairSum_le
      (i.val - 1) (by
        have := i.pos
        have := i.lt_large
        omega)
  have hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hiPrevious,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.lt_large,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence i.lt_large]
    simpa only [Nat.sub_add_cancel i.pos] using hpairRaw
  let previous : Fin n := ⟨i.val - 1, by
    have := i.pos
    have := i.lt_large
    omega⟩
  have hpreviousSucc : previous.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [previous, Fin.succ_mk]
    exact Nat.sub_add_cancel i.pos
  have hpreviousCast : previous.castSucc =
      ⟨i.val - 1, hiPrevious⟩ := by
    apply Fin.ext
    rfl
  have hne : c.alphaValue previous ≠ 0 := by
    intro hzero
    have hgap := (c.alpha_p2 previous).2.mp hzero
    rw [orderGap, hpreviousSucc, hpreviousCast] at hgap
    have hgap' : c.orderSequence.entryOrZero i.val -
        c.orderSequence.entryOrZero (i.val - 1) =
          -(2 * (ramificationIndex K : Int)) := by
      simpa only [
        BeliOrderSequence.entryOrZero_of_lt c.orderSequence i.lt_large,
        BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
        orderSequence_at] using hgap
    have hePos := ramificationIndex_pos (K := K)
    rw [hbPrevious, hbCurrent] at hpair
    omega
  simpa only [previous] using c.one_le_alphaValue_of_ne_zero previous hne

end BONG.GoodBONG

end Bong
