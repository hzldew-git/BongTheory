/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma219GapOneComplete
import Bong.Bong.Beli2019Lemma219GapThree
import Bong.Bong.Beli2019SectionFourLongOrders

/-!
# Beli (2019), Section 4(iv): the two outer branches

When `S_i ≥ R_(i+2)`, Lemma 2.19 factors the desired representation
through the middle prefix of length `i - 1`.  The reverse-dual branch
`T_(i-1) ≥ S_(i+1)` factors through the middle prefix of length `i + 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- Section 4(iv), branch `S_i ≥ R_(i+2)`. -/
theorem sectionFourLongCertificate_throughPrevious
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hmiddle : a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
      b.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩) :
    LongRepresentationCertificate a b c i := by
  have hsourceMiddle :
      c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ := htrigger.2.1.trans_le hmiddle
  have hprevious := b.previous_order_le_of_middle_source_crossGap
    c hbc.orderCondition i hsourceMiddle
  have hmiddleTarget :
      b.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    have hpreviousTwoE :
        b.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) ≤
          c.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) :=
      by simpa only [add_comm] using
        add_le_add_right hprevious (2 * (ramificationIndex K : Int))
    exact hpreviousTwoE.trans_lt htrigger.2.1
  let p : RepresentationIndex (n + 1) (n + 1) :=
    { val := i.val - 1
      pos := by
        have := i.one_lt
        omega
      lt_large := by
        have := i.succ_lt_large
        omega
      le_small := by
        have := i.succ_lt_large
        omega }
  have hsourceToMiddle := b.beli2019Lemma219_gapOne_complete
    c hbc p (by
      simpa only [p, Nat.sub_sub, one_add_one_eq_two] using hsourceMiddle)
  have hmiddleToTarget := a.beli2019Lemma219_gapThree
    b hab i hmiddleTarget
  exact LongRepresentationCertificate.throughPrevious
    (by simpa only [p] using hsourceToMiddle) hmiddleToTarget

/-- Section 4(iv), reverse-dual branch `T_(i-1) ≥ S_(i+1)`. -/
theorem sectionFourLongCertificate_throughNext
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.LongRepresentationTrigger c i)
    (hmiddle : b.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ ≤
      c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩) :
    LongRepresentationCertificate a b c i := by
  have hmiddleTarget :
      b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    have hmiddleTwoE :
        b.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) ≤
          c.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) :=
      by simpa only [add_comm] using
        add_le_add_right hmiddle (2 * (ramificationIndex K : Int))
    exact hmiddleTwoE.trans_lt htrigger.2.1
  have hnext := a.next_order_le_of_target_middle_crossGap
    b hab.orderCondition i hmiddleTarget
  have hsourceMiddle :
      c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val + 1, i.succ_lt_large⟩ :=
    htrigger.2.1.trans_le hnext
  let p : RepresentationIndex (n + 1) (n + 1) :=
    { val := i.val + 1
      pos := by omega
      lt_large := i.succ_lt_large
      le_small := i.succ_lt_large.le }
  have hsourceToMiddle := b.beli2019Lemma219_gapThree
    c hbc i hsourceMiddle
  have hmiddleToTarget := a.beli2019Lemma219_gapOne_complete
    b hab p (by
      simpa only [p, Nat.add_sub_cancel] using hmiddleTarget)
  exact LongRepresentationCertificate.throughNext hsourceToMiddle
    (by simpa only [p] using hmiddleToTarget)

end BONG.GoodBONG

end Bong
