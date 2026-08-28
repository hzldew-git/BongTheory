/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma219GapOne
import Bong.Bong.Beli2019Lemma219GapThree
import Bong.Bong.Beli2019Lemma79PointwiseComplete

/-!
# Beli (2019), Lemma 7.9(iv): the common-suffix branch

At a long boundary after the final changed order, the next coefficient of
the original and reduced target BONGs agrees.  The gap-three case of Lemma
2.19 embeds the source prefix in the original target prefix.  Its gap-one
case identifies the reduced and original target prefixes, so composition
gives condition (iv) for the reduced target.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The paper's condition `i + 1 ≥ u` in zero-based form: the long index is
at or beyond the last unequal order coordinate. -/
def Lemma79NormalizedClassification.IsCommonSuffixForLongAt
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (_D : Lemma79NormalizedClassification a b)
    (i : LongRepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ last, BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last ∧ last ≤ i.val

/-- On the long common-suffix branch, the next source and target orders are
equal. -/
theorem Lemma79NormalizedClassification.nextOrder_eq_of_commonSuffixForLong
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (htail : D.IsCommonSuffixForLongAt i) :
    a.order ⟨i.val + 1, i.succ_lt_large⟩ =
      b.order ⟨i.val + 1, i.succ_lt_large⟩ := by
  rcases htail with ⟨last, hlast, hle⟩
  have hentry := hlast.after (i.val + 1) (by omega) i.succ_lt_large
  rw [a.orderSequence_entryOrZero_eq_order
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (n + 2)),
    b.orderSequence_entryOrZero_eq_order
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (n + 2))] at hentry
  exact hentry

/-- The common-suffix branch of Lemma 7.9(iv), stated with the single order
equality actually used in the proof. -/
theorem beli2019Lemma79_long_of_nextOrder_eq
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
      b.order ⟨i.val + 1, i.succ_lt_large⟩)
    (htrigger :
      (if hi : i.val ≤ n + 2 then
          b.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            c.order ⟨i.val - 1, by have := i.one_lt; omega⟩
        else True) ∧
      c.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ + 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
      b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
          2 * (ramificationIndex K : Int) ≤
        c.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ + 2 * (ramificationIndex K : Int)) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.succ_lt_large
        omega))
      (b.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
  have hsourceStrict :
      c.order ⟨i.val - 2, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    rw [hnext]
    exact htrigger.2.1
  have htargetStrict :
      b.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ := by
    rw [hnext]
    exact htrigger.2.2.trans_lt htrigger.2.1
  have hsourceToOriginal := a.beli2019Lemma219_gapThree
    (alphaV := alpha) (alphaW := alpha) c hac i hsourceStrict
  have hreducedToOriginal := a.beli2019Lemma219_gapOne
    (alphaV := alpha) (alphaW := alpha) b hab i htargetStrict
  exact hsourceToOriginal.trans hreducedToOriginal.symm_of_sameRank

/-- The common-suffix branch packaged directly from a normalized Lemma 6.7
classification. -/
theorem Lemma79NormalizedClassification.longRepresentation_of_commonSuffix
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (htail : D.IsCommonSuffixForLongAt i)
    (htrigger :
      (if hi : i.val ≤ n + 2 then
          b.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            c.order ⟨i.val - 1, by have := i.one_lt; omega⟩
        else True) ∧
      c.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ + 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
      b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
          2 * (ramificationIndex K : Int) ≤
        c.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ + 2 * (ramificationIndex K : Int)) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.succ_lt_large
        omega))
      (b.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) :=
  beli2019Lemma79_long_of_nextOrder_eq a b c hab hac i
    (D.nextOrder_eq_of_commonSuffixForLong i htail) htrigger

end BONG.GoodBONG

end Bong
