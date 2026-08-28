/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-III witness

The exact third-prefix value is finite, so its even prefix is nonempty.
Extended capped domination then selects the odd one-based index used in the
paper and records both its central defect bound and its norm-floor order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The self-comparison at the empty prefix with scalar one is infinite. -/
theorem truncatedPrefixDefect_self_one_zero_eq_top
    (c : GoodBONG q N (n + 2)) :
    c.truncatedPrefixDefect c 1 0 0 = ⊤ := by
  unfold truncatedPrefixDefect
  rw [c.prefixAlphaCap_zero]
  simp only [inf_top_eq]
  rw [show (1 : Kˣ) * c.prefixProduct 0 * c.prefixProduct 0 = 1 by
    simp [GoodBONG.prefixProduct]]
  rw [defectOrder_eq_top_of_isSquare]
  exact IsSquare.one

/-- The domination witness in the exact type-III third-prefix branch. -/
theorem beli2019Lemma79_typeIII_caseSix_exists_dominationWitness
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hthird : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ)) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i.val - 1 ∧
      c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ) ∧
      (((((c.order j.castSucc - c.order ⟨i.val - 1, by
              exact (Nat.sub_le i.val 1).trans_lt i.lt_large⟩ : Int) : ℚ) +
          c.alphaValue ⟨i.val - 2, by
            have hiLarge := i.lt_large
            omega⟩ : ℚ)) : WithTop ℚ) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ) ∧
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 ≤
        c.order j.castSucc := by
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  have hlengthEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hlengthPos : 0 < i.val - 1 := by
    by_contra hnot
    have hzero : i.val - 1 = 0 := Nat.eq_zero_of_not_pos hnot
    have htop : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) = ⊤ := by
      rw [hzero]
      norm_num
      exact c.truncatedPrefixDefect_self_one_zero_eq_top
    rw [htop] at hthird
    exact WithTop.top_ne_coe hthird
  have hnextBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  rcases c.exists_even_capped_domination_order_bound_through_next
      (i.val - 1) hlengthPos hnextBound hlengthEven with
    ⟨j, hjEven, hjlt, hjDefect, hjOrder⟩
  have hjDefect' : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ) := by
    rw [← hthird]
    exact hjDefect
  have hjOrder' :
      (((((c.order j.castSucc - c.order ⟨i.val - 1, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨i.val - 2, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ) := by
    rw [← hthird]
    simpa only [show i.val - 1 - 1 = i.val - 2 by omega] using hjOrder
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hthirdMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) j.castSucc.isLt hjEven
  have hjLower :
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 ≤
        c.order j.castSucc := by
    rw [hsourceLeft]
    calc
      a.orderSequence.entryOrZero 0 + 1 ≤
          c.orderSequence.entryOrZero 0 := hfirstLower
      _ ≤ c.orderSequence.entryOrZero j.val := hthirdMonotone
      _ = c.order j.castSucc :=
        c.orderSequence_entryOrZero_eq_order j.castSucc
  exact ⟨j, hjEven, hjlt, hjDefect', hjOrder', hjLower⟩

end BONG.GoodBONG

end Bong
