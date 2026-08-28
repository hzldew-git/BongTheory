/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectOne

/-!
# Beli (2019), Lemma 7.9(ii): profile-neutral odd coordinates

This file converts the profile data used in case 2 of the proof into the
ordinary representation defect condition.  The adjacent-pair comparison is
extracted from condition 2.1(i), and congruent prefix sums give the even-order
comparison product required by the defect-one theorem.
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

/-- Congruent prefix orders make the product of the two prefixes have even
valuation. -/
theorem comparisonPrefixProduct_order_even_of_prefixSum_modEq
    (a : GoodBONG q L m) (b : GoodBONG r M n)
    (i : Nat) (him : i ≤ m) (hin : i ≤ n)
    (hparity : Int.ModEq 2 (a.orderSequence.prefixSum i)
      (b.orderSequence.prefixSum i)) :
    Even (ordUnit K (a.prefixProduct i * b.prefixProduct i)) := by
  rw [ordUnit_mul,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum i him,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum i hin]
  rw [Int.modEq_iff_dvd] at hparity
  rcases hparity with ⟨z, hz⟩
  refine ⟨b.orderSequence.prefixSum i - z, ?_⟩
  omega

variable {q : QuadraticSpace K V} {L M : Lattice K V}

/-- The complete profile-neutral form of case 2 in the proof of 2.1(ii). -/
theorem lemma79_ii_of_odd_coordinate_of_order
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hnextAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ))
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≤
      c.orderSequence.entryOrZero (i.val - 1))
    (hparity : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let O := (b.representationOrderCondition_iff c le_rfl).mp horder
  have hpairRaw := O.pairSum_le (i.val - 1) (by
    have := i.pos
    have := i.lt_large
    omega)
  have hiPrevious : i.val - 1 < n + 1 := by omega
  have hpreviousSucc : i.val - 1 + 1 = i.val :=
    Nat.sub_add_cancel i.pos
  have hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        hiPrevious,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.lt_large,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence i.lt_large,
      orderSequence_at, hpreviousSucc] using hpairRaw
  have heven : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) := by
    intro hcurrentEq
    exact b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
      c i.val i.lt_large.le i.lt_large.le (hparity hcurrentEq)
  exact b.lemma79_ii_of_odd_coordinate c i hiNext hnextAlpha
    hcurrent hpair heven

end BONG.GoodBONG

end Bong
