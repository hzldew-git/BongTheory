/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectOddLeftOuter

/-!
# Beli (2019), Lemma 7.9(ii): assembling an odd profile coordinate

This file separates the common local argument in the type-I branch from
the order-profile calculations at the canonical switch.  Exact source and
target orders at the current even coordinate supply the current-order,
adjacent-pair, and prefix-parity hypotheses of the defect-one theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Common assembly for an odd coordinate whose preceding target order is
the first source order plus one and whose adjacent pair agrees with the
source pair. -/
theorem lemma79_ii_of_odd_profile
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) (hodd : Odd i.val)
    (hnextAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ))
    (hfirstTarget : b.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero 0 + 1)
    (hcurrentTarget : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero 0 + 1)
    (hpairSource : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero (i.val - 1) +
        a.orderSequence.entryOrZero i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  rcases hodd with ⟨d, hd⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hkBound : k < n + 2 := by
    simp only [k]
    omega
  have hkNextBound : k + 1 < n + 2 := by
    simp only [k]
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hreferenceFirst : b.orderSequence.entryOrZero k ≤
      c.orderSequence.entryOrZero 0 := by
    rw [show b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero 0 + 1 by
        simpa only [k] using hcurrentTarget]
    exact hfirstOrder
  have hcMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 k (Nat.zero_le k) hkBound hkEven
  have hcurrentK : b.orderSequence.entryOrZero k ≤
      c.orderSequence.entryOrZero k := hreferenceFirst.trans hcMonotone
  have hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≤
      c.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hcurrentK
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have hpairACRaw := hacSequence.pairSum_le k (by omega)
  have hpairAC : a.orderSequence.entryOrZero k +
        a.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1) := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt _ hkBound,
      BeliOrderSequence.entryOrZero_of_lt _ hkNextBound,
      orderSequence_at] using hpairACRaw
  have hpairK : b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1) := by
    rw [show b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) =
      a.orderSequence.entryOrZero k +
        a.orderSequence.entryOrZero (k + 1) by
      simpa only [k, Nat.sub_add_cancel i.pos] using hpairSource]
    exact hpairAC
  have hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hpairK
  let T := b.orderSequence.entryOrZero k
  have htargetFirst : T ≤ b.orderSequence.entryOrZero 0 := by
    dsimp only [T]
    rw [show b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero 0 + 1 by
        simpa only [k] using hcurrentTarget]
    rw [hfirstTarget]
  have hparity : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
    intro heqCurrent
    have hbParity := b.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hkBound htargetFirst le_rfl
    have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
      dsimp only [T]
      simpa only [k] using heqCurrent.symm.le
    have hcParity := c.prefixSum_modEq_mul_of_current_le_reference_le_first
      T k hkBound hreferenceFirst hcCurrent
    have hcombined := hbParity.trans hcParity.symm
    simpa only [k, Nat.sub_add_cancel i.pos] using hcombined
  have heven : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)) := by
    intro heqCurrent
    exact b.comparisonPrefixProduct_order_even_of_prefixSum_modEq
      c i.val i.lt_large.le i.lt_large.le (hparity heqCurrent)
  exact b.lemma79_ii_of_odd_coordinate c i hiNext hnextAlpha
    hcurrent hpair heven

end BONG.GoodBONG

end Bong
