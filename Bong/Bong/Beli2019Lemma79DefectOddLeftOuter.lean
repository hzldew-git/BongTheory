/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIILeftAlpha

/-!
# Beli (2019), Lemma 7.9(ii): odd coordinates in a left outer profile

The type-II and type-III branches have the same no-gap-two left profile.
Once the preceding target alpha is at most one, this file proves the whole
odd-coordinate defect inequality and instantiates it for type II.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The common type-II/type-III proof of Lemma 7.9(ii), case 2. -/
theorem lemma79_ii_of_odd_leftOuter
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hbefore : i.val < O.transition.lastZero + 1)
    (hpreviousAlpha : b.alphaValue ⟨i.val - 1, by
      have hilarge := i.lt_large
      omega⟩ ≤ 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  have hleftEven := O.left_even_of_first_eq_zero hfirst
  rcases hodd with ⟨d, hd⟩
  rcases hleftEven with ⟨e, he⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarLeft : i.val + 1 ≤ O.transition.lastZero := by omega
  have hkLeft : k ≤ O.transition.lastZero := by
    simp only [k]
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := O.transition.firstTwo_le_rank
    have htransition := O.transition.lastZero_lt_firstTwo
    omega
  have hkBound : k < n + 2 := by
    simp only [k]
    omega
  have hkNextBound : k + 1 < n + 2 := by
    simp only [k]
    omega
  have hbPrevious := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo k hkLeft hkEven
  have hbFar := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val + 1) hfarLeft hfarEven
  have htwoStep : b.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hbFar.trans hbPrevious.symm
  let alphaIndex : Fin (n + 1) := ⟨i.val, by omega⟩
  have hnextAlpha := b.nextAlphaValue_le_of_twoStep_eq
    alphaIndex i.pos (by simpa only [alphaIndex] using htwoStep) (by
      simpa only [alphaIndex] using hpreviousAlpha)
  have hnextAlpha' : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ) := by
    simpa only [alphaIndex] using hnextAlpha
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
    rw [hbPrevious]
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
  have hpairParity : Even (O.transition.lastZero - k) :=
    ⟨e - d, by simp only [k]; omega⟩
  have hpairAB := O.leftPairEq k (by omega) hpairParity
  have hpairK : b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1) := by
    rw [← hpairAB]
    exact hpairAC
  have hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val := by
    simpa only [k, Nat.sub_add_cancel i.pos] using hpairK
  let T := b.orderSequence.entryOrZero k
  have hbZero := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have htargetFirst : T ≤ b.orderSequence.entryOrZero 0 := by
    dsimp only [T]
    rw [hbPrevious, hbZero]
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
  exact b.lemma79_ii_of_odd_coordinate c i hiNext hnextAlpha'
    hcurrent hpair heven

/-- Lemma 7.9(ii), case 2, for a normalized type-II profile. -/
theorem beli2019Lemma79_ii_typeII_odd_left
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hbefore : i.val < D.outer.transition.lastZero + 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  rcases hodd with ⟨d, hd⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hkLeft : k ≤ D.outer.transition.lastZero := by
    simp only [k]
    omega
  have hpreviousAlpha := a.beli2019Lemma69_i_typeII_targetLeftTail
    b D hfirst k hkLeft hkEven
  exact lemma79_ii_of_odd_leftOuter a b c D.outer hfirst D.no_gap_two
    hac hnorm i ⟨d, hd⟩ hbefore (by
      simpa only [k] using hpreviousAlpha)

end BONG.GoodBONG

end Bong
