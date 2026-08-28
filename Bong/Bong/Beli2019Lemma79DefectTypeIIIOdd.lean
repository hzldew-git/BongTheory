/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79NextAlpha

/-!
# Beli (2019), Lemma 7.9(ii): the type-III odd left branch

This file assembles case 2 of the proof of condition 2.1(ii) for odd paper
indices strictly before the left transition of a normalized type-III profile.
The proof uses the concrete order profile, not a packaged assumption that the
target already satisfies condition 2.1(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 2, for a normalized type-III profile. -/
theorem beli2019Lemma79_ii_typeIII_odd_left
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hbefore : i.val < D.outer.transition.lastZero + 1) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let k := i.val - 1
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  rcases hodd with ⟨d, hd⟩
  rcases hleftEven with ⟨e, he⟩
  have hkEven : Even k := ⟨d, by simp only [k]; omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarLeft : i.val + 1 ≤ D.outer.transition.lastZero := by omega
  have hkLeft : k ≤ D.outer.transition.lastZero := by
    simp only [k]
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hkBound : k < n + 2 := by
    simp only [k]
    omega
  have hkNextBound : k + 1 < n + 2 := by
    simp only [k]
    omega
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two k hkLeft hkEven
  have hbFar := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val + 1) hfarLeft hfarEven
  have htwoStep : b.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [k] using hbFar.trans hbPrevious.symm
  have hpreviousAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail
    b D hfirst hab hdefectAB htotal hlast k hkLeft hkEven
  let alphaIndex : Fin (n + 1) := ⟨i.val, by omega⟩
  have hnextAlpha := b.nextAlphaValue_le_of_twoStep_eq
    alphaIndex i.pos (by simpa only [alphaIndex] using htwoStep) (by
      simpa only [alphaIndex, k] using hpreviousAlpha)
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
  have hpairParity : Even (D.outer.transition.lastZero - k) :=
    ⟨e - d, by simp only [k]; omega⟩
  have hpairAB := D.outer.leftPairEq k (by omega) hpairParity
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
  have hbZero := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
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

end BONG.GoodBONG

end Bong
