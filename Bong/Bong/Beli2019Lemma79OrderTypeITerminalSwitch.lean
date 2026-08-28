/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77TypeITerminalSwitch
import Bong.Bong.Beli2019Lemma79EvenTargetParity
import Bong.Bong.Beli2019Lemma79OrderTypeIPrimaryCentral

/-!
# Beli (2019), Lemma 7.9(i): a terminal type-I switch

This is the boundary branch in which the canonical right switch is the last
unequal coordinate, but a common suffix coordinate still follows it.  The
usual one-unit source-target shift at the next coordinate has disappeared.
The equality case is excluded by retaining the sharp defect identity from
the primary branch: equality forces a zero alpha, hence even parity of the
mixed product; its odd total order then makes the mixed defect zero and
contradicts the positive adjacent lower bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.7 puts the source prefix strictly above the primary cut even
when the right switch itself is the last unequal coordinate. -/
theorem lemma79_typeI_even_sourcePrefix_gt_primaryCut_terminalSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hnext : C.rightSwitch + 1 < n + 2) :
    (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect a
        ((-1) ^ ((C.rightSwitch + 2) / 2)) 0
          (C.rightSwitch + 2) := by
  have hlower := beli2019Lemma77_typeI_terminalSwitch_sourceCapped
    a b D C hfirst hdefect hrightLast hnext
  have hrightTwoEven : Even (C.rightSwitch + 2) := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hplateau := lemma77_typeI_source_plateau
    a b D C hfirst (C.rightSwitch + 2) (by omega) (by omega)
      hrightTwoEven le_rfl
  have hplateau' : a.order (0 : Fin (n + 2)) =
      a.order ⟨C.rightSwitch, by omega⟩ := by
    simpa only [show C.rightSwitch + 2 - 2 = C.rightSwitch by omega] using
      hplateau
  have hstrict :
      (((a.order (0 : Fin (n + 2)) + 1 -
          a.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) : WithTop ℚ) <
        ((((a.order ⟨C.rightSwitch, by omega⟩ -
          a.order ⟨C.rightSwitch + 1, hnext⟩ : Int) : ℚ) + 2 : ℚ) :
            WithTop ℚ) := by
    norm_cast
    linarith [hplateau']
  exact hstrict.trans_le hlower

/-- The primary candidate at a terminal switch gives the pair alternative.
The only extra work relative to the interior proof is ruling out equality of
the next source order and the preceding comparison order. -/
theorem lemma79_typeI_even_primary_data_terminalSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hnext : C.rightSwitch + 1 < n + 2)
    (hnot : ¬ b.orderSequence.entry C.rightSwitch (by omega) ≤
      c.orderSequence.entry C.rightSwitch (by omega))
    (hprimary : a.representationPrimaryDefect c {
      val := C.rightSwitch + 1
      pos := by omega
      lt_large := hnext
      le_small := hnext.le } ≤ 0) :
    2 ≤ C.rightSwitch ∧
      b.orderSequence.entry C.rightSwitch (by omega) +
          b.orderSequence.entry (C.rightSwitch + 1) hnext ≤
        c.orderSequence.entry (C.rightSwitch - 1) (by omega) +
          c.orderSequence.entry C.rightSwitch (by omega) := by
  let k := C.rightSwitch
  have hk : k < n + 2 := by
    dsimp only [k]
    omega
  have hkNext : k + 1 < n + 2 := by
    simpa only [k] using hnext
  have hkEven : Even k := by
    simpa only [k] using C.right_even
  have hleft : C.leftSwitch ≤ k := by
    dsimp only [k]
    exact C.left_le_anchor.trans C.anchor_le_right
  have hlast : k ≤ D.profile.last := by
    dsimp only [k]
    exact hrightLast.le
  have hnot' : ¬ b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk := by
    simpa only [k] using hnot
  have hprimary' : a.representationPrimaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } ≤ 0 := by
    simpa only [k] using hprimary
  have hsource :=
    lemma79_typeI_even_sourcePrefix_gt_primaryCut_terminalSwitch
      a b D C hfirst hdefect hrightLast hnext
  rcases lemma79_typeI_even_primary_defect_core_of_sourcePrefix
      a b c D C hfirst hnorm k hk hkNext hkEven hleft hlast hnot'
        (by simpa only [k] using hsource) hprimary' with
    ⟨hkTwo, hcMinusTwo, hthirdEq, hlower, hupper⟩
  rcases lemma79_typeI_even_primary_sourceNext_le_previous_of_sourcePrefix
      a b c D C hfirst hnorm k hk hkNext hkEven hleft hlast hnot'
        (by simpa only [k] using hsource) hprimary' with
    ⟨_, hsourceNextLe⟩
  rcases lemma79_typeI_even_failure_orders
      a b c D C hfirst hnorm k hk hkEven hleft hlast hnot' with
    ⟨hbCurrent, _, hcCurrent⟩
  have hsourceNextStrict :
      a.orderSequence.entryOrZero (k + 1) <
        c.orderSequence.entryOrZero (k - 1) := by
    apply lt_of_le_of_ne hsourceNextLe
    intro heq
    have heq' : c.orderSequence.entryOrZero (k - 1) =
        a.orderSequence.entryOrZero (k + 1) := heq.symm
    have haZeroOrder : a.order (0 : Fin (n + 2)) =
        a.orderSequence.entryOrZero 0 :=
      (a.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2))).symm
    have hcMinusTwoOrder : c.order ⟨k - 2, by omega⟩ =
        a.orderSequence.entryOrZero 0 + 1 := by
      rw [← c.orderSequence_entryOrZero_eq_order]
      exact hcMinusTwo
    have hpreviousOrder : c.order ⟨k - 1, by omega⟩ =
        a.order ⟨k + 1, hkNext⟩ := by
      rw [← c.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order]
      exact heq'
    have hcoefficient := hlower.trans hupper
    norm_cast at hcoefficient
    rw [haZeroOrder, hcMinusTwoOrder, hpreviousOrder] at hcoefficient
    push_cast at hcoefficient
    have halphaNonnegative := (c.alpha_p2 ⟨k - 2, by omega⟩).1
    have halphaZero : c.alphaValue ⟨k - 2, by omega⟩ = 0 := by
      apply le_antisymm
      · linarith
      · exact halphaNonnegative
    have hgap := (c.alpha_p2 ⟨k - 2, by omega⟩).2.mp halphaZero
    have hcCurrentOrder : c.order ⟨k, hk⟩ =
        a.orderSequence.entryOrZero 0 + 1 := by
      rw [← c.orderSequence_entryOrZero_eq_order]
      exact hcCurrent
    have hcurrentNextMod : Int.ModEq 2
        (a.orderSequence.entryOrZero (k + 1))
        (c.orderSequence.entryOrZero k) := by
      rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
        c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩,
        hcCurrentOrder]
      unfold orderGap at hgap
      rw [show (⟨k - 2, by omega⟩ : Fin (n + 1)).succ =
          (⟨k - 1, by omega⟩ : Fin (n + 2)) by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega,
        show (⟨k - 2, by omega⟩ : Fin (n + 1)).castSucc =
          (⟨k - 2, by omega⟩ : Fin (n + 2)) by
            apply Fin.ext
            rfl] at hgap
      rw [hpreviousOrder, hcMinusTwoOrder] at hgap
      rw [Int.modEq_iff_dvd]
      refine ⟨ramificationIndex K, ?_⟩
      omega
    have hprefixParity :=
      lemma79_typeI_even_prefix_modEq_add_one_of_not_le
        a b c D C hfirst hnorm k hk hkEven hleft hlast hnot'
    have hprefixParity' : Int.ModEq 2
        (a.orderSequence.prefixSum (k + 2) +
          c.orderSequence.prefixSum k) 1 := by
      have hadd := hprefixParity.add hcurrentNextMod
      have hadd' := hadd.add
        (Int.ModEq.rfl : Int.ModEq 2
          (c.orderSequence.prefixSum k)
          (c.orderSequence.prefixSum k))
      have href : Int.ModEq 2
          ((c.orderSequence.prefixSum k +
              c.orderSequence.entryOrZero k + 1) +
            c.orderSequence.entryOrZero k +
            c.orderSequence.prefixSum k) 1 := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-(c.orderSequence.prefixSum k +
          c.orderSequence.entryOrZero k), ?_⟩
        ring
      rw [a.orderSequence.prefixSum_succ,
        c.orderSequence.prefixSum_succ] at hadd'
      have hresult := hadd'.trans href
      simpa only [a.orderSequence.prefixSum_add_two, add_assoc] using hresult
    have ordUnit_neg_eq (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa using ord_neg K (z : K)
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have hneg : ordUnit K (-1 : Kˣ) = 0 := by
      rw [ordUnit_neg_eq, hone]
    have hproductOrder : ordUnit K
          ((-1 : Kˣ) * a.prefixProduct (k + 2) * c.prefixProduct k) =
        a.orderSequence.prefixSum (k + 2) +
          c.orderSequence.prefixSum k := by
      rw [ordUnit_mul, ordUnit_mul, hneg, zero_add,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (k + 2) (by omega),
        c.ordUnit_prefixProduct_eq_orderSequence_prefixSum k (by omega)]
    have hodd : Odd (ordUnit K
        ((-1 : Kˣ) * a.prefixProduct (k + 2) * c.prefixProduct k)) := by
      rw [hproductOrder]
      rw [Int.modEq_iff_dvd] at hprefixParity'
      rcases hprefixParity' with ⟨z, hz⟩
      exact ⟨-z, by omega⟩
    have hmixedZero := truncatedPrefixDefect_eq_zero_of_odd_order_general
      a c (-1) (k + 2) k hodd
    have hthirdZero :
        c.truncatedPrefixDefect c ((-1) ^ (k / 2)) 0 k = 0 :=
      hthirdEq.trans hmixedZero
    rw [hthirdZero] at hlower
    norm_cast at hlower
    push_cast at hlower
    rw [hcMinusTwoOrder, hpreviousOrder, halphaZero] at hlower
    unfold orderGap at hgap
    rw [show (⟨k - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨k - 1, by omega⟩ : Fin (n + 2)) by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega,
      show (⟨k - 2, by omega⟩ : Fin (n + 1)).castSucc =
        (⟨k - 2, by omega⟩ : Fin (n + 2)) by
          apply Fin.ext
          rfl] at hgap
    rw [hpreviousOrder, hcMinusTwoOrder] at hgap
    have hePos := ramificationIndex_pos (K := K)
    have hePosQ : (0 : ℚ) < (ramificationIndex K : ℚ) := by
      exact_mod_cast hePos
    have hgapQ :
        (a.order ⟨k + 1, hkNext⟩ : ℚ) -
            ((a.orderSequence.entryOrZero 0 : ℚ) + 1) =
          -(2 * (ramificationIndex K : ℚ)) := by
      exact_mod_cast hgap
    push_cast at hlower
    linarith [hgapQ, hePosQ]
  have hsourceNextLower :
      a.orderSequence.entryOrZero (k + 1) + 1 ≤
        c.orderSequence.entryOrZero (k - 1) := by
    omega
  have hbCurrent' : b.orderSequence.entry k hk =
      a.orderSequence.entryOrZero 0 + 2 := by
    rw [← b.orderSequence.entryOrZero_of_lt hk]
    exact hbCurrent
  have hcCurrent' : c.orderSequence.entry k hk =
      a.orderSequence.entryOrZero 0 + 1 := by
    rw [← c.orderSequence.entryOrZero_of_lt hk]
    exact hcCurrent
  have hnextCommon := D.profile.lastDifference.after
    (k + 1) (by
      dsimp only [k]
      rw [← hrightLast]
      omega) hkNext
  have htargetNext : b.orderSequence.entry (k + 1) hkNext =
      a.orderSequence.entryOrZero (k + 1) := by
    rw [← b.orderSequence.entryOrZero_of_lt hkNext]
    exact hnextCommon.symm
  have hcomparisonPrevious :
      c.orderSequence.entry (k - 1) (by omega) =
        c.orderSequence.entryOrZero (k - 1) := by
    rw [c.orderSequence.entryOrZero_of_lt (by omega)]
  constructor
  · simpa only [k] using hkTwo
  · change b.orderSequence.entry k hk +
        b.orderSequence.entry (k + 1) hkNext ≤
      c.orderSequence.entry (k - 1) (by omega) +
        c.orderSequence.entry k hk
    rw [hbCurrent', hcCurrent', htargetNext, hcomparisonPrevious]
    omega

/-- Condition 2.1(i) at the last unequal coordinate when the canonical
right switch is terminal and a common suffix coordinate follows it. -/
theorem beli2019Lemma79_i_typeI_terminalSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have _ := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hnext : C.rightSwitch + 1 < n + 2) :
    b.orderSequence.entry C.rightSwitch (by omega) ≤
        c.orderSequence.entry C.rightSwitch (by omega) ∨
      ∃ (hk0 : 0 < C.rightSwitch)
          (hkNext' : C.rightSwitch + 1 < n + 2),
        b.orderSequence.entry C.rightSwitch (by omega) +
            b.orderSequence.entry (C.rightSwitch + 1) hkNext' ≤
          c.orderSequence.entry (C.rightSwitch - 1) (by omega) +
            c.orderSequence.entry C.rightSwitch (by omega) := by
  by_cases hdirect : b.orderSequence.entry C.rightSwitch (by omega) ≤
      c.orderSequence.entry C.rightSwitch (by omega)
  · exact Or.inl hdirect
  · have hleft : C.leftSwitch ≤ C.rightSwitch :=
      C.left_le_anchor.trans C.anchor_le_right
    let idx : RepresentationIndex (n + 2) (n + 2) := {
      val := C.rightSwitch + 1
      pos := by omega
      lt_large := hnext
      le_small := hnext.le }
    have hAlpha := lemma79_typeI_even_alphaValue_le_zero_of_not_le
      a b c D C hfirst hdefectAC hnorm C.rightSwitch (by omega) hnext
        C.right_even hleft (by rw [hrightLast]) hdirect
    have hHalf := lemma79_typeI_even_halfGap_pos_of_not_le
      a b c D C hfirst hinitial hnorm C.rightSwitch (by omega) hnext
        C.right_even hleft (by rw [hrightLast]) hdirect
    have hcandidates :=
      a.representationDefectCandidate_le_of_alphaValue_le_of_lt_halfGap
        c idx 0 (by simpa only [idx] using hAlpha) (by
          simpa only [idx] using hHalf)
    rcases hcandidates with hprimary | ⟨hi, hsecondary⟩
    · have hpair := lemma79_typeI_even_primary_data_terminalSwitch
        a b c D C hfirst hrightLast hdefectAB hnorm hnext hdirect (by
          simpa only [idx] using hprimary)
      exact Or.inr ⟨by omega, hnext, hpair.2⟩
    · have hpair := lemma79_typeI_even_pair_of_secondary_le_zero
        a b c D C hfirst C.rightSwitch (by omega) hnext C.right_even
          hleft (by simpa only [idx] using hi) (by
            simpa only [idx] using hsecondary)
      exact Or.inr ⟨by
        have hiPos := hi.1
        simp only [idx] at hiPos
        omega, hnext, hpair⟩

end BONG.GoodBONG

end Bong
