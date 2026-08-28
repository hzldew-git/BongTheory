/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Bounds
import Bong.Bong.Beli2019Lemma69TypeILeftPrimary
import Bong.Bong.Beli2019Lemma79OrderTypeICentralComplete

/-!
# Beli (2019), Lemma 7.9(i): the exceptional type-I left predecessor

This file formalizes the first half of the exceptional argument in lines
5137--5154 of the v2 paper.  If both alternatives of condition 2.1(i) fail
at the predecessor of the first type-I switch, the old order condition is
forced to be an equality.  Lemma 2.14 then removes the half-gap candidate,
the source alpha formula bounds `A'`, and the primary candidate is too large.
Thus an interior failure must be carried by the secondary mixed defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Exact order data forced by failure of both alternatives at the
predecessor of the canonical type-I left switch. -/
structure Lemma79TypeILeftPredecessorFailureData
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (leftSwitch : Nat) : Prop where
  targetCurrent_le :
    c.orderSequence.entryOrZero (leftSwitch - 1) ≤
      a.orderSequence.entryOrZero (leftSwitch - 1) - 2
  pair_eq :
    a.orderSequence.entryOrZero (leftSwitch - 1) +
        a.orderSequence.entryOrZero leftSwitch =
      c.orderSequence.entryOrZero (leftSwitch - 2) +
        c.orderSequence.entryOrZero (leftSwitch - 1)
  cross :
    a.orderSequence.entryOrZero leftSwitch <
      c.orderSequence.entryOrZero (leftSwitch - 2)

/-- Failure of both new alternatives pins down the exceptional equality
configuration displayed in lines 5143--5146 of the paper. -/
theorem lemma79_typeI_leftPredecessor_failureData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnotDirect : ¬ b.orderSequence.entryOrZero (C.leftSwitch - 1) ≤
      c.orderSequence.entryOrZero (C.leftSwitch - 1))
    (hnotPair : ¬
      b.orderSequence.entryOrZero (C.leftSwitch - 1) +
          b.orderSequence.entryOrZero C.leftSwitch ≤
        c.orderSequence.entryOrZero (C.leftSwitch - 2) +
          c.orderSequence.entryOrZero (C.leftSwitch - 1)) :
    Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpreviousRaw := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hprevious :
      b.orderSequence.entryOrZero (C.leftSwitch - 1) =
        a.orderSequence.entryOrZero (C.leftSwitch - 1) - 1 := by
    rw [b.orderSequence.entryOrZero_of_lt (by omega),
      a.orderSequence.entryOrZero_of_lt (by omega)]
    exact hpreviousRaw
  have hcurrent := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst C.leftSwitch C.left_even le_rfl
      (C.left_le_anchor.trans C.anchor_le_right)
  have htargetCurrent :
      c.orderSequence.entryOrZero (C.leftSwitch - 1) ≤
        a.orderSequence.entryOrZero (C.leftSwitch - 1) - 2 := by
    omega
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have holdPair :
      a.orderSequence.entryOrZero (C.leftSwitch - 1) +
          a.orderSequence.entryOrZero C.leftSwitch ≤
        c.orderSequence.entryOrZero (C.leftSwitch - 2) +
          c.orderSequence.entryOrZero (C.leftSwitch - 1) := by
    rcases hacSequence.compare (C.leftSwitch - 1) (by omega) with
      holdDirect | ⟨_, hnext, holdPair⟩
    · have holdDirect' :
          a.orderSequence.entryOrZero (C.leftSwitch - 1) ≤
            c.orderSequence.entryOrZero (C.leftSwitch - 1) := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega),
          c.orderSequence.entryOrZero_of_lt (by omega)]
        exact holdDirect
      omega
    · calc
        a.orderSequence.entryOrZero (C.leftSwitch - 1) +
              a.orderSequence.entryOrZero C.leftSwitch =
            a.orderSequence.entry (C.leftSwitch - 1) (by omega) +
              a.orderSequence.entry C.leftSwitch hleftBound := by
                rw [a.orderSequence.entryOrZero_of_lt (by omega),
                  a.orderSequence.entryOrZero_of_lt hleftBound]
        _ ≤ c.orderSequence.entry (C.leftSwitch - 2) (by omega) +
              c.orderSequence.entry (C.leftSwitch - 1) (by omega) := by
                simpa only [show C.leftSwitch - 1 + 1 = C.leftSwitch by omega,
                  show C.leftSwitch - 1 - 1 = C.leftSwitch - 2 by omega] using
                    holdPair
        _ = c.orderSequence.entryOrZero (C.leftSwitch - 2) +
              c.orderSequence.entryOrZero (C.leftSwitch - 1) := by
                rw [c.orderSequence.entryOrZero_of_lt (by omega),
                  c.orderSequence.entryOrZero_of_lt (by omega)]
  have hpairEq :
      a.orderSequence.entryOrZero (C.leftSwitch - 1) +
          a.orderSequence.entryOrZero C.leftSwitch =
        c.orderSequence.entryOrZero (C.leftSwitch - 2) +
          c.orderSequence.entryOrZero (C.leftSwitch - 1) := by
    omega
  refine ⟨htargetCurrent, hpairEq, ?_⟩
  omega

/-- At the exceptional profile, Lemma 2.14 forces `A = A'`: otherwise
the half-gap candidate would reverse the strict cross-order inequality. -/
theorem lemma79_typeI_leftPredecessor_alpha_eq_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (leftSwitch : Nat) (hleftTwo : 2 ≤ leftSwitch)
    (hleftBound : leftSwitch < n + 2)
    (F : Lemma79TypeILeftPredecessorFailureData a c leftSwitch) :
    a.representationAlpha c
        ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩ =
      a.representationAlphaPrime c
        ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩ := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩
  by_contra hne
  have hsplit := a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
    c idx (by simpa only [idx] using hne)
  have hreverse := a.sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
    c idx (by simp only [idx]; omega) hsplit.2
  have hcross :
      a.order ⟨leftSwitch, hleftBound⟩ <
        c.order ⟨leftSwitch - 2, by omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact F.cross
  exact (lt_asymm hcross hreverse).elim

/-- Condition 2.1(ii) for the old pair and the normalized source-alpha
formula bound the reduced invariant `A'` by
`R_t - R_(t-1) + 1`. -/
theorem lemma79_typeI_leftPredecessor_alphaPrime_le_sourceCut
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (F : Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch) :
    a.representationAlphaPrime c
        ⟨C.leftSwitch, hleftPos,
          C.left_le_anchor.trans_lt D.anchor_bound,
          (C.left_le_anchor.trans_lt D.anchor_bound).le⟩ ≤
      (((a.order
            ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
          a.order ⟨C.leftSwitch - 1, by
            have hbound := C.left_le_anchor.trans_lt D.anchor_bound
            omega⟩ : Int) : ℚ) + 1 : ℚ) := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.leftSwitch, hleftPos, hleftBound, hleftBound.le⟩
  let p : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  have halphaPrime := lemma79_typeI_leftPredecessor_alpha_eq_prime
    a c C.leftSwitch hleftTwo hleftBound F
  have hcomparison := hdefectAC idx
  have hcap := a.truncatedPrefixDefect_le_leftCap
    c 1 idx.val idx.val
  rw [a.prefixAlphaCap_of_internal idx.pos idx.lt_large] at hcap
  have hAlphaLe :
      (a.representationAlphaValue c idx : WithTop ℚ) ≤
        (a.alphaValue p : WithTop ℚ) := by
    exact hcomparison.trans hcap
  have hsourceFormula := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefectAB idx (by simp only [idx]; omega)
      (by simp only [idx]; exact le_rfl)
      (by simpa only [idx] using C.left_even)
  calc
    a.representationAlphaPrime c idx = a.representationAlpha c idx :=
      halphaPrime.symm
    _ = (a.representationAlphaValue c idx : WithTop ℚ) :=
      (a.coe_representationAlphaValue c idx).symm
    _ ≤ (a.alphaValue p : WithTop ℚ) := hAlphaLe
    _ = (((a.order ⟨C.leftSwitch, hleftBound⟩ -
          a.order ⟨C.leftSwitch - 1, by omega⟩ : Int) : ℚ) + 1 : ℚ) := by
      exact congrArg (fun x : ℚ => (x : WithTop ℚ)) (by
        simpa only [idx, p] using hsourceFormula)

/-- The primary defect candidate is strictly larger than the source cut,
because failure of the direct comparison lowers the third current order by
at least two and every capped defect is nonnegative. -/
theorem lemma79_typeI_leftPredecessor_sourceCut_lt_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (leftSwitch : Nat) (hleftTwo : 2 ≤ leftSwitch)
    (hleftBound : leftSwitch < n + 2)
    (F : Lemma79TypeILeftPredecessorFailureData a c leftSwitch) :
    ((((a.order ⟨leftSwitch, hleftBound⟩ -
        a.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ) <
      a.representationPrimaryDefect c
        ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩ := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩
  have hcurrent :
      c.order ⟨leftSwitch - 1, by omega⟩ ≤
        a.order ⟨leftSwitch - 1, by omega⟩ - 2 := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact F.targetCurrent_le
  have hcoefficient :
      ((((a.order ⟨leftSwitch, hleftBound⟩ -
          a.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) + 1 : ℚ) :
            WithTop ℚ) <
        (((a.order ⟨leftSwitch, hleftBound⟩ -
          c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) := by
    norm_cast
    exact_mod_cast (show
      a.order ⟨leftSwitch, hleftBound⟩ -
          a.order ⟨leftSwitch - 1, by omega⟩ + 1 <
        a.order ⟨leftSwitch, hleftBound⟩ -
          c.order ⟨leftSwitch - 1, by omega⟩ by omega)
  have hnonnegative := a.truncatedPrefixDefect_nonneg
    c (-1) (idx.val + 1) (idx.val - 1)
  unfold representationPrimaryDefect
  exact hcoefficient.trans_le (by
    calc
      (((a.order ⟨leftSwitch, hleftBound⟩ -
          c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
          0 + (((a.order ⟨leftSwitch, hleftBound⟩ -
            c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) := by rw [zero_add]
      _ ≤ a.truncatedPrefixDefect c (-1) (leftSwitch + 1)
            (leftSwitch - 1) +
          (((a.order ⟨leftSwitch, hleftBound⟩ -
            c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) := by
        simpa only [idx] using
          add_le_add_left hnonnegative
            (((a.order ⟨leftSwitch, hleftBound⟩ -
              c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
                WithTop ℚ)
      _ = (((a.order ⟨leftSwitch, hleftBound⟩ -
            c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) (leftSwitch + 1)
            (leftSwitch - 1) := by rw [add_comm])

/-- Consequently an interior exceptional failure must be realized by the
secondary candidate of `A'`. -/
theorem lemma79_typeI_leftPredecessor_secondary_le_sourceCut
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (F : Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch)
    (hinterior : C.leftSwitch + 1 < n + 2) :
    a.representationSecondaryDefect c
        ⟨C.leftSwitch, hleftPos,
          C.left_le_anchor.trans_lt D.anchor_bound,
          (C.left_le_anchor.trans_lt D.anchor_bound).le⟩
        ⟨by
          change 1 < C.leftSwitch
          rcases C.left_even with ⟨d, hd⟩
          omega, hinterior⟩ ≤
      (((a.order
            ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
          a.order ⟨C.leftSwitch - 1, by
            omega⟩ : Int) : ℚ) + 1 : ℚ) := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.leftSwitch, hleftPos, hleftBound, hleftBound.le⟩
  let hi : 1 < idx.val ∧ idx.val + 1 < n + 2 :=
    ⟨by
      simp only [idx]
      omega,
    by simpa only [idx] using hinterior⟩
  have hprime := lemma79_typeI_leftPredecessor_alphaPrime_le_sourceCut
    a b c D C hfirst hleftPos hdefectAB hdefectAC F
  have hprimary := lemma79_typeI_leftPredecessor_sourceCut_lt_primary
    a c C.leftSwitch hleftTwo hleftBound F
  rw [a.representationAlphaPrime_eq_min_primary_secondary c idx hi] at hprime
  rcases min_le_iff.mp hprime with hprimaryLe | hsecondary
  · exact False.elim ((not_le_of_gt hprimary) hprimaryLe)
  · simpa only [idx, hi] using hsecondary

/-- The secondary-candidate inequality and the exceptional adjacent-sum
equality simplify to the mixed-defect upper bound in line 5154. -/
theorem lemma79_typeI_leftPredecessor_mixed_le_orderCut
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (leftSwitch : Nat) (hleftTwo : 2 ≤ leftSwitch)
    (hleftBound : leftSwitch < n + 2)
    (hinterior : leftSwitch + 1 < n + 2)
    (F : Lemma79TypeILeftPredecessorFailureData a c leftSwitch)
    (hsecondary :
      a.representationSecondaryDefect c
          ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩
          ⟨by
            show 1 < leftSwitch
            omega, hinterior⟩ ≤
        (((a.order ⟨leftSwitch, hleftBound⟩ -
            a.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) + 1 : ℚ)) :
    a.truncatedPrefixDefect c 1 (leftSwitch + 2) (leftSwitch - 2) ≤
      (((a.order ⟨leftSwitch, hleftBound⟩ -
          a.order ⟨leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨leftSwitch, by omega, hleftBound, hleftBound.le⟩
  let hi : 1 < idx.val ∧ idx.val + 1 < n + 2 :=
    ⟨by simp only [idx]; omega, by simpa only [idx] using hinterior⟩
  let coefficient : ℚ :=
    ((a.order ⟨leftSwitch, hleftBound⟩ +
      a.order ⟨leftSwitch + 1, hinterior⟩ -
      c.order ⟨leftSwitch - 2, by omega⟩ -
      c.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ)
  let sourceCut : ℚ :=
    ((a.order ⟨leftSwitch, hleftBound⟩ -
      a.order ⟨leftSwitch - 1, by omega⟩ : Int) : ℚ) + 1
  let targetCut : ℚ :=
    ((a.order ⟨leftSwitch, hleftBound⟩ -
      a.order ⟨leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1
  let mixed : WithTop ℚ :=
    a.truncatedPrefixDefect c 1 (leftSwitch + 2) (leftSwitch - 2)
  have hpair :
      a.order ⟨leftSwitch - 1, by omega⟩ +
          a.order ⟨leftSwitch, hleftBound⟩ =
        c.order ⟨leftSwitch - 2, by omega⟩ +
          c.order ⟨leftSwitch - 1, by omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact F.pair_eq
  have hsecondaryRaw := hsecondary
  unfold representationSecondaryDefect at hsecondaryRaw
  have hsecondary' :
      (coefficient : WithTop ℚ) + mixed ≤ (sourceCut : WithTop ℚ) := by
    simpa only [idx, hi, coefficient, sourceCut, mixed] using hsecondaryRaw
  have htranslated := add_le_add_right hsecondary'
    ((-coefficient : ℚ) : WithTop ℚ)
  have hcut : sourceCut - coefficient = targetCut := by
    dsimp only [sourceCut, coefficient, targetCut]
    push_cast
    have hpairQ :
        (a.order ⟨leftSwitch - 1, by omega⟩ : ℚ) +
            a.order ⟨leftSwitch, hleftBound⟩ =
          c.order ⟨leftSwitch - 2, by omega⟩ +
            c.order ⟨leftSwitch - 1, by omega⟩ := by
      exact_mod_cast hpair
    linarith
  change mixed ≤ (targetCut : WithTop ℚ)
  calc
    mixed = 0 + mixed := by rw [zero_add]
    _ = (((-coefficient : ℚ) : WithTop ℚ) +
        (coefficient : WithTop ℚ)) + mixed := by
      have hcancel : (((-coefficient : ℚ) : WithTop ℚ) +
          (coefficient : WithTop ℚ)) = 0 := by
        norm_cast
        ring
      rw [hcancel]
    _ = ((-coefficient : ℚ) : WithTop ℚ) +
        ((coefficient : WithTop ℚ) + mixed) := by rw [add_assoc]
    _ ≤ ((-coefficient : ℚ) : WithTop ℚ) +
        (sourceCut : WithTop ℚ) := htranslated
    _ = (targetCut : WithTop ℚ) := by
      norm_cast
      linarith [hcut]

end BONG.GoodBONG

end Bong
