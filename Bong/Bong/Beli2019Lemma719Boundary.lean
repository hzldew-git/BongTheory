/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718NormalForms
import Bong.Bong.Beli2019Lemma715AlphaCommon

/-!
# Beli (2019), Lemma 7.19: boundary alpha equality

This file proves the boundary calculation in Lemma 7.19 for all three
normal forms of Lemma 7.18.  Types I and II reduce to the common-tail
compression theorem because both preceding gaps are at least `2e`.  In type
III the target preceding gap is `2e - 2`; maximality of the stopping index
and parity of negative good-BONG gaps give the compensating following-gap
bound `2 - 2e`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

theorem alpha_eq_at_common_tail_of_previous_gaps_ge_twoE
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 2)
    (hcurrentValue : a.valueUnit ⟨s, by omega⟩ =
      b.valueUnit ⟨s, by omega⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (hsourcePreviousGap :
      2 * (ramificationIndex K : Int) ≤
        a.order ⟨s, by omega⟩ - a.order ⟨s - 1, by omega⟩)
    (htargetPreviousGap :
      2 * (ramificationIndex K : Int) ≤
        b.order ⟨s, by omega⟩ - b.order ⟨s - 1, by omega⟩) :
    a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩ := by
  let boundary : Fin (n + 2) := ⟨s, hs⟩
  have hboundaryPositive : 0 < boundary.val := by
    simp only [boundary]
    omega
  have hcurrentIndex : boundary.castSucc =
      (⟨s, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentValue' : a.valueUnit boundary.castSucc =
      b.valueUnit boundary.castSucc := by
    rw [hcurrentIndex]
    exact hcurrentValue
  have hcurrent : a.order boundary.castSucc =
      b.order boundary.castSucc := by
    change a.toBONG.order boundary.castSucc =
      b.toBONG.order boundary.castSucc
    rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hcurrentValue'
  have htail' : ∀ j : Fin (n + 3), boundary.val < j.val →
      a.valueUnit j = b.valueUnit j := by
    intro j hj
    exact htail j (by simpa [boundary] using hj)
  have hrightValue : a.valueUnit boundary.succ =
      b.valueUnit boundary.succ := htail' boundary.succ (by simp)
  have hleftValue : a.valueUnit boundary.castSucc =
      b.valueUnit boundary.castSucc := by
    exact hcurrentValue'
  have hlocal : a.leftDefectCandidate boundary boundary =
      b.leftDefectCandidate boundary boundary :=
    a.leftDefectCandidate_self_eq_of_pair_valueUnits_eq b boundary
      hleftValue hrightValue
  have hsourcePrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((a.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        a.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    a.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive (by simpa [boundary] using hsourcePreviousGap)
  have htargetPrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((b.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        b.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    b.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive (by simpa [boundary] using htargetPreviousGap)
  have hprefixSource : ∀ x ∈ a.prefixSegmentAlphaCandidates boundary,
      a.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = a.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    exact a.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
      boundary hboundaryPositive hsourcePrefixAlpha
  have hprefixTarget : ∀ x ∈ b.prefixSegmentAlphaCandidates boundary,
      b.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = b.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    exact b.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
      boundary hboundaryPositive htargetPrefixAlpha
  simpa only [boundary] using
    a.alpha_eq_of_boundary_local_eq b boundary hcurrent htail'
      hprefixSource hprefixTarget hlocal

/-- The boundary calculation needed for Lemma 7.19, type III.  The source
preceding gap is at least `2e`; the target preceding gap is exactly `2e-2`.
The sharper lower bound `2-2e` on the following target gap compensates for
the target prefix alpha dropping from `2e` to `2e-1`. -/
theorem alpha_eq_at_common_tail_of_typeIII_previous_gaps
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 2)
    (hcurrentValue : a.valueUnit ⟨s, by omega⟩ =
      b.valueUnit ⟨s, by omega⟩)
    (htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j)
    (hsourcePreviousGap :
      2 * (ramificationIndex K : Int) ≤
        a.order ⟨s, by omega⟩ - a.order ⟨s - 1, by omega⟩)
    (htargetPreviousGap :
      b.order ⟨s, by omega⟩ - b.order ⟨s - 1, by omega⟩ =
        2 * (ramificationIndex K : Int) - 2)
    (htargetFollowingGap :
      2 - 2 * (ramificationIndex K : Int) ≤
        b.order ⟨s + 1, by omega⟩ - b.order ⟨s, by omega⟩) :
    a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩ := by
  let boundary : Fin (n + 2) := ⟨s, hs⟩
  have hboundaryPositive : 0 < boundary.val := by
    simp only [boundary]
    omega
  have hcurrentIndex : boundary.castSucc =
      (⟨s, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentValue' : a.valueUnit boundary.castSucc =
      b.valueUnit boundary.castSucc := by
    rw [hcurrentIndex]
    exact hcurrentValue
  have hcurrent : a.order boundary.castSucc =
      b.order boundary.castSucc := by
    change a.toBONG.order boundary.castSucc =
      b.toBONG.order boundary.castSucc
    rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hcurrentValue'
  have htail' : ∀ j : Fin (n + 3), boundary.val < j.val →
      a.valueUnit j = b.valueUnit j := by
    intro j hj
    exact htail j (by simpa [boundary] using hj)
  have hrightValue : a.valueUnit boundary.succ =
      b.valueUnit boundary.succ := htail' boundary.succ (by simp)
  have hlocal : a.leftDefectCandidate boundary boundary =
      b.leftDefectCandidate boundary boundary :=
    a.leftDefectCandidate_self_eq_of_pair_valueUnits_eq b boundary
      hcurrentValue' hrightValue
  have hsourcePrefixAlpha : 2 * (ramificationIndex K : ℚ) ≤
      ((a.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        a.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot :=
    a.prefixSegmentAlphaValue_ge_twoE_of_predecessor_gap boundary
      hboundaryPositive (by
        simpa [boundary] using hsourcePreviousGap)
  have htargetPrefixAlphaEq :=
    b.prefixSegmentAlphaValue_eq_twoE_sub_one_of_predecessor_gap_eq
      boundary hboundaryPositive (by
        simpa [boundary] using htargetPreviousGap)
  have htargetPrefixAlpha : 2 * (ramificationIndex K : ℚ) - 1 ≤
      ((b.prefixAlphaSegmentWitness boundary hboundaryPositive).toGoodBONG
        b.good).alphaValue
        (prefixAlphaLocalizationIndex boundary hboundaryPositive).localPivot := by
    rw [htargetPrefixAlphaEq]
  have htargetFollowingGap' :
      2 - 2 * (ramificationIndex K : Int) ≤ b.orderGap boundary := by
    simpa [orderGap, boundary] using htargetFollowingGap
  have hprefixSource : ∀ x ∈ a.prefixSegmentAlphaCandidates boundary,
      a.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = a.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    exact a.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE
      boundary hboundaryPositive hsourcePrefixAlpha
  have hprefixTarget : ∀ x ∈ b.prefixSegmentAlphaCandidates boundary,
      b.halfGapCandidate boundary ≤ x := by
    intro x hx
    have hx' : x = b.prefixSegmentAlphaCandidate boundary
        hboundaryPositive := by
      simpa only [prefixSegmentAlphaCandidates, dif_pos hboundaryPositive,
        Finset.mem_singleton] using hx
    subst x
    exact b.halfGapCandidate_le_prefixSegmentAlphaCandidate_of_alpha_ge_twoE_sub_one
      boundary hboundaryPositive htargetFollowingGap' htargetPrefixAlpha
  simpa only [boundary] using
    a.alpha_eq_of_boundary_local_eq b boundary hcurrent htail'
      hprefixSource hprefixTarget hlocal

theorem Lemma718TypeINormalForm.boundaryAlpha
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hs : s < n + 2) :
    a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩ := by
  let current : Fin (n + 3) := ⟨s, by omega⟩
  let previous : Fin (n + 3) := ⟨s - 1, by omega⟩
  have hcurrentValue : a.valueUnit current = b.valueUnit current := by
    exact (lemma718_typeI_realized_suffix a b s D.targetValues current
      (by simp [current])).symm
  have htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j := by
    intro j hj
    exact (lemma718_typeI_realized_suffix a b s D.targetValues j hj.le).symm
  have hcurrentStrict : R < a.order current := by
    rcases D.typeI.1 with hend | ⟨hsRank, hstrict⟩
    · omega
    · simpa only [current] using hstrict
  have hcurrentLower : R + 1 ≤ a.order current := by omega
  have hprevious : a.order previous =
      R - 2 * (ramificationIndex K : Int) := by
    simpa only [previous] using D.stopping.terminal
  have htargetCurrent : b.order current = a.order current := by
    change b.toBONG.order current = a.toBONG.order current
    rw [b.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit,
      show b.toBONG.valueUnit current = a.toBONG.valueUnit current from
        hcurrentValue.symm]
  have hpreviousLt : previous.val < s := by
    have hsTwo : 2 ≤ s := D.stopping.two_le
    simp only [previous]
    omega
  have htargetPrevious : b.order previous = a.order previous + 1 := by
    calc
      b.order previous = ordUnit K (b.valueUnit previous) :=
        b.toBONG.order_eq_ordUnit previous
      _ = ordUnit K (lemma718TypeITargetValues a s previous) := by
        rw [D.targetValues]
      _ = a.order previous + 1 :=
        ordUnit_lemma718TypeITargetValues_prefix a s previous hpreviousLt
  have hsourceGap : 2 * (ramificationIndex K : Int) ≤
      a.order current - a.order previous := by
    calc
      2 * (ramificationIndex K : Int) ≤
          (R + 1) -
            (R - 2 * (ramificationIndex K : Int)) := by linarith
      _ ≤ a.order current -
          (R - 2 * (ramificationIndex K : Int)) :=
        sub_le_sub_right hcurrentLower _
      _ = a.order current - a.order previous := by rw [hprevious]
  have htargetGap : 2 * (ramificationIndex K : Int) ≤
      b.order current - b.order previous := by
    have hbase : 2 * (ramificationIndex K : Int) ≤
        a.order current - (a.order previous + 1) := by
      calc
        2 * (ramificationIndex K : Int) =
            (R + 1) -
              ((R - 2 * (ramificationIndex K : Int)) + 1) := by ring
        _ ≤ a.order current -
            ((R - 2 * (ramificationIndex K : Int)) + 1) :=
          sub_le_sub_right hcurrentLower _
        _ = a.order current - (a.order previous + 1) := by
          rw [hprevious]
    calc
      2 * (ramificationIndex K : Int) ≤
          a.order current - (a.order previous + 1) := hbase
      _ = b.order current - b.order previous := by
        rw [htargetCurrent, htargetPrevious]
  have hcurrentArg :
      a.valueUnit ⟨s, by omega⟩ = b.valueUnit ⟨s, by omega⟩ := by
    simpa only [current] using hcurrentValue
  have hsourceArg : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨s, by omega⟩ - a.order ⟨s - 1, by omega⟩ := by
    simpa only [current, previous] using hsourceGap
  have htargetArg : 2 * (ramificationIndex K : Int) ≤
      b.order ⟨s, by omega⟩ - b.order ⟨s - 1, by omega⟩ := by
    simpa only [current, previous] using htargetGap
  exact alpha_eq_at_common_tail_of_previous_gaps_ge_twoE
    a b s D.stopping.two_le hs hcurrentArg htail hsourceArg htargetArg

theorem Lemma718TypeIINormalForm.boundaryAlpha
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hs : s < n + 2) :
    a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩ := by
  let current : Fin (n + 3) := ⟨s, by omega⟩
  let previous : Fin (n + 3) := ⟨s - 1, by omega⟩
  have hcurrentValue : a.valueUnit current = b.valueUnit current := by
    exact (lemma718_typeII_realized_suffix a b s D.targetValues current
      (by simp [current])).symm
  have htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j := by
    intro j hj
    exact (lemma718_typeII_realized_suffix a b s D.targetValues j hj.le).symm
  have hcurrentStrict : R < a.order current := by
    rcases D.typeII.1 with hend | ⟨hsRank, hstrict⟩
    · omega
    · simpa only [current] using hstrict
  have hcurrentLower : R + 1 ≤ a.order current := by omega
  have hprevious : a.order previous =
      R - 2 * (ramificationIndex K : Int) := by
    simpa only [previous] using D.stopping.terminal
  have htargetCurrent : b.order current = a.order current := by
    change b.toBONG.order current = a.toBONG.order current
    rw [b.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit,
      show b.toBONG.valueUnit current = a.toBONG.valueUnit current from
        hcurrentValue.symm]
  have hsourceGap : 2 * (ramificationIndex K : Int) ≤
      a.order current - a.order previous := by
    calc
      2 * (ramificationIndex K : Int) ≤
          (R + 1) -
            (R - 2 * (ramificationIndex K : Int)) := by linarith
      _ ≤ a.order current -
          (R - 2 * (ramificationIndex K : Int)) :=
        sub_le_sub_right hcurrentLower _
      _ = a.order current - a.order previous := by rw [hprevious]
  have htargetGap : 2 * (ramificationIndex K : Int) ≤
      b.order current - b.order previous := by
    by_cases hsTwo : s = 2
    · have hpreviousInitial : previous.val < 2 := by
        simp only [previous]
        omega
      have hpreviousValue : b.valueUnit previous = a.valueUnit previous := by
        calc
          b.valueUnit previous = lemma718TypeIITargetValues a s previous :=
            D.targetValues previous
          _ = a.valueUnit previous :=
            lemma718TypeIITargetValues_initial a s previous hpreviousInitial
      have htargetPrevious : b.order previous = a.order previous := by
        change b.toBONG.order previous = a.toBONG.order previous
        rw [b.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
        exact congrArg (ordUnit K) hpreviousValue
      rwa [htargetCurrent, htargetPrevious]
    · rcases D.stopping.even with ⟨d, hd⟩
      have hsAtLeastTwo : 2 ≤ s := D.stopping.two_le
      have hsFour : 4 ≤ s := by omega
      have hpreviousTwo : 2 ≤ previous.val := by
        simp only [previous]
        omega
      have hpreviousLt : previous.val < s := by
        simp only [previous]
        omega
      have htargetPrevious : b.order previous = a.order previous + 1 := by
        calc
          b.order previous = ordUnit K (b.valueUnit previous) :=
            b.toBONG.order_eq_ordUnit previous
          _ = ordUnit K (lemma718TypeIITargetValues a s previous) := by
            rw [D.targetValues]
          _ = a.order previous + 1 :=
            ordUnit_lemma718TypeIITargetValues_changed a s previous
              hpreviousTwo hpreviousLt
      have hbase : 2 * (ramificationIndex K : Int) ≤
          a.order current - (a.order previous + 1) := by
        calc
          2 * (ramificationIndex K : Int) =
              (R + 1) -
                ((R - 2 * (ramificationIndex K : Int)) + 1) := by ring
          _ ≤ a.order current -
              ((R - 2 * (ramificationIndex K : Int)) + 1) :=
            sub_le_sub_right hcurrentLower _
          _ = a.order current - (a.order previous + 1) := by
            rw [hprevious]
      calc
        2 * (ramificationIndex K : Int) ≤
            a.order current - (a.order previous + 1) := hbase
        _ = b.order current - b.order previous := by
          rw [htargetCurrent, htargetPrevious]
  have hcurrentArg :
      a.valueUnit ⟨s, by omega⟩ = b.valueUnit ⟨s, by omega⟩ := by
    simpa only [current] using hcurrentValue
  have hsourceArg : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨s, by omega⟩ - a.order ⟨s - 1, by omega⟩ := by
    simpa only [current, previous] using hsourceGap
  have htargetArg : 2 * (ramificationIndex K : Int) ≤
      b.order ⟨s, by omega⟩ - b.order ⟨s - 1, by omega⟩ := by
    simpa only [current, previous] using htargetGap
  exact alpha_eq_at_common_tail_of_previous_gaps_ge_twoE
    a b s D.stopping.two_le hs hcurrentArg htail hsourceArg htargetArg

theorem Lemma718TypeIIINormalForm.boundaryAlpha
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hs : s < n + 2) :
    a.alpha ⟨s, hs⟩ = b.alpha ⟨s, hs⟩ := by
  let boundary : Fin (n + 2) := ⟨s, hs⟩
  let current : Fin (n + 3) := ⟨s, by omega⟩
  let previous : Fin (n + 3) := ⟨s - 1, by omega⟩
  let following : Fin (n + 3) := ⟨s + 1, by omega⟩
  have hcurrentIndex : boundary.castSucc = current := by
    apply Fin.ext
    rfl
  have hfollowingIndex : boundary.succ = following := by
    apply Fin.ext
    rfl
  have hcurrentValue : a.valueUnit current = b.valueUnit current := by
    exact (lemma718_typeIII_realized_suffix a b s D.targetValues current
      (by simp [current])).symm
  have hfollowingValue : a.valueUnit following = b.valueUnit following := by
    exact (lemma718_typeIII_realized_suffix a b s D.targetValues following
      (by simp [following])).symm
  have htail : ∀ j : Fin (n + 3), s < j.val →
      a.valueUnit j = b.valueUnit j := by
    intro j hj
    exact (lemma718_typeIII_realized_suffix a b s D.targetValues j hj.le).symm
  have hsourceCurrent : a.order current = R := by
    rcases D.typeIII with ⟨hsRank, hcurrent⟩
    simpa only [current] using hcurrent
  have hsourcePrevious : a.order previous =
      R - 2 * (ramificationIndex K : Int) := by
    simpa only [previous] using D.stopping.terminal
  have hsourcePreviousGap : 2 * (ramificationIndex K : Int) ≤
      a.order current - a.order previous := by
    rw [hsourceCurrent, hsourcePrevious]
    omega
  have htargetCurrent : b.order current = a.order current := by
    change b.toBONG.order current = a.toBONG.order current
    rw [b.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hcurrentValue.symm
  have htargetFollowing : b.order following = a.order following := by
    change b.toBONG.order following = a.toBONG.order following
    rw [b.toBONG.order_eq_ordUnit, a.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hfollowingValue.symm
  have hpreviousLt : previous.val < s := by
    have hsTwo : 2 ≤ s := D.stopping.two_le
    simp only [previous]
    omega
  have hpreviousOdd : Odd previous.val := by
    rcases D.stopping.even with ⟨d, hd⟩
    change Odd (s - 1)
    exact ⟨d - 1, by omega⟩
  have htargetPrevious : b.order previous = a.order previous + 2 := by
    calc
      b.order previous = ordUnit K (b.valueUnit previous) :=
        b.toBONG.order_eq_ordUnit previous
      _ = ordUnit K (lemma718TypeIIITargetValues a s previous) := by
        rw [D.targetValues]
      _ = a.order previous + 2 :=
        ordUnit_lemma718TypeIIITargetValues_changed a s previous
          hpreviousLt hpreviousOdd
  have htargetPreviousGap :
      b.order current - b.order previous =
        2 * (ramificationIndex K : Int) - 2 := by
    rw [htargetCurrent, htargetPrevious, hsourceCurrent, hsourcePrevious]
    ring
  have hsourceMaximal : a.order following ≠
      R - 2 * (ramificationIndex K : Int) := by
    simpa only [following] using D.stopping.maximal (by omega)
  have hsourceMaximalAtBoundary : a.order boundary.succ ≠
      R - 2 * (ramificationIndex K : Int) := by
    rw [hfollowingIndex]
    exact hsourceMaximal
  have hsourceFollowingGapNe :
      a.orderGap boundary ≠ -(2 * (ramificationIndex K : Int)) := by
    intro hgap
    apply hsourceMaximalAtBoundary
    unfold orderGap at hgap
    have hcurrentAtBoundary : a.order boundary.castSucc = R := by
      rw [hcurrentIndex]
      exact hsourceCurrent
    rw [hcurrentAtBoundary] at hgap
    omega
  have hsourceFollowingGap :
      2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap boundary := by
    have hlower := a.orderGap_ge_neg_two_mul_e boundary
    by_cases hnegative : a.orderGap boundary < 0
    · rcases a.orderGap_even_of_negative boundary hnegative with ⟨d, hd⟩
      omega
    · have hePos := ramificationIndex_pos (K := K)
      omega
  have htargetFollowingGap :
      2 - 2 * (ramificationIndex K : Int) ≤
        b.order following - b.order current := by
    calc
      2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap boundary :=
        hsourceFollowingGap
      _ = a.order following - a.order current := by
        unfold orderGap
        rw [hfollowingIndex, hcurrentIndex]
      _ = b.order following - b.order current := by
        rw [htargetFollowing, htargetCurrent]
  have hcurrentArg :
      a.valueUnit ⟨s, by omega⟩ = b.valueUnit ⟨s, by omega⟩ := by
    simpa only [current] using hcurrentValue
  have hsourcePreviousArg : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨s, by omega⟩ - a.order ⟨s - 1, by omega⟩ := by
    simpa only [current, previous] using hsourcePreviousGap
  have htargetPreviousArg :
      b.order ⟨s, by omega⟩ - b.order ⟨s - 1, by omega⟩ =
        2 * (ramificationIndex K : Int) - 2 := by
    simpa only [current, previous] using htargetPreviousGap
  have htargetFollowingArg :
      2 - 2 * (ramificationIndex K : Int) ≤
        b.order ⟨s + 1, by omega⟩ - b.order ⟨s, by omega⟩ := by
    simpa only [following, current] using htargetFollowingGap
  exact alpha_eq_at_common_tail_of_typeIII_previous_gaps
    a b s D.stopping.two_le hs hcurrentArg htail hsourcePreviousArg
      htargetPreviousArg htargetFollowingArg

end BONG.GoodBONG

end Bong
