/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92Statement

/-!
# Beli (2019), Lemma 9.2: propagation after deleting the head

The low-rank parts of Lemma 9.2 establish one equality between a global alpha
and the corresponding alpha of the projected tail.  Property P1 then
propagates that equality to every later index.  This file proves that
paper-independent propagation argument once and packages the two instances
used in ranks four and at least five.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n N : Nat}

/-- If the alpha of the projected tail is below the one left-defect candidate
lost by deleting the head, it is also below the corresponding global alpha. -/
theorem tailAlpha_le_shift_of_firstLeftDefectBound
    (b : GoodBONG q L (n + 2)) (i : Fin n)
    (hfirst : b.tail.alpha i ≤
      b.leftDefectCandidate i.succ (0 : Fin (n + 1))) :
    b.tail.alpha i ≤ b.alpha i.succ := by
  change b.tail.alpha i ≤
    (b.alphaCandidates i.succ).min' (b.alphaCandidates_nonempty i.succ)
  apply Finset.le_min'
  intro y hy
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
  · have htail := b.tail.alpha_le_halfGapCandidate i
    simpa only [b.halfGapCandidate_tail i] using htail
  · by_cases hj : j = (0 : Fin (n + 1))
    · subst j
      exact hfirst
    · have hjpos : 0 < j.1 := by
        by_contra hnot
        have : j.1 = 0 := by omega
        exact hj (Fin.ext this)
      let jTail : Fin n := ⟨j.1 - 1, by omega⟩
      have hsucc : jTail.succ = j := by
        apply Fin.ext
        simp only [jTail, Fin.val_succ]
        omega
      have hjTailLe : jTail ≤ i := by
        change j.1 - 1 ≤ i.1
        change j.1 ≤ i.succ.1 at hji
        simp only [Fin.val_succ] at hji
        omega
      have htail := b.tail.alpha_le_leftDefectCandidate hjTailLe
      rw [b.leftDefectCandidate_tail, hsucc] at htail
      exact htail
  · have hjpos : 0 < j.1 := by
      change i.succ.1 ≤ j.1 at hij
      simp only [Fin.val_succ] at hij
      omega
    let jTail : Fin n := ⟨j.1 - 1, by omega⟩
    have hsucc : jTail.succ = j := by
      apply Fin.ext
      simp only [jTail, Fin.val_succ]
      omega
    have hiLeTail : i ≤ jTail := by
      change i.1 ≤ j.1 - 1
      change i.succ.1 ≤ j.1 at hij
      simp only [Fin.val_succ] at hij
      omega
    have htail := b.tail.alpha_le_rightDefectCandidate hiLeTail
    rw [b.rightDefectCandidate_tail, hsucc] at htail
    exact htail

/-- If the one left-defect candidate lost by deleting the head is strictly
smaller than the projected-tail alpha, that candidate is the shifted global
alpha.  This is the converse branch of the preceding candidate comparison. -/
theorem alpha_shift_eq_firstLeftDefect_of_lt_tailAlpha
    (b : GoodBONG q L (n + 2)) (i : Fin n)
    (hfirst : b.leftDefectCandidate i.succ (0 : Fin (n + 1)) <
      b.tail.alpha i) :
    b.alpha i.succ =
      b.leftDefectCandidate i.succ (0 : Fin (n + 1)) := by
  apply le_antisymm
  · exact b.alpha_le_leftDefectCandidate (Fin.zero_le _)
  · change b.leftDefectCandidate i.succ (0 : Fin (n + 1)) ≤
      (b.alphaCandidates i.succ).min' (b.alphaCandidates_nonempty i.succ)
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
    · have htail := b.tail.alpha_le_halfGapCandidate i
      exact hfirst.le.trans (by
        simpa only [b.halfGapCandidate_tail i] using htail)
    · by_cases hj : j = (0 : Fin (n + 1))
      · subst j
        exact le_rfl
      · have hjpos : 0 < j.1 := by
          by_contra hnot
          have : j.1 = 0 := by omega
          exact hj (Fin.ext this)
        let jTail : Fin n := ⟨j.1 - 1, by omega⟩
        have hsucc : jTail.succ = j := by
          apply Fin.ext
          simp only [jTail, Fin.val_succ]
          omega
        have hjTailLe : jTail ≤ i := by
          change j.1 - 1 ≤ i.1
          change j.1 ≤ i.succ.1 at hji
          simp only [Fin.val_succ] at hji
          omega
        have htail := b.tail.alpha_le_leftDefectCandidate hjTailLe
        rw [b.leftDefectCandidate_tail, hsucc] at htail
        exact hfirst.le.trans htail
    · have hjpos : 0 < j.1 := by
        change i.succ.1 ≤ j.1 at hij
        simp only [Fin.val_succ] at hij
        omega
      let jTail : Fin n := ⟨j.1 - 1, by omega⟩
      have hsucc : jTail.succ = j := by
        apply Fin.ext
        simp only [jTail, Fin.val_succ]
        omega
      have hiLeTail : i ≤ jTail := by
        change i.1 ≤ j.1 - 1
        change i.succ.1 ≤ j.1 at hij
        simp only [Fin.val_succ] at hij
        omega
      have htail := b.tail.alpha_le_rightDefectCandidate hiLeTail
      rw [b.rightDefectCandidate_tail, hsucc] at htail
      exact hfirst.le.trans htail

/-- Strict failure of the head-deletion equality forces the lost first
left-defect candidate to be strictly below the projected-tail alpha. -/
theorem firstLeftDefect_lt_tailAlpha_of_alpha_shift_lt
    (b : GoodBONG q L (n + 2)) (i : Fin n)
    (hshift : b.alpha i.succ < b.tail.alpha i) :
    b.leftDefectCandidate i.succ (0 : Fin (n + 1)) <
      b.tail.alpha i := by
  by_contra hnot
  have hle : b.tail.alpha i ≤
      b.leftDefectCandidate i.succ (0 : Fin (n + 1)) :=
    le_of_not_gt hnot
  have hreverse := b.tailAlpha_le_shift_of_firstLeftDefectBound i hle
  exact (not_lt_of_ge hreverse) hshift

set_option maxHeartbeats 800000 in
-- Fin-index normalization and nested `WithTop` arithmetic require extra
-- elaboration time in this propagation argument.
/-- Equality at one head-deletion boundary propagates to every later alpha.
This is the abstract form of the two higher-rank continuation arguments in
the proof of Lemma 9.2. -/
theorem alphaValue_shift_eq_tail_of_base_eq
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (p i : Fin n) (hpi : p ≤ i)
    (hbase : b.alphaValue p.succ = b.tail.alphaValue p) :
    b.alphaValue i.succ = b.tail.alphaValue i := by
  cases n with
  | zero => exact Fin.elim0 p
  | succ m =>
    have hendpoint := b.tail.alphaRightEndpoint_antitone hpi
    unfold alphaRightEndpoint at hendpoint
    simp only [b.order_goodTail] at hendpoint
    have htailQ :
        b.tail.alphaValue i ≤
          ((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) +
            b.tail.alphaValue p := by
      rw [Int.cast_sub]
      linarith
    have htailTop :
        (b.tail.alphaValue i : WithTop ℚ) ≤
          (((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) :
            WithTop ℚ) +
            (b.tail.alphaValue p : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr htailQ
    have hbaseCandidate :
        (b.tail.alphaValue p : WithTop ℚ) ≤
          b.leftDefectCandidate p.succ (0 : Fin (m + 1 + 1)) := by
      rw [← hbase, b.coe_alphaValue]
      exact b.alpha_le_leftDefectCandidate (Fin.zero_le _)
    have hcombine :
        (((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) :
            WithTop ℚ) +
            b.leftDefectCandidate p.succ (0 : Fin (m + 1 + 1)) =
          b.leftDefectCandidate i.succ (0 : Fin (m + 1 + 1)) := by
      have hcoeff :
          ((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) +
              ((b.order p.succ.succ -
                b.order (0 : Fin (m + 1 + 1)).castSucc : Int) : ℚ) =
            ((b.order i.succ.succ -
              b.order (0 : Fin (m + 1 + 1)).castSucc : Int) : ℚ) := by
        simp only [Int.cast_sub]
        ring
      unfold leftDefectCandidate
      rw [← add_assoc, ← WithTop.coe_add, hcoeff]
    have hfirst : b.tail.alpha i ≤
        b.leftDefectCandidate i.succ (0 : Fin (m + 1 + 1)) := by
      rw [← b.tail.coe_alphaValue]
      calc
        (b.tail.alphaValue i : WithTop ℚ) ≤
            (((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) :
                WithTop ℚ) +
              (b.tail.alphaValue p : WithTop ℚ) := htailTop
        _ ≤ (((b.order i.succ.succ - b.order p.succ.succ : Int) : ℚ) :
                WithTop ℚ) +
              b.leftDefectCandidate p.succ (0 : Fin (m + 1 + 1)) :=
          add_le_add_right hbaseCandidate _
        _ = b.leftDefectCandidate i.succ (0 : Fin (m + 1 + 1)) := hcombine
    apply WithTop.coe_injective
    rw [b.coe_alphaValue, b.tail.coe_alphaValue]
    exact le_antisymm (b.alpha_shift_le_tail i)
      (b.tailAlpha_le_shift_of_firstLeftDefectBound i hfirst)

set_option maxHeartbeats 800000 in
-- The constructor packages the preceding propagation theorem across all
-- later boundaries, which gives the elaborator a larger finite-index term.
/-- A rank-four base equality at paper index `i = 3` supplies every equality
required by Lemma 9.2, including its conditional early clause. -/
theorem exists_lemma92Transform_of_earlyBaseAgreement
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (N + 4))
    (hfirst : c.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)))
    (hbase : c.alphaValue (2 : Fin (N + 3)) =
      c.tail.alphaValue (1 : Fin (N + 2))) :
    Nonempty (Beli2019Lemma92Transform a) := by
  apply exists_lemma92Transform_of_selfTailAgreement (N := N) a c hfirst
  · intro i hi
    have hpi : (1 : Fin (N + 2)) ≤ i := by
      change (1 : Nat) ≤ i.1
      omega
    exact c.alphaValue_shift_eq_tail_of_base_eq
      (1 : Fin (N + 2)) i hpi hbase
  · intro _
    exact hbase

set_option maxHeartbeats 800000 in
-- The rank-five boundary is propagated through a dependent family of `Fin`
-- indices and needs a modest local heartbeat allowance.
/-- In the complementary branch, the paper constructs the base equality at
`i = 4`.  From rank five onward it propagates to every required later index;
the early clause is vacuous because all three early alternatives are absent. -/
theorem exists_lemma92Transform_of_laterBaseAgreement
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (N + 5))
    (hfirst : c.valueUnit (0 : Fin (N + 5)) =
      a.valueUnit (0 : Fin (N + 5)))
    (hnotEarly : ¬a.Lemma92EarlyAlternative)
    (hbase : c.alphaValue (3 : Fin (N + 4)) =
      c.tail.alphaValue (2 : Fin (N + 3))) :
    Nonempty (Beli2019Lemma92Transform a) := by
  apply exists_lemma92Transform_of_selfTailAgreement (N := N + 1) a c hfirst
  · intro i hi
    have hpi : (2 : Fin (N + 3)) ≤ i := by
      change (2 : Nat) ≤ i.1
      omega
    exact c.alphaValue_shift_eq_tail_of_base_eq
      (2 : Fin (N + 3)) i hpi hbase
  · intro hcase
    exact (hnotEarly hcase).elim

end BONG.GoodBONG

end Bong
