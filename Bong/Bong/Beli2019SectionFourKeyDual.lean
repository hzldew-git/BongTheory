/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPrimary
import Bong.Bong.Beli2019OrderConditionDual

/-!
# Beli (2019), Lemma 4.2(ii) by reverse duality

The paper proves only part (i) of Lemma 4.2 and obtains part (ii) by
reverse duality at the complementary index.  This file records the index
and trigger identities needed for that reduction.  The three BONGs are
reversed and their roles are changed from `a, b, c` to `cDual, bDual,
aDual`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The complementary index of the left endpoint of a boundary is the
right endpoint of the complementary boundary. -/
theorem rev_currentEssentialIndex_eq_nextEssentialIndex_reverse
    (j : RepresentationIndex (n + 1) (n + 1)) :
    Fin.rev (currentEssentialIndex j) = nextEssentialIndex j.reverse := by
  apply Fin.ext
  simp only [Fin.rev, currentEssentialIndex, nextEssentialIndex,
    RepresentationIndex.reverse_val]
  have hpos := j.pos
  have hlarge := j.lt_large
  omega

/-- The complementary index of the right endpoint of a boundary is the
left endpoint of the complementary boundary. -/
theorem rev_nextEssentialIndex_eq_currentEssentialIndex_reverse
    (j : RepresentationIndex (n + 1) (n + 1)) :
    Fin.rev (nextEssentialIndex j) = currentEssentialIndex j.reverse := by
  apply Fin.ext
  simp only [Fin.rev, currentEssentialIndex, nextEssentialIndex,
    RepresentationIndex.reverse_val]
  have hpos := j.pos
  have hlarge := j.lt_large
  omega

/-- Lemma 4.2(ii)'s direct inequality is exactly Lemma 4.2(i)'s direct
inequality for the three swapped reverse-dual order sequences. -/
theorem keyLemmaLeftDirectTrigger_reverseDual_iff
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    {LD MD ND : Lattice K V}
    (aDual : GoodBONG q LD (n + 1))
    (bDual : GoodBONG q MD (n + 1))
    (cDual : GoodBONG q ND (n + 1))
    (haOrders : ∀ i, aDual.order i = -a.order (Fin.rev i))
    (hbOrders : ∀ i, bDual.order i = -b.order (Fin.rev i))
    (hcOrders : ∀ i, cDual.order i = -c.order (Fin.rev i))
    (j : RepresentationIndex (n + 1) (n + 1)) :
    cDual.KeyLemmaLeftDirectTrigger bDual aDual
        (nextEssentialIndex j.reverse) ↔
      a.KeyLemmaRightDirectTrigger b c (currentEssentialIndex j) := by
  unfold KeyLemmaLeftDirectTrigger KeyLemmaRightDirectTrigger
  constructor
  · intro h hiPos hiTwo
    have hleftTwo : 1 < (nextEssentialIndex j.reverse).val := by
      simp only [nextEssentialIndex, RepresentationIndex.reverse_val]
      have hlarge := j.lt_large
      change (currentEssentialIndex j).val + 2 < n + 1 at hiTwo
      simp only [currentEssentialIndex] at hiTwo ⊢
      omega
    have hleftNext :
        (nextEssentialIndex j.reverse).val + 1 < n + 1 := by
      simp only [nextEssentialIndex, RepresentationIndex.reverse_val]
      change 0 < (currentEssentialIndex j).val at hiPos
      simp only [currentEssentialIndex] at hiPos ⊢
      omega
    have hdual := h hleftTwo hleftNext
    rw [haOrders, haOrders, hcOrders, hbOrders] at hdual
    have hci0Bound :
        (currentEssentialIndex j).val + 2 < n + 1 := hiTwo
    have hci0 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val - 2, by omega⟩ =
          ⟨(currentEssentialIndex j).val + 2, hci0Bound⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualTwo : 1 < n + 1 - j.val := hleftTwo
      omega
    have hci1LeftBound :
        (nextEssentialIndex j.reverse).val - 1 < n + 1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (nextEssentialIndex j.reverse).isLt
    have hci1 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val - 1,
          hci1LeftBound⟩ =
          ⟨(currentEssentialIndex j).val + 1, by
            omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualTwo : 1 < n + 1 - j.val := hleftTwo
      omega
    have hai1 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val + 1, hleftNext⟩ =
          ⟨(currentEssentialIndex j).val - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualNext : n + 1 - j.val + 1 < n + 1 := hleftNext
      omega
    have hbi :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val,
          (nextEssentialIndex j.reverse).isLt⟩ =
          ⟨(currentEssentialIndex j).val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      omega
    rw [hci0, hci1, hai1, hbi] at hdual
    linarith
  · intro h hiTwo hiNext
    have hrightPos : 0 < (currentEssentialIndex j).val := by
      simp only [currentEssentialIndex]
      simp only [nextEssentialIndex, RepresentationIndex.reverse_val] at hiNext
      have hlarge := j.lt_large
      omega
    have hrightTwo : (currentEssentialIndex j).val + 2 < n + 1 := by
      simp only [currentEssentialIndex]
      simp only [nextEssentialIndex, RepresentationIndex.reverse_val] at hiTwo
      have hpos := j.pos
      omega
    have horiginal := h hrightPos hrightTwo
    rw [haOrders, haOrders, hcOrders, hbOrders]
    have hci0 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val - 2, by omega⟩ =
          ⟨(currentEssentialIndex j).val + 2, hrightTwo⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualTwo : 1 < n + 1 - j.val := hiTwo
      omega
    have hci1LeftBound :
        (nextEssentialIndex j.reverse).val - 1 < n + 1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (nextEssentialIndex j.reverse).isLt
    have hci1 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val - 1,
          hci1LeftBound⟩ =
          ⟨(currentEssentialIndex j).val + 1, by
            omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualTwo : 1 < n + 1 - j.val := hiTwo
      omega
    have hai1 :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val + 1, hiNext⟩ =
          ⟨(currentEssentialIndex j).val - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      have hdualNext : n + 1 - j.val + 1 < n + 1 := hiNext
      omega
    have hbi :
        Fin.rev ⟨(nextEssentialIndex j.reverse).val,
          (nextEssentialIndex j.reverse).isLt⟩ =
          ⟨(currentEssentialIndex j).val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.rev, nextEssentialIndex,
        RepresentationIndex.reverse_val, currentEssentialIndex]
      have hpos := j.pos
      have hlarge := j.lt_large
      omega
    rw [hci0, hci1, hai1, hbi]
    linarith

/-- Essentiality at the current endpoint becomes essentiality at the next
endpoint of the complementary reverse-dual boundary. -/
theorem isNextEssential_reverseDual_iff_isCurrentEssential
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (cDual : GoodBONG q (Lattice.dualLattice q N) (n + 1))
    (haOrders : ∀ i, aDual.order i = -a.order (Fin.rev i))
    (hcOrders : ∀ i, cDual.order i = -c.order (Fin.rev i))
    (j : RepresentationIndex (n + 1) (n + 1)) :
    cDual.IsNextEssential aDual j.reverse ↔ a.IsCurrentEssential c j := by
  have haSequence := a.orderSequence_eq_reverseNegate_of_orders
    aDual haOrders
  have hcSequence := c.orderSequence_eq_reverseNegate_of_orders
    cDual hcOrders
  unfold IsNextEssential IsCurrentEssential IsEssentialFor
  rw [hcSequence, haSequence,
    ← rev_currentEssentialIndex_eq_nextEssentialIndex_reverse]
  exact BeliOrderSequence.reverseNegate_isEssentialFor_iff
    a.orderSequence c.orderSequence (currentEssentialIndex j)

set_option maxHeartbeats 800000 in
-- Three simultaneous reverse-dual choices keep all pairwise alpha values aligned.
/-- Choose reverse-dual BONGs for all three lattices with the pairwise
representation-alpha identities needed in Lemma 4.2. -/
theorem exists_sectionFourReverseDualTriple
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1)) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
      (cDual : GoodBONG q (Lattice.dualLattice q N) (n + 1)),
      (∀ i, aDual.order i = -a.order (Fin.rev i)) ∧
      (∀ i, bDual.order i = -b.order (Fin.rev i)) ∧
      (∀ i, cDual.order i = -c.order (Fin.rev i)) ∧
      (∀ i : RepresentationIndex (n + 1) (n + 1),
        bDual.representationAlpha aDual i.reverse =
          a.representationAlpha b i) ∧
      (∀ i : RepresentationIndex (n + 1) (n + 1),
        cDual.representationAlpha aDual i.reverse =
          a.representationAlpha c i) ∧
      (∀ i : RepresentationIndex (n + 1) (n + 1),
        cDual.representationAlpha bDual i.reverse =
          b.representationAlpha c i) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        cDual.truncatedPrefixDefect bDual epsilon p r =
          b.truncatedPrefixDefect c epsilon
            (n + 1 - r) (n + 1 - p)) := by
  rcases a.exists_reverseDual_with_alpha with
    ⟨aDual, _, haValues, haOrders, haAlpha⟩
  rcases b.exists_reverseDual_with_alpha with
    ⟨bDual, _, hbValues, hbOrders, hbAlpha⟩
  rcases c.exists_reverseDual_with_alpha with
    ⟨cDual, _, hcValues, hcOrders, hcAlpha⟩
  have haUnits : ∀ i,
      aDual.toBONG.valueUnit i =
        (a.toBONG.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    exact haValues i
  have hbUnits : ∀ i,
      bDual.toBONG.valueUnit i =
        (b.toBONG.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    exact hbValues i
  have hcUnits : ∀ i,
      cDual.toBONG.valueUnit i =
        (c.toBONG.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    exact hcValues i
  have habDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p) := by
    intro p r hp hr epsilon
    exact truncatedPrefixDefect_reverseDual_swap_general
      a b aDual bDual haUnits hbUnits haAlpha hbAlpha p r hp hr epsilon
  have hacDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        cDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect c epsilon
            (n + 1 - r) (n + 1 - p) := by
    intro p r hp hr epsilon
    exact truncatedPrefixDefect_reverseDual_swap_general
      a c aDual cDual haUnits hcUnits haAlpha hcAlpha p r hp hr epsilon
  have hbcDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        cDual.truncatedPrefixDefect bDual epsilon p r =
          b.truncatedPrefixDefect c epsilon
            (n + 1 - r) (n + 1 - p) := by
    intro p r hp hr epsilon
    exact truncatedPrefixDefect_reverseDual_swap_general
      b c bDual cDual hbUnits hcUnits hbAlpha hcAlpha p r hp hr epsilon
  refine ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
    ?_, ?_, ?_, habDefect, hbcDefect⟩
  · intro i
    exact a.representationAlpha_reverseDual_swap b aDual bDual
      haOrders hbOrders habDefect i
  · intro i
    exact a.representationAlpha_reverseDual_swap c aDual cDual
      haOrders hcOrders hacDefect i
  · intro i
    exact b.representationAlpha_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbcDefect i

set_option maxHeartbeats 1000000 in
/-- Once Lemma 4.2(i)'s direct branch is known uniformly, Lemma 4.2(ii)'s
direct branch follows by applying it to the swapped reverse-dual triple. -/
theorem currentDirectBounds_of_nextDirectBounds_reverseDual
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hnext : ∀ {L' M' N' : Lattice K V}
      (x : GoodBONG q L' (n + 1))
      (y : GoodBONG q M' (n + 1))
      (z : GoodBONG q N' (n + 1)),
      x.RepresentationOrderCondition y le_rfl →
      x.RepresentationDefectCondition y →
      y.RepresentationOrderCondition z le_rfl →
      y.RepresentationDefectCondition z →
      ∀ k : RepresentationIndex (n + 1) (n + 1),
        x.IsNextEssential z k →
        x.KeyLemmaLeftDirectTrigger y z (nextEssentialIndex k) →
        x.representationAlpha z k ≤ x.representationAlpha y k ∧
          x.representationAlpha z k ≤ y.representationAlpha z k)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.IsCurrentEssential c j)
    (hdirect : a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationAlpha b j ∧
      a.representationAlpha c j ≤ b.representationAlpha c j := by
  rcases a.exists_sectionFourReverseDualTriple b c with
    ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
      habAlpha, hacAlpha, hbcAlpha, habComparison, hbcComparison⟩
  have hcbOrder : cDual.RepresentationOrderCondition bDual le_rfl :=
    b.representationOrderCondition_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbc
  have hbaOrder : bDual.RepresentationOrderCondition aDual le_rfl :=
    a.representationOrderCondition_reverseDual_swap b aDual bDual
      haOrders hbOrders hab
  have hcbDefect : cDual.RepresentationDefectCondition bDual :=
    b.representationDefectCondition_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbcComparison hbcDefect
  have hbaDefect : bDual.RepresentationDefectCondition aDual :=
    a.representationDefectCondition_reverseDual_swap b aDual bDual
      haOrders hbOrders habComparison habDefect
  have hnextEssential : cDual.IsNextEssential aDual j.reverse :=
    (a.isNextEssential_reverseDual_iff_isCurrentEssential c
      aDual cDual haOrders hcOrders j).2 hcurrent
  have hleftDirect : cDual.KeyLemmaLeftDirectTrigger bDual aDual
      (nextEssentialIndex j.reverse) :=
    (a.keyLemmaLeftDirectTrigger_reverseDual_iff b c
      aDual bDual cDual haOrders hbOrders hcOrders j).2 hdirect
  have hbounds := hnext cDual bDual aDual hcbOrder hcbDefect hbaOrder
    hbaDefect j.reverse hnextEssential hleftDirect
  constructor
  · calc
      a.representationAlpha c j =
          cDual.representationAlpha aDual j.reverse := (hacAlpha j).symm
      _ ≤ bDual.representationAlpha aDual j.reverse := hbounds.2
      _ = a.representationAlpha b j := habAlpha j
  · calc
      a.representationAlpha c j =
          cDual.representationAlpha aDual j.reverse := (hacAlpha j).symm
      _ ≤ cDual.representationAlpha bDual j.reverse := hbounds.1
      _ = b.representationAlpha c j := hbcAlpha j

set_option maxHeartbeats 1000000 in
-- The fallback transport carries the three aligned reverse-dual BONGs and
-- two defect-condition proofs through the complementary index calculation.
/-- Lemma 4.2(ii)'s fallback branch follows from part (i)'s fallback branch
on the swapped reverse-dual triple. -/
theorem currentFallbackBound_of_nextFallbackBound_reverseDual
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hnext : ∀ {L' M' N' : Lattice K V}
      (x : GoodBONG q L' (n + 1))
      (y : GoodBONG q M' (n + 1))
      (z : GoodBONG q N' (n + 1)),
      x.RepresentationOrderCondition y le_rfl →
      x.RepresentationDefectCondition y →
      y.RepresentationOrderCondition z le_rfl →
      y.RepresentationDefectCondition z →
      ∀ k : RepresentationIndex (n + 1) (n + 1),
        ∀ hk : 1 < k.val ∧ k.val + 1 < n + 1,
        x.IsNextEssential z k →
        ¬x.KeyLemmaLeftDirectTrigger y z (nextEssentialIndex k) →
        x.representationAlpha z k ≤ x.nextFallbackBound y k hk.2)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hprev : 1 < j.val)
    (hcurrent : a.IsCurrentEssential c j)
    (hfailure : ¬a.KeyLemmaRightDirectTrigger b c
      (currentEssentialIndex j)) :
    a.representationAlpha c j ≤ a.currentFallbackBound b c j hprev := by
  rcases a.exists_sectionFourReverseDualTriple b c with
    ⟨aDual, bDual, cDual, haOrders, hbOrders, hcOrders,
      habAlpha, hacAlpha, hbcAlpha, habComparison, hbcComparison⟩
  have hcbOrder : cDual.RepresentationOrderCondition bDual le_rfl :=
    b.representationOrderCondition_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbc
  have hbaOrder : bDual.RepresentationOrderCondition aDual le_rfl :=
    a.representationOrderCondition_reverseDual_swap b aDual bDual
      haOrders hbOrders hab
  have hcbDefect : cDual.RepresentationDefectCondition bDual :=
    b.representationDefectCondition_reverseDual_swap c bDual cDual
      hbOrders hcOrders hbcComparison hbcDefect
  have hbaDefect : bDual.RepresentationDefectCondition aDual :=
    a.representationDefectCondition_reverseDual_swap b aDual bDual
      haOrders hbOrders habComparison habDefect
  have hnextEssential : cDual.IsNextEssential aDual j.reverse :=
    (a.isNextEssential_reverseDual_iff_isCurrentEssential c
      aDual cDual haOrders hcOrders j).2 hcurrent
  have hleftFailure : ¬cDual.KeyLemmaLeftDirectTrigger bDual aDual
      (nextEssentialIndex j.reverse) := by
    simpa only [a.keyLemmaLeftDirectTrigger_reverseDual_iff b c
      aDual bDual cDual haOrders hbOrders hcOrders j] using hfailure
  have hdualInterior : 1 < j.reverse.val ∧
      j.reverse.val + 1 < n + 1 := by
    have hjNext : j.val + 1 < n + 1 := by
      by_contra hnot
      have hterminal : (currentEssentialIndex j).val + 2 = n + 1 := by
        simp only [currentEssentialIndex]
        have := j.lt_large
        omega
      exact hfailure (a.keyLemmaRightDirectTrigger_of_penultimate
        b c (currentEssentialIndex j) hterminal)
    exact (RepresentationIndex.reverse_interior_iff j).2
      ⟨hprev, hjNext⟩
  have hbound := hnext cDual bDual aDual hcbOrder hcbDefect
    hbaOrder hbaDefect j.reverse hdualInterior hnextEssential hleftFailure
  have hnextIndex : nextRepresentationIndex j.reverse hdualInterior.2 =
      (previousRepresentationIndex j hprev).reverse := by
    let left := nextRepresentationIndex j.reverse hdualInterior.2
    let right := (previousRepresentationIndex j hprev).reverse
    have hval : left.val = right.val := by
      dsimp only [left, right, nextRepresentationIndex,
        previousRepresentationIndex]
      simp only [RepresentationIndex.reverse_val]
      have hpos := j.pos
      have hlt := j.lt_large
      omega
    have hproof : left = right := by
      apply RepresentationIndex.ext
      exact hval
    exact hproof
  have horderCurrent :
      cDual.order ⟨j.reverse.val, j.reverse.lt_large⟩ =
        -c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hlarge := j.lt_large
    omega
  have horderNext :
      cDual.order ⟨j.reverse.val + 1, hdualInterior.2⟩ =
        -c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ := by
    rw [hcOrders]
    congr 2
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hlarge := j.lt_large
    have hpos := j.pos
    omega
  rw [hacAlpha j] at hbound
  unfold nextFallbackBound at hbound
  unfold currentFallbackBound
  rw [hnextIndex, hbcAlpha (previousRepresentationIndex j hprev),
    horderCurrent, horderNext] at hbound
  have hshift :
      ((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) =
      ((-c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
        -c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ) := by
    push_cast
    ring
  simpa only [hshift] using hbound

end BONG.GoodBONG

end Bong
