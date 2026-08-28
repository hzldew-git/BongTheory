/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailRepresentation
import Bong.Bong.Beli2019Lemma93TailAlpha
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Lemma 9.3: the central trigger after deleting equal heads

The numerical trigger in condition 2.1(iii) can occur only at an essential
index (Lemma 2.13).  At such an index the two equalities `A_i = A_i*`
selected in Lemma 9.3 identify both representation-alpha terms, so the tail
trigger shifts to the corresponding trigger for the original BONGs.
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

private theorem representationIndex_eq_of_val_eq
    {m n : Nat} {i j : RepresentationIndex m n} (h : i.val = j.val) :
    i = j := by
  cases i
  cases j
  simp_all

/-- Lemma 2.13 for condition (iii): its strict numerical trigger forces the
corresponding index to be essential. -/
theorem isEssentialFor_of_centralAlphaTrigger
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (i : CentralRepresentationIndex (N + 1) (N + 1))
    (htrigger : a.centralAlphaTrigger b i) :
    a.IsEssentialFor b ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ := by
  unfold IsEssentialFor BeliOrderSequence.IsEssentialFor
  constructor
  · intro hi0 hiNext
    change 0 < i.val - 1 at hi0
    change i.val - 1 + 1 < N + 1 at hiNext
    have hfirst := htrigger.1
    simp only [orderSequence_at]
    have hleft :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (N + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    have hright :
        (⟨i.val - 1 + 1, by omega⟩ : Fin (N + 1)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [hleft, hright]
    exact hfirst
  · intro hiTwo hiNext
    change 1 < i.val - 1 at hiTwo
    change i.val - 1 + 2 < N + 1 at hiNext
    have hiVal : 2 < i.val := by omega
    have hiNextVal : i.val + 1 < N + 1 := by omega
    let previous : RepresentationIndex (N + 1) (N + 1) := i.previous
    let current : RepresentationIndex (N + 1) (N + 1) :=
      i.current i.lt_large.le
    have hpreviousTwo : 1 < previous.val := by
      simp only [previous, CentralRepresentationIndex.previous]
      omega
    have hcurrentNext : current.val + 1 < N + 1 := by
      simp only [current, CentralRepresentationIndex.current]
      omega
    have hpreviousRaw := by
      letI : Beli2006AlphaLaws.{u, w} K := targetLaws
      exact (a.representationAlpha_le_prime b previous).trans
        (a.representationAlphaPrime_le_primaryRightHalfGap
          b previous hpreviousTwo)
    have hcurrentRaw :=
      (a.representationAlpha_le_prime b current).trans
        (a.representationAlphaPrime_le_primaryLeftHalfGap
          b current hcurrentNext)
    have hprevious := hpreviousRaw
    rw [← a.coe_representationAlphaValue b previous] at hprevious
    norm_cast at hprevious
    have hcurrent := hcurrentRaw
    rw [← a.coe_representationAlphaValue b current] at hcurrent
    norm_cast at hcurrent
    have hsum := htrigger.2
    have hiOrdinary : i.val ≤ N + 1 := i.lt_large.le
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos hiOrdinary] at hsum
    norm_cast at hsum
    unfold halfGapValue orderGap at hprevious hcurrent
    have hprevious' :
        a.representationAlphaValue b previous ≤
          ((a.order ⟨i.val - 1, by omega⟩ : ℚ) -
            (b.order ⟨i.val - 2, by omega⟩ : ℚ)) +
            (((b.order ⟨i.val - 2, by omega⟩ : ℚ) -
              (b.order ⟨i.val - 3, by omega⟩ : ℚ)) / 2 +
              (ramificationIndex K : ℚ)) := by
      dsimp only [previous, CentralRepresentationIndex.previous] at hprevious
      push_cast at hprevious
      have htargetIndex :
          (⟨i.val - 1 - 1, by omega⟩ : Fin (N + 1)) =
            ⟨i.val - 2, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 - 1 = i.val - 2
        omega
      let p : Fin N := ⟨i.val - 1 - 2, by omega⟩
      have hp : p = ⟨i.val - 3, by omega⟩ := by
        apply Fin.ext
        change i.val - 1 - 2 = i.val - 3
        omega
      have hpSucc : p.succ = ⟨i.val - 2, by omega⟩ := by
        apply Fin.ext
        simp only [p, Fin.val_succ]
        omega
      have hpCast : p.castSucc = ⟨i.val - 3, by omega⟩ := by
        apply Fin.ext
        simp only [p, Fin.val_castSucc]
        omega
      change a.representationAlphaValue b previous ≤
        (a.order ⟨i.val - 1, by omega⟩ : ℚ) -
            (b.order ⟨i.val - 1 - 1, by omega⟩ : ℚ) +
          (((b.order p.succ : ℚ) - (b.order p.castSucc : ℚ)) / 2 +
            (ramificationIndex K : ℚ)) at hprevious
      rw [htargetIndex, hpSucc, hpCast] at hprevious
      exact hprevious
    have hcurrent' :
        a.representationAlphaValue b current ≤
          ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
            (b.order ⟨i.val - 1, by omega⟩ : ℚ)) +
            (((a.order ⟨i.val + 1, hiNextVal⟩ : ℚ) -
              (a.order ⟨i.val, i.lt_large⟩ : ℚ)) / 2 +
              (ramificationIndex K : ℚ)) := by
      dsimp only [current, CentralRepresentationIndex.current] at hcurrent
      push_cast at hcurrent
      let p : Fin N := ⟨i.val, by omega⟩
      have hpSucc : p.succ = ⟨i.val + 1, hiNextVal⟩ := by
        apply Fin.ext
        simp only [p, Fin.val_succ]
      have hpCast : p.castSucc = ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        simp only [p, Fin.val_castSucc]
      change a.representationAlphaValue b current ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
            (b.order ⟨i.val - 1, by omega⟩ : ℚ) +
          (((a.order p.succ : ℚ) - (a.order p.castSucc : ℚ)) / 2 +
            (ramificationIndex K : ℚ)) at hcurrent
      rw [hpSucc, hpCast] at hcurrent
      exact hcurrent
    have hsum' :
        2 * (ramificationIndex K : ℚ) +
            (a.order ⟨i.val - 1, by omega⟩ : ℚ) <
          a.representationAlphaValue b previous +
            ((b.order ⟨i.val - 1, by omega⟩ : ℚ) +
              a.representationAlphaValue b current) := by
      push_cast at hsum
      simpa only [previous, current,
        CentralRepresentationIndex.previous,
        CentralRepresentationIndex.current] using hsum
    have hordersQ :
        (b.order ⟨i.val - 3, by omega⟩ : ℚ) +
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) <
          (a.order ⟨i.val, by omega⟩ : ℚ) +
            (a.order ⟨i.val + 1, by omega⟩ : ℚ) := by
      linarith [hprevious', hcurrent', hsum']
    have hordersZ :
        b.order ⟨i.val - 3, by omega⟩ +
            b.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, by omega⟩ +
            a.order ⟨i.val + 1, hiNextVal⟩ := by
      exact_mod_cast hordersQ
    simp only [orderSequence_at]
    have hleftTwo :
        (⟨i.val - 1 - 2, by omega⟩ : Fin (N + 1)) =
          ⟨i.val - 3, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 2 = i.val - 3
      omega
    have hleftOne :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (N + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    have hrightOne :
        (⟨i.val - 1 + 1, by omega⟩ : Fin (N + 1)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hrightTwo :
        (⟨i.val - 1 + 2, by omega⟩ : Fin (N + 1)) =
          ⟨i.val + 1, hiNextVal⟩ := by
      apply Fin.ext
      change i.val - 1 + 2 = i.val + 1
      omega
    rw [hleftTwo, hleftOne, hrightOne, hrightTwo]
    exact hordersZ

/-- At the essential index forced by Lemma 2.13, the two selected equalities
`A_i = A_i*` lift the tail trigger to the shifted original trigger. -/
theorem centralAlphaTrigger_tailShift_of_essentialAlpha
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (b : GoodBONG r M (N + 2))
    (hrepresentationAlpha :
      ∀ j : RepresentationIndex (N + 1) (N + 1),
        (a.tail.IsCurrentEssential b.tail j ∨
          a.tail.IsNextEssential b.tail j) →
        a.tail.representationAlpha b.tail j =
          a.representationAlpha b j.tailShift)
    (i : CentralRepresentationIndex (N + 1) (N + 1))
    (htrigger : a.tail.centralAlphaTrigger b.tail i) :
    a.centralAlphaTrigger b i.tailShift := by
  have hiTail : i.val ≤ N + 1 := i.lt_large.le
  have hiOriginal : i.tailShift.val ≤ N + 2 := by
    simp only [CentralRepresentationIndex.tailShift_val]
    omega
  have hessential :=
    a.tail.isEssentialFor_of_centralAlphaTrigger
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      b.tail i htrigger
  have hpreviousEssential :
      a.tail.IsNextEssential b.tail i.previous := by
    simpa only [IsNextEssential, nextEssentialIndex,
      CentralRepresentationIndex.previous] using hessential
  have hcurrentEssential :
      a.tail.IsCurrentEssential b.tail (i.current hiTail) := by
    simpa only [IsCurrentEssential, currentEssentialIndex,
      CentralRepresentationIndex.current] using hessential
  have hpreviousIndex :
      i.previous.tailShift = i.tailShift.previous := by
    apply representationIndex_eq_of_val_eq
    simp only [RepresentationIndex.tailShift_val,
      CentralRepresentationIndex.previous,
      CentralRepresentationIndex.tailShift_val]
    have := i.one_lt
    omega
  have hcurrentIndex :
      (i.current hiTail).tailShift =
        i.tailShift.current hiOriginal := by
    apply representationIndex_eq_of_val_eq
    simp only [RepresentationIndex.tailShift_val,
      CentralRepresentationIndex.current,
      CentralRepresentationIndex.tailShift_val]
  have hpreviousAlpha :
      a.tail.representationAlpha b.tail i.previous =
        a.representationAlpha b i.tailShift.previous := by
    rw [← hpreviousIndex]
    exact hrepresentationAlpha i.previous (Or.inr hpreviousEssential)
  have hcurrentAlpha :
      a.tail.representationAlpha b.tail (i.current hiTail) =
        a.representationAlpha b (i.tailShift.current hiOriginal) := by
    rw [← hcurrentIndex]
    exact hrepresentationAlpha (i.current hiTail) (Or.inl hcurrentEssential)
  have hBPreviousTwo :
      b.tail.order ⟨i.val - 2, by omega⟩ =
        b.order ⟨i.tailShift.val - 2, by
          have := i.tailShift.lt_large
          omega⟩ := by
    rw [b.order_goodTail]
    apply congrArg b.order
    apply Fin.ext
    change (i.val - 2) + 1 = (i.val + 1) - 2
    have := i.one_lt
    omega
  have hACurrent :
      a.tail.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.tailShift.val, i.tailShift.lt_large⟩ := by
    rw [a.order_goodTail]
    congr 1
  have hAPrevious :
      a.tail.order ⟨i.val - 1, by omega⟩ =
        a.order ⟨i.tailShift.val - 1, by
          have := i.tailShift.lt_large
          omega⟩ := by
    rw [a.order_goodTail]
    apply congrArg a.order
    apply Fin.ext
    change (i.val - 1) + 1 = (i.val + 1) - 1
    have := i.one_lt
    omega
  have hBPrevious :
      b.tail.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.tailShift.val - 1, by
          have := i.tailShift.lt_large
          omega⟩ := by
    rw [b.order_goodTail]
    apply congrArg b.order
    apply Fin.ext
    change (i.val - 1) + 1 = (i.val + 1) - 1
    have := i.one_lt
    omega
  unfold centralAlphaTrigger at htrigger ⊢
  constructor
  · rw [← hBPreviousTwo, ← hACurrent]
    exact htrigger.1
  · have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum ⊢
    rw [dif_pos hiTail] at hsum
    rw [dif_pos hiOriginal]
    rw [a.tail.coe_representationAlphaValue b.tail i.previous,
      a.tail.coe_representationAlphaValue b.tail (i.current hiTail),
      hpreviousAlpha, hcurrentAlpha] at hsum
    rw [a.coe_representationAlphaValue b i.tailShift.previous,
      a.coe_representationAlphaValue b (i.tailShift.current hiOriginal)]
    rw [← hAPrevious, ← hBPrevious]
    exact hsum

end BONG.GoodBONG

end Bong
