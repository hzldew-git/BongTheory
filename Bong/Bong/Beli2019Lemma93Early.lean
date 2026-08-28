/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93High

/-!
# Beli (2019), Lemma 9.3: the early Lemma 9.2 branch

Under one of Lemma 9.2's three early alternatives, the transformed BONG also
aligns the alpha at paper index three with the first alpha of its projected
tail.  Consequently the uniform comparison-alpha transport starts one index
earlier: every tail boundary of value greater than three is automatic.
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
  {L : Lattice K V} {M : Lattice K W} {n N : Nat}

/-- The early equality supplied by Lemma 9.2 transports every positive
internal alpha cap beginning with the second tail cap. -/
theorem prefixAlphaCap_shift_eq_tail_of_earlyAlphaValue_eq
    (a : GoodBONG q L (n + 2))
    (halpha : ∀ k : Fin n, 1 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (i : Nat) (hi : 2 ≤ i) (hile : i ≤ n + 1) :
    a.prefixAlphaCap (i + 1) = a.tail.prefixAlphaCap i := by
  by_cases hin : i < n + 1
  · rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
      a.tail.prefixAlphaCap_of_internal (by omega) hin]
    let k : Fin n := ⟨i - 1, by omega⟩
    have hsucc : k.succ =
        (⟨i + 1 - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [k, Fin.val_succ]
      omega
    have hk := halpha k (by simp only [k]; omega)
    rw [hsucc] at hk
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hk
  · have hilast : i = n + 1 := by omega
    subst i
    simp

/-- In the early branch, the primary candidate is invariant from tail index
three onward. -/
theorem representationPrimaryDefect_tail_eq_shift_of_earlyAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 1 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 1 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 2 < i.val) :
    a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b i.tailShift := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_earlyAlphaValue_eq
    halphaA (i.val + 1) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_earlyAlphaValue_eq
    halphaB (i.val - 1) (by omega) (by omega)
  have hdefect := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    b hhead (-1) (i.val + 1) (i.val - 1) (by omega) (by omega)
      hcapA hcapB
  unfold representationPrimaryDefect
  rw [a.order_goodTail, b.order_goodTail]
  have htarget : i.val + 1 + 1 = i.tailShift.val + 1 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 1 + 1 = i.tailShift.val - 1 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, hsourceIndex, ← hdefect]

/-- In the early branch, the secondary candidate is invariant from tail
index four onward. -/
theorem representationSecondaryDefect_tail_eq_shift_of_earlyAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 1 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 1 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 3 < i.val) (hinterior : i.val + 1 < n + 1) :
    a.tail.representationSecondaryDefect b.tail i
        ⟨by omega, hinterior⟩ =
      a.representationSecondaryDefect b i.tailShift
        ⟨by
          change 1 < i.val + 1
          omega,
         by
          change i.val + 1 + 1 < n + 2
          omega⟩ := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_earlyAlphaValue_eq
    halphaA (i.val + 2) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_earlyAlphaValue_eq
    halphaB (i.val - 2) (by omega) (by omega)
  have hdefect := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    b hhead 1 (i.val + 2) (i.val - 2) (by omega) (by omega)
      hcapA hcapB
  unfold representationSecondaryDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  have htarget : i.val + 2 + 1 = i.tailShift.val + 2 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 2 + 1 = i.tailShift.val - 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have htargetNextIndex :
      (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex :
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex,
    hsourceIndex, ← hdefect]

set_option maxHeartbeats 800000 in
-- The dependent minimum formulas require additional kernel reduction.
/-- If both selected BONGs satisfy Lemma 9.2's early equality, comparison
alpha transport is automatic at every tail index greater than three. -/
theorem representationAlpha_tail_eq_shift_of_earlyAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 1 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 1 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 3 < i.val) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
    a.representationHalfGap_tail_eq_shift b i]
  by_cases hinterior : i.val + 1 < n + 1
  · have htailInterior : 1 < i.val ∧ i.val + 1 < n + 1 :=
      ⟨by omega, hinterior⟩
    have horiginalInterior :
        1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_min_primary_secondary
        b.tail i htailInterior,
      a.representationAlphaPrime_eq_min_primary_secondary
        b i.tailShift horiginalInterior,
      a.representationPrimaryDefect_tail_eq_shift_of_earlyAlphaValue_eq
        b hhead halphaA halphaB i (by omega)]
    congr 2
    exact a.representationSecondaryDefect_tail_eq_shift_of_earlyAlphaValue_eq
      b hhead halphaA halphaB i hi hinterior
  · have htailEndpoint :
        ¬(1 < i.val ∧ i.val + 1 < n + 1) := by omega
    have horiginalEndpoint :
        ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i htailEndpoint,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift horiginalEndpoint,
      a.representationPrimaryDefect_tail_eq_shift_of_earlyAlphaValue_eq
        b hhead halphaA halphaB i (by omega)]

/-- Lemma 9.2's conditional early field, rewritten as a self-tail equality
for the transformed BONG. -/
theorem Beli2019Lemma92Transform.transformed_earlyAlpha_eq_tail
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} (T : Beli2019Lemma92Transform a)
    (hcase : a.Lemma92EarlyAlternative) :
    T.transformed.alphaValue (2 : Fin (N + 3)) =
      T.transformed.tail.alphaValue (1 : Fin (N + 2)) :=
  (a.alpha_invariant T.transformed (2 : Fin (N + 3))).symm.trans
    (T.earlyAlpha_eq_tail hcase)

/-- The early and later fields of a Lemma 9.2 transform combine into alpha
transport at every tail-alpha index at least one. -/
theorem Beli2019Lemma92Transform.transformed_alpha_eq_tail_of_one_le
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} (T : Beli2019Lemma92Transform a)
    (hcase : a.Lemma92EarlyAlternative)
    (i : Fin (N + 2)) (hi : 1 ≤ i.1) :
    T.transformed.alphaValue i.succ =
      T.transformed.tail.alphaValue i := by
  by_cases hone : i.1 = 1
  · have hiFin : i = (1 : Fin (N + 2)) := Fin.ext hone
    subst i
    rw [show Fin.succ (1 : Fin (N + 2)) = (2 : Fin (N + 3)) by
      apply Fin.ext
      rfl]
    exact T.transformed_earlyAlpha_eq_tail hcase
  · exact T.transformed_laterAlpha_eq_tail i (by omega)

/-- When both selected inputs lie in Lemma 9.2's early branch, the fourth
low index of Lemma 9.3 is no longer exceptional. -/
theorem representationAlpha_tail_eq_shift_of_lemma92Transforms_early
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (Ta : Beli2019Lemma92Transform a)
    (Tb : Beli2019Lemma92Transform b)
    (hcaseA : a.Lemma92EarlyAlternative)
    (hcaseB : b.Lemma92EarlyAlternative)
    (hhead : Ta.transformed.value 0 = Tb.transformed.value 0)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 3 < i.val) :
    Ta.transformed.tail.representationAlpha Tb.transformed.tail i =
      Ta.transformed.representationAlpha Tb.transformed i.tailShift := by
  have halphaA : ∀ k : Fin (N + 2), 1 ≤ k.1 →
      Ta.transformed.alphaValue k.succ =
        Ta.transformed.tail.alphaValue k := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    intro k hk
    exact Ta.transformed_alpha_eq_tail_of_one_le hcaseA k hk
  have halphaB : ∀ k : Fin (N + 2), 1 ≤ k.1 →
      Tb.transformed.alphaValue k.succ =
        Tb.transformed.tail.alphaValue k := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    intro k hk
    exact Tb.transformed_alpha_eq_tail_of_one_le hcaseB k hk
  exact Ta.transformed.representationAlpha_tail_eq_shift_of_earlyAlphaValue_eq
    Tb.transformed hhead halphaA halphaB i hi

end BONG.GoodBONG

end Bong
