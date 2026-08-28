/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailDefect
import Bong.Bong.Beli2019Lemma93TailAlpha
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 9.3: exact comparison-alpha transport

Deleting equal first BONG values removes a common square from every raw
comparison prefix.  If the corresponding internal alpha caps also agree,
then all candidates defining the comparison alpha agree term by term.  This
is the uniform high-index calculation in the proof of Lemma 9.3; the first
few indices are exceptional only because one of those caps is an endpoint.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Unequal prefix lengths are allowed: adding the same equal head to both
prefixes still changes their product only by a square. -/
theorem defectOrder_shiftedPrefixes_eq_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0) (ε : Kˣ)
    (i j : Nat) (hi : i ≤ n + 1) (hj : j ≤ n + 1) :
    defectOrder (K := K)
        (ε * a.prefixProduct (i + 1) * b.prefixProduct (j + 1)) =
      defectOrder (K := K)
        (ε * a.tail.prefixProduct i * b.tail.prefixProduct j) := by
  have hheadUnit : a.valueUnit 0 = b.valueUnit 0 := by
    apply Units.ext
    simpa only [GoodBONG.coe_valueUnit] using hhead
  rw [a.prefixProduct_succ_eq_head_mul_tail i hi,
    b.prefixProduct_succ_eq_head_mul_tail j hj, ← hheadUnit]
  have hfactor :
      ε * (a.valueUnit 0 * a.tail.prefixProduct i) *
          (a.valueUnit 0 * b.tail.prefixProduct j) =
        (ε * a.tail.prefixProduct i * b.tail.prefixProduct j) *
          a.valueUnit 0 ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

/-- A positive tail prefix has the same alpha cap as the corresponding
one-longer original prefix when the shifted alpha equality holds.  At the
full prefix both sides are the omitted endpoint cap `⊤`. -/
theorem prefixAlphaCap_shift_eq_tail_of_alphaValue_eq
    (a : GoodBONG q L (n + 2))
    (halpha : ∀ k : Fin n,
      a.alphaValue k.succ = a.tail.alphaValue k)
    (i : Nat) (hi0 : 0 < i) (hile : i ≤ n + 1) :
    a.prefixAlphaCap (i + 1) = a.tail.prefixAlphaCap i := by
  by_cases hin : i < n + 1
  · rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
      a.tail.prefixAlphaCap_of_internal hi0 hin]
    let k : Fin n := ⟨i - 1, by omega⟩
    have hsucc : k.succ =
        (⟨i + 1 - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [k, Fin.val_succ]
      omega
    have hk := halpha k
    rw [hsucc] at hk
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hk
  · have hilast : i = n + 1 := by omega
    subst i
    simp

/-- Version of the cap identity using only the later alpha equalities supplied
by Lemma 9.2. -/
theorem prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    (a : GoodBONG q L (n + 2))
    (halpha : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (i : Nat) (hi : 3 ≤ i) (hile : i ≤ n + 1) :
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

/-- Raw-prefix equality plus explicit cap equalities gives exact truncated
defect transport. -/
theorem truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0) (ε : Kˣ)
    (i j : Nat) (hile : i ≤ n + 1) (hjle : j ≤ n + 1)
    (hcapA : a.prefixAlphaCap (i + 1) = a.tail.prefixAlphaCap i)
    (hcapB : b.prefixAlphaCap (j + 1) = b.tail.prefixAlphaCap j) :
    a.truncatedPrefixDefect b ε (i + 1) (j + 1) =
      a.tail.truncatedPrefixDefect b.tail ε i j := by
  unfold truncatedPrefixDefect
  rw [a.defectOrder_shiftedPrefixes_eq_tail b hhead ε i j hile hjle,
    hcapA, hcapB]

/-- Exact capped-defect transport for arbitrary positive prefix lengths. -/
theorem truncatedPrefixDefect_shift_eq_tail_of_alphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n,
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (ε : Kˣ) (i j : Nat)
    (hi0 : 0 < i) (hile : i ≤ n + 1)
    (hj0 : 0 < j) (hjle : j ≤ n + 1) :
    a.truncatedPrefixDefect b ε (i + 1) (j + 1) =
      a.tail.truncatedPrefixDefect b.tail ε i j := by
  exact a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq b hhead ε i j
    hile hjle
    (a.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq halphaA i hi0 hile)
    (b.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq halphaB j hj0 hjle)

/-- The half-gap candidate is unaffected by deleting equal heads. -/
theorem representationHalfGap_tail_eq_shift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    a.tail.representationHalfGap b.tail i =
      a.representationHalfGap b i.tailShift := by
  have hilarge := i.lt_large
  have hipos := i.pos
  unfold representationHalfGap
  simp only [RepresentationIndex.tailShift_val]
  rw [a.order_goodTail, b.order_goodTail]
  have htarget : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  have hsource : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.val + 1 - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change (i.val - 1) + 1 = i.val + 1 - 1
    omega
  rw [htarget, hsource]

/-- Under shifted alpha equalities, the primary comparison-defect candidate
is unchanged away from the first tail boundary. -/
theorem representationPrimaryDefect_tail_eq_shift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n,
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val) :
    a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b i.tailShift := by
  have hilarge := i.lt_large
  have hdefect :=
    a.truncatedPrefixDefect_shift_eq_tail_of_alphaValue_eq b hhead
      halphaA halphaB (-1) (i.val + 1) (i.val - 1)
      (by omega) (by omega) (by omega) (by omega)
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

/-- Under shifted alpha equalities, the secondary comparison-defect
candidate is unchanged once all four prefix caps are positive or terminal. -/
theorem representationSecondaryDefect_tail_eq_shift
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n,
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 2 < i.val) (hinterior : i.val + 1 < n + 1) :
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
  have hdefect :=
    a.truncatedPrefixDefect_shift_eq_tail_of_alphaValue_eq b hhead
      halphaA halphaB 1 (i.val + 2) (i.val - 2)
      (by omega) (by omega) (by omega) (by omega)
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
  have htargetNextIndex : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex,
    hsourceIndex, ← hdefect]

set_option maxHeartbeats 800000 in
/-- Exact transport of the comparison alpha once the boundary is beyond the
three endpoint-sensitive initial positions. -/
theorem representationAlpha_tail_eq_shift_of_alphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n,
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 2 < i.val) :
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
      a.representationPrimaryDefect_tail_eq_shift b hhead
        halphaA halphaB i (by omega)]
    congr 2
    exact a.representationSecondaryDefect_tail_eq_shift b hhead
      halphaA halphaB i hi hinterior
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
      a.representationPrimaryDefect_tail_eq_shift b hhead
        halphaA halphaB i (by omega)]

/-- Primary-candidate transport using only Lemma 9.2's later alpha
equalities. -/
theorem representationPrimaryDefect_tail_eq_shift_of_laterAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 2 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 4 < i.val) :
    a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b i.tailShift := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 1) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
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

/-- Secondary-candidate transport using only Lemma 9.2's later alpha
equalities. -/
theorem representationSecondaryDefect_tail_eq_shift_of_laterAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 2 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 4 < i.val) (hinterior : i.val + 1 < n + 1) :
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
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 2) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
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
  have htargetNextIndex : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex,
    hsourceIndex, ← hdefect]

set_option maxHeartbeats 800000 in
/-- Lemma 9.2 automatically supplies the exact comparison-alpha equality at
every tail boundary with paper index at least six. -/
theorem representationAlpha_tail_eq_shift_of_laterAlphaValue_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n, 2 ≤ k.1 →
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 4 < i.val) :
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
      a.representationPrimaryDefect_tail_eq_shift_of_laterAlphaValue_eq
        b hhead halphaA halphaB i hi]
    congr 2
    exact a.representationSecondaryDefect_tail_eq_shift_of_laterAlphaValue_eq
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
      a.representationPrimaryDefect_tail_eq_shift_of_laterAlphaValue_eq
        b hhead halphaA halphaB i hi]

end BONG.GoodBONG

end Bong
