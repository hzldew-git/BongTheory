/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716PrefixTransport
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 7.16(ii): the unchanged tail

For zero-based indices `i ≥ s`, the order data entering `B_i` and `C_i`
agree.  The primary and secondary candidates also agree because they use
prefixes of lengths `i + 1` and `i + 2`, where Lemma 7.15 supplies prefix
isometries.  At the diagonal defect boundary itself one needs `i ≥ s + 1`.

This file proves the equalities candidate by candidate and then transports
condition 2.1(ii) on the entire unchanged tail.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Equality of all tail alphas gives equality of the associated prefix caps,
including the full-prefix endpoint convention. -/
theorem lemma716_tail_prefixAlphaCap_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (s k : Nat)
    (halphas : ∀ i, s ≤ i.val → a.alphaValue i = b.alphaValue i)
    (hsk : s + 1 ≤ k) (hk : k ≤ n + 3) :
    a.prefixAlphaCap k = b.prefixAlphaCap k := by
  by_cases hklt : k < n + 3
  · apply a.prefixAlphaCap_eq_of_internal_alpha_eq b k (by omega) hklt
    let boundary : Fin (n + 2) := ⟨k - 1, by omega⟩
    apply halphas boundary
    change s ≤ k - 1
    omega
  · have hkfull : k = n + 3 := by omega
    subst k
    simp

/-- Every capped mixed defect whose left prefix lies in the unchanged tail
is identical for the original and constructed BONGs. -/
theorem lemma716_tail_truncatedPrefixDefect_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (halphas : ∀ i, s ≤ i.val → a.alphaValue i = b.alphaValue i)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (epsilon : Kˣ) (k j : Nat) (hsk : s + 1 ≤ k)
    (hk : k ≤ n + 3) :
    a.truncatedPrefixDefect c epsilon k j =
      b.truncatedPrefixDefect c epsilon k j := by
  exact a.truncatedPrefixDefect_eq_of_prefix_isometric b c epsilon k j hk
    (a.lemma716_tail_prefixAlphaCap_eq b s k halphas hsk hk)
    (hprefix k hsk hk)

/-- The half-gap candidate is unchanged at every tail boundary. -/
theorem lemma716_tail_representationHalfGap_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (i : RepresentationIndex (n + 3) (n + 3)) (hsi : s ≤ i.val) :
    a.representationHalfGap c i = b.representationHalfGap c i := by
  unfold representationHalfGap
  rw [horders ⟨i.val, i.lt_large⟩ hsi]

/-- The primary candidate is unchanged at every tail boundary. -/
theorem lemma716_tail_representationPrimaryDefect_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3)) (hsi : s ≤ i.val) :
    a.representationPrimaryDefect c i =
      b.representationPrimaryDefect c i := by
  have hk : i.val + 1 ≤ n + 3 := i.lt_large
  unfold representationPrimaryDefect
  rw [horders ⟨i.val, i.lt_large⟩ hsi,
    a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas hprefix
      (-1) (i.val + 1) (i.val - 1) (by omega) hk]

/-- The optional secondary candidate is unchanged at every tail boundary. -/
theorem lemma716_tail_representationSecondaryDefect_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3))
    (hi : 1 < i.val ∧ i.val + 1 < n + 3) (hsi : s ≤ i.val) :
    a.representationSecondaryDefect c i hi =
      b.representationSecondaryDefect c i hi := by
  have hk : i.val + 2 ≤ n + 3 := hi.2
  let next : Fin (n + 3) := ⟨i.val + 1, hi.2⟩
  have hsnext : s ≤ next.val := by
    change s ≤ i.val + 1
    omega
  have hnext : a.order ⟨i.val + 1, hi.2⟩ =
      b.order ⟨i.val + 1, hi.2⟩ := by
    simpa only [next] using horders next hsnext
  unfold representationSecondaryDefect
  rw [horders ⟨i.val, i.lt_large⟩ hsi,
    hnext,
    a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas hprefix
      1 (i.val + 2) (i.val - 2) (by omega) hk]

/-- The complete candidate sets defining `C_i` and `B_i` agree on the
unchanged tail. -/
theorem lemma716_tail_representationAlphaCandidates_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3)) (hsi : s ≤ i.val) :
    a.representationAlphaCandidates c i =
      b.representationAlphaCandidates c i := by
  unfold representationAlphaCandidates
  rw [a.lemma716_tail_representationHalfGap_eq b c s horders i hsi,
    a.lemma716_tail_representationPrimaryDefect_eq b c s horders halphas
      hprefix i hsi]
  split_ifs with hi
  · rw [a.lemma716_tail_representationSecondaryDefect_eq b c s horders
      halphas hprefix i hi hsi]
  · rfl

/-- The representation invariant itself agrees on the unchanged tail. -/
theorem lemma716_tail_representationAlpha_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3)) (hsi : s ≤ i.val) :
    a.representationAlpha c i = b.representationAlpha c i := by
  have hcandidates := a.lemma716_tail_representationAlphaCandidates_eq
    b c s horders halphas hprefix i hsi
  unfold representationAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [hcandidates] using hz
  · apply Finset.le_min'
    intro z hz
    apply Finset.min'_le
    simpa only [← hcandidates] using hz

/-- Rational-valued form of the tail equality `C_i = B_i`. -/
theorem lemma716_tail_representationAlphaValue_eq
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3)) (hsi : s ≤ i.val) :
    a.representationAlphaValue c i =
      b.representationAlphaValue c i := by
  apply WithTop.coe_injective
  rw [coe_representationAlphaValue, coe_representationAlphaValue,
    a.lemma716_tail_representationAlpha_eq b c s horders halphas hprefix
      i hsi]

/-- Condition 2.1(ii) transports pointwise on the paper's range
`i ≥ s + 1`. -/
theorem lemma716_tail_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (hac : a.RepresentationDefectCondition c)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : RepresentationIndex (n + 3) (n + 3))
    (hsi : s + 1 ≤ i.val) :
    b.RepresentationDefectAt c i := by
  unfold RepresentationDefectAt
  rw [← b.coe_representationAlphaValue c i,
    ← a.lemma716_tail_representationAlphaValue_eq b c s horders halphas
      hprefix i (by omega),
    ← a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas hprefix
      1 i.val i.val hsi i.lt_large.le]
  exact hac i

end BONG.GoodBONG

end Bong
