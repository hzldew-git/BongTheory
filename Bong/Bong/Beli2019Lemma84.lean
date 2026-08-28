/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 8.4

This file proves the endpoint-plateau and half-gap propagation statements
used in the first-element transformations of Section 8.  They are direct
consequences of the monotonicity of `R_i + α_i` and `-R_{i+1} + α_i`, the
half-gap bound, and Beli (2009), Corollary 2.3.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

namespace BONG.GoodBONG

/-- Lemma 8.4(i), left-endpoint form: equality at the ends of an interval
forces `R_k + α_k` to be constant throughout the interval. -/
theorem beli2019Lemma84_i_left
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (_hij : i ≤ j)
    (heq : b.alphaLeftEndpoint i = b.alphaLeftEndpoint j)
    (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.alphaLeftEndpoint k = b.alphaLeftEndpoint i := by
  apply le_antisymm
  · rw [heq]
    exact b.alphaLeftEndpoint_monotone hkj
  · exact b.alphaLeftEndpoint_monotone hik

/-- Lemma 8.4(i), right-endpoint form: equality at the ends of an interval
forces `-R_{k+1} + α_k` to be constant throughout the interval. -/
theorem beli2019Lemma84_i_right
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (_hij : i ≤ j)
    (heq : b.alphaRightEndpoint i = b.alphaRightEndpoint j)
    (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.alphaRightEndpoint k = b.alphaRightEndpoint i := by
  apply le_antisymm
  · exact b.alphaRightEndpoint_antitone hik
  · rw [heq]
    exact b.alphaRightEndpoint_antitone hkj

/-- Lemma 8.4(ii): if a left-endpoint plateau contains an index attaining
the half-gap bound, then the adjacent order sum agrees with the left endpoint
of the interval and every intervening index attains its half-gap bound. -/
theorem beli2019Lemma84_ii
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1))
    (hij : i ≤ j) (hik : i ≤ k) (hkj : k ≤ j)
    (heq : b.alphaLeftEndpoint i = b.alphaLeftEndpoint j)
    (hkHalf : b.AttainsHalfGap k) :
    b.adjacentOrderSum i = b.adjacentOrderSum k ∧
      ∀ l : Fin (n + 1), i ≤ l → l ≤ k → b.AttainsHalfGap l := by
  have hleftKI := b.beli2019Lemma84_i_left i j hij heq k hik hkj
  have halphaI := b.alphaValue_le_halfGapValue i
  have hsumKIQ :
      (b.adjacentOrderSum k : ℚ) ≤ (b.adjacentOrderSum i : ℚ) := by
    unfold AttainsHalfGap at hkHalf
    unfold alphaLeftEndpoint at hleftKI
    unfold halfGapValue orderGap at halphaI hkHalf
    unfold adjacentOrderSum
    push_cast at hleftKI halphaI hkHalf ⊢
    linarith
  have hsumKI : b.adjacentOrderSum k ≤ b.adjacentOrderSum i := by
    exact_mod_cast hsumKIQ
  have hsumIK : b.adjacentOrderSum i = b.adjacentOrderSum k :=
    le_antisymm (b.adjacentOrderSum_monotone hik) hsumKI
  let C := b.beli2009Corollary23 i k hik hsumIK
  have hiHalf : b.AttainsHalfGap i :=
    (C.attainsHalfGap_iff k hik le_rfl).1 hkHalf
  refine ⟨hsumIK, ?_⟩
  intro l hil hlk
  exact (C.attainsHalfGap_iff l hil hlk).2 hiHalf

/-- Lemma 8.4(iii): the right-endpoint analogue of part (ii). -/
theorem beli2019Lemma84_iii
    (b : GoodBONG q L (n + 2)) (i j k : Fin (n + 1))
    (hij : i ≤ j) (hik : i ≤ k) (hkj : k ≤ j)
    (heq : b.alphaRightEndpoint i = b.alphaRightEndpoint j)
    (hkHalf : b.AttainsHalfGap k) :
    b.adjacentOrderSum k = b.adjacentOrderSum j ∧
      ∀ l : Fin (n + 1), k ≤ l → l ≤ j → b.AttainsHalfGap l := by
  have hrightKI := b.beli2019Lemma84_i_right i j hij heq k hik hkj
  have hrightKJ :
      b.alphaRightEndpoint k = b.alphaRightEndpoint j :=
    hrightKI.trans heq
  have halphaJ := b.alphaValue_le_halfGapValue j
  have hsumJKQ :
      (b.adjacentOrderSum j : ℚ) ≤ (b.adjacentOrderSum k : ℚ) := by
    unfold AttainsHalfGap at hkHalf
    unfold alphaRightEndpoint at hrightKJ
    unfold halfGapValue orderGap at halphaJ hkHalf
    unfold adjacentOrderSum
    push_cast at hrightKJ halphaJ hkHalf ⊢
    linarith
  have hsumJK : b.adjacentOrderSum j ≤ b.adjacentOrderSum k := by
    exact_mod_cast hsumJKQ
  have hsumKJ : b.adjacentOrderSum k = b.adjacentOrderSum j :=
    le_antisymm (b.adjacentOrderSum_monotone hkj) hsumJK
  let C := b.beli2009Corollary23 k j hkj hsumKJ
  refine ⟨hsumKJ, ?_⟩
  intro l hkl hlj
  exact (C.attainsHalfGap_iff l hkl hlj).2 hkHalf

end BONG.GoodBONG

end Bong
