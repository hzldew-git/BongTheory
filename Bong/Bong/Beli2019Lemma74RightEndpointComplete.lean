/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma74Boundary

/-!
# Beli (2019), Lemma 7.4(iii): complete right endpoint

The second equality in Lemma 7.4(iii) needs an alpha index only at its left
endpoint.  Its right endpoint is merely an order coordinate and may therefore
be the final coordinate of the BONG.  This endpoint-complete form is needed
when Lemma 9.12 propagates a defect bound from a full prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- Only the right half of Lemma 7.4(iii) is needed at the final endpoint.
theorem beli2019Lemma74_iii_rightEndpoint_complete
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (start : Fin (n + 1))
    (endpoint : RepresentationIndex (n + 2) (n + 2))
    (hstart : start.val < endpoint.val)
    (heven : Even (endpoint.val - start.val))
    (horder : b.order start.castSucc =
      b.order ⟨endpoint.val, endpoint.lt_large⟩) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((endpoint.val - start.val) / 2))
        (start.val + 1) (endpoint.val + 1) =
      (b.alphaValue start : WithTop ℚ) := by
  rcases heven with ⟨d, hd⟩
  have hdPos : 0 < d := by omega
  have hgap : start.val + 2 ≤ endpoint.val := by omega
  let next : Fin (n + 1) := ⟨start.val + 1, by
    have := endpoint.lt_large
    omega⟩
  let afterTwo : Fin (n + 2) := ⟨start.val + 2, by
    have := endpoint.lt_large
    omega⟩
  let endpointValue : Fin (n + 2) :=
    ⟨endpoint.val, endpoint.lt_large⟩
  let critical : ℚ :=
    ((b.order next.castSucc - b.order next.succ : Int) : ℚ) +
      b.alphaValue next
  have hafterTwoOrder : b.order afterTwo = b.order endpointValue := by
    apply b.order_eq_of_evenGap_between_equal
      start.castSucc afterTwo endpointValue
    · change start.val ≤ afterTwo.val
      simp only [afterTwo]
      omega
    · change afterTwo.val ≤ endpointValue.val
      simp only [afterTwo, endpointValue]
      omega
    · change Even (afterTwo.val - start.val)
      refine ⟨1, ?_⟩
      simp only [afterTwo]
      omega
    · refine ⟨d - 1, ?_⟩
      simp only [afterTwo, endpointValue]
      omega
    · simpa only [endpointValue] using horder
  have hlowerRaw := b.beli2019Lemma74_ii_nat
    (start.val + 2) endpoint.val
    (by omega) (by omega) (by have := endpoint.lt_large; omega)
      endpoint.lt_large
    (by
      refine ⟨d - 1, ?_⟩
      omega)
    (by simpa only [afterTwo, endpointValue] using hafterTwoOrder)
  dsimp only at hlowerRaw
  have hexponent :
      (endpoint.val - (start.val + 2) + 2) / 2 =
        (endpoint.val - start.val) / 2 := by
    omega
  have hstartPrefix : start.val + 2 - 1 = start.val + 1 := by omega
  have hlower : (critical : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((endpoint.val - start.val) / 2))
        (start.val + 1) (endpoint.val + 1) := by
    simpa only [critical, next, hexponent, hstartPrefix,
      WithTop.coe_add] using hlowerRaw
  have hupperRaw := b.truncatedPrefixDefect_le_leftCap b
    ((-1) ^ ((endpoint.val - start.val) / 2))
    (start.val + 1) (endpoint.val + 1)
  rw [b.prefixAlphaCap_of_internal (i := start.val + 1)
    (by omega) (by omega)] at hupperRaw
  have hcapIndex : (⟨start.val + 1 - 1, by omega⟩ : Fin (n + 1)) =
      start := by
    apply Fin.ext
    change start.val + 1 - 1 = start.val
    omega
  rw [hcapIndex] at hupperRaw
  have hcurrentSucc : start.succ = next.castSucc := by
    apply Fin.ext
    simp only [next, Fin.val_succ, Fin.val_castSucc]
  have hnextSucc : next.succ = afterTwo := by
    apply Fin.ext
    simp only [next, afterTwo, Fin.val_succ]
  have hbaseAfter : b.order start.castSucc = b.order afterTwo :=
    horder.trans (by simpa only [endpointValue] using hafterTwoOrder.symm)
  have hsum : b.adjacentOrderSum start = b.adjacentOrderSum next := by
    unfold adjacentOrderSum
    rw [hcurrentSucc, hnextSucc, hbaseAfter]
    omega
  have hendpoint :=
    (b.beli2009Corollary23 start next
      (by change start.val ≤ next.val; simp only [next]; omega) hsum).rightEndpoint_eq
      next (by change start.val ≤ next.val; simp only [next]; omega) le_rfl
  have hbridge : b.order start.succ = b.order next.castSucc :=
    congrArg b.order hcurrentSucc
  have hbridgeQ : (b.order start.succ : ℚ) =
      (b.order next.castSucc : ℚ) := by
    exact_mod_cast hbridge
  have hcritical : critical = b.alphaValue start := by
    unfold alphaRightEndpoint at hendpoint
    dsimp only [critical]
    push_cast at hendpoint ⊢
    linarith
  apply le_antisymm
  · exact hupperRaw
  · rw [← hcritical]
    exact hlower

end BONG.GoodBONG

end Bong
