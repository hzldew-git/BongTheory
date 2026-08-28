/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019), Lemma 7.4(iii): complete right endpoint

The first equality in Lemma 7.4(iii) only needs its left endpoint to index an
alpha value.  Its right endpoint indexes an order and may therefore be the
last order of the BONG.  This formulation records that distinction and covers
the final internal representation boundary omitted by the symmetric
`Fin (n + 1)` formulation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- Only the left half of Lemma 7.4(iii) is needed at the final endpoint.
/-- The left-prefix equality in Lemma 7.4(iii), allowing the right endpoint
to be the final order coordinate. -/
theorem beli2019Lemma74_iii_leftEndpoint_complete
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (start : Fin (n + 1))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hstart : start.val < i.val)
    (heven : Even (i.val - start.val))
    (horder : b.order start.castSucc = b.order ⟨i.val, i.lt_large⟩) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((i.val - start.val) / 2)) start.val i.val =
      (b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : WithTop ℚ) := by
  rcases heven with ⟨d, hd⟩
  have hiFormula : i.val = start.val + 2 * d := by omega
  have hdPos : 0 < d := by omega
  let previous : Fin (n + 1) := ⟨i.val - 2, by
    have hiBound := i.lt_large
    omega⟩
  let middle : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  let endpoint : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let critical : ℚ :=
    ((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
      b.alphaValue previous
  have hpreviousOrder : b.order previous.castSucc = b.order endpoint := by
    apply b.order_eq_of_evenGap_between_equal
      start.castSucc previous.castSucc endpoint
    · change start.val ≤ previous.val
      simp only [previous]
      omega
    · change previous.val ≤ endpoint.val
      simp only [previous, endpoint]
      omega
    · change Even (previous.val - start.val)
      refine ⟨d - 1, ?_⟩
      simp only [previous]
      omega
    · change Even (endpoint.val - previous.val)
      refine ⟨1, ?_⟩
      simp only [previous, endpoint]
      omega
    · simpa only [endpoint] using horder
  have hleftOrder : b.order start.castSucc = b.order previous.castSucc :=
    horder.trans (by simpa only [endpoint] using hpreviousOrder.symm)
  have hlowerRaw := b.beli2019Lemma74_i start previous
    (by change start.val ≤ previous.val; simp only [previous]; omega)
    (by
      refine ⟨d - 1, ?_⟩
      simp only [previous]
      omega)
    hleftOrder
  have hexponent :
      (previous.val - start.val + 2) / 2 =
        (i.val - start.val) / 2 := by
    simp only [previous]
    omega
  have hend : previous.val + 2 = i.val := by
    simp only [previous]
    omega
  rw [hexponent, hend] at hlowerRaw
  have hlower : (critical : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((i.val - start.val) / 2)) start.val i.val := by
    change (critical : WithTop ℚ) ≤ _ at hlowerRaw
    exact hlowerRaw
  have hupperRaw := b.truncatedPrefixDefect_le_rightCap b
    ((-1) ^ ((i.val - start.val) / 2)) start.val i.val
  rw [b.prefixAlphaCap_of_internal i.pos i.lt_large] at hupperRaw
  have hupper : b.truncatedPrefixDefect b
        ((-1) ^ ((i.val - start.val) / 2)) start.val i.val ≤
      (b.alphaValue middle : WithTop ℚ) := by
    simpa only [middle] using hupperRaw
  have hpreviousSucc : previous.succ = middle.castSucc := by
    apply Fin.ext
    simp only [previous, middle, Fin.val_succ, Fin.val_castSucc]
    omega
  have hmiddleSucc : middle.succ = endpoint := by
    apply Fin.ext
    simp only [middle, endpoint, Fin.val_succ]
    omega
  have hsum : b.adjacentOrderSum previous =
      b.adjacentOrderSum middle := by
    unfold adjacentOrderSum
    rw [hpreviousSucc, hmiddleSucc, hpreviousOrder]
    omega
  have hendpoint :=
    (b.beli2009Corollary23 previous middle
      (by change previous.val ≤ middle.val;
          simp only [previous, middle]; omega) hsum).leftEndpoint_eq
      middle
      (by change previous.val ≤ middle.val;
          simp only [previous, middle]; omega)
      le_rfl
  have hbridge : b.order previous.succ =
      b.order middle.castSucc := congrArg b.order hpreviousSucc
  have hbridgeQ : (b.order previous.succ : ℚ) =
      (b.order middle.castSucc : ℚ) := by
    exact_mod_cast hbridge
  have hcritical : critical = b.alphaValue middle := by
    unfold alphaLeftEndpoint at hendpoint
    dsimp only [critical]
    push_cast at hendpoint ⊢
    linarith
  apply le_antisymm
  · simpa only [middle] using hupper
  · simpa only [middle, hcritical] using hlower

/-- On an even order plateau, the alternating self-prefix is the alpha at its
right boundary, including the final internal boundary. -/
theorem even_selfCapped_eq_alpha_of_plateau_complete
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val) :
    b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val =
      (b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : WithTop ℚ) := by
  let start : Fin (n + 1) := ⟨0, by omega⟩
  have horder : b.order start.castSucc = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order start.castSucc,
      ← b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩]
    change b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val
    exact hplateau
  simpa only [start, Nat.sub_zero] using
    beli2019Lemma74_iii_leftEndpoint_complete
      b start i (by simp only [start]; omega)
        (by simpa only [start, Nat.sub_zero] using hiEven) horder

/-- The scalar beta bound implies the complete even plateau self-prefix
estimate. -/
theorem lemma79_even_sourceCapped_of_plateau_complete
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) {N : Lattice K V}
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val)
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  rw [b.even_selfCapped_eq_alpha_of_plateau_complete i hiTwo hiEven hplateau]
  exact_mod_cast hbeta

end BONG.GoodBONG

end Bong
