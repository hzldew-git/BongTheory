/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentral

/-!
# Beli (2019), Lemma 7.6: strict type-I prefix bounds

The weak central-prefix estimate used earlier is sharpened here.  A finite
threshold strictly below both the relevant target alpha and `2e` is
strictly below the alternating target prefix defect.  This is the form
needed in the gap-two part of Lemma 7.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Strict lower bounds on two adjacent even alternating blocks concatenate
to a strict lower bound on the complete block. -/
theorem alternatingPrefixDefect_concat_gt
    (b : GoodBONG q M (n + 2)) (left right : Nat)
    (hleftRight : left ≤ right)
    (hleftEven : Even left) (hrightEven : Even right)
    (x : WithTop Rat)
    (hprefix : x <
      b.truncatedPrefixDefect b ((-1) ^ (left / 2)) 0 left)
    (hsegment : x <
      b.truncatedPrefixDefect b ((-1) ^ ((right - left) / 2))
        left right) :
    x < b.truncatedPrefixDefect b ((-1) ^ (right / 2)) 0 right := by
  have hdomination := b.truncatedPrefixDefect_domination b b
    ((-1) ^ (left / 2)) ((-1) ^ ((right - left) / 2))
      0 left right
  have hhalves : left / 2 + (right - left) / 2 = right / 2 := by
    rcases hleftEven with ⟨d, hd⟩
    rcases hrightEven with ⟨e, he⟩
    omega
  calc
    x < min
        (b.truncatedPrefixDefect b ((-1) ^ (left / 2)) 0 left)
        (b.truncatedPrefixDefect b ((-1) ^ ((right - left) / 2))
          left right) := lt_min hprefix hsegment
    _ ≤ b.truncatedPrefixDefect b
        (((-1) ^ (left / 2)) * ((-1) ^ ((right - left) / 2)))
          0 right := hdomination
    _ = b.truncatedPrefixDefect b ((-1) ^ (right / 2)) 0 right := by
      rw [← pow_add, hhalves]

/-- Strict counterpart of the first-switch lower bound in Lemma 7.6. -/
theorem beli2019Lemma76_typeI_boundary_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (x : Rat)
    (hbeta : x < b.alphaValue ⟨C.leftSwitch - 1, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩)
    (htwoE : x < 2 * (ramificationIndex K : Rat)) :
    (x : WithTop Rat) < b.truncatedPrefixDefect b
      ((-1) ^ (C.leftSwitch / 2)) 0 C.leftSwitch := by
  have hcases := beli2019Lemma76_typeI a b D C hfirst hleftPos
  dsimp only at hcases
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  let caseCurrent : Fin (n + 1) := ⟨C.leftSwitch - 2 + 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  let current : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hcurrentEq : caseCurrent = current := by
    apply Fin.ext
    simp only [caseCurrent, current]
    omega
  have hupper := lemma79_typeI_leftSwitch_gap_le_twoE_add_one
    a b D C hleftPos
  have hupper' : b.orderGap caseCurrent ≤
      2 * (ramificationIndex K : Int) + 1 := by
    rw [hcurrentEq]
    simpa only [current] using hupper
  by_cases hgap : b.orderGap caseCurrent ≤
      2 * (ramificationIndex K : Int)
  · rw [hcases.1 hgap]
    apply WithTop.coe_lt_coe.mpr
    simpa only [show C.leftSwitch - 2 + 1 = C.leftSwitch - 1 by omega]
      using hbeta
  · have hgapEq : b.orderGap caseCurrent =
        2 * (ramificationIndex K : Int) + 1 := by
      omega
    exact (WithTop.coe_lt_coe.mpr htwoE).trans_le (hcases.2 hgapEq)

set_option maxHeartbeats 2000000 in
-- The proof combines dependent first-switch and current alpha indices.
/-- Strict Lemma 7.6 bound at every positive even coordinate in the
canonical type-I interval. -/
theorem beli2019Lemma76_typeI_central_prefix_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i < n + 1)
    (hiEven : Even i) (hiLeft : C.leftSwitch ≤ i)
    (hiRight : i ≤ C.rightSwitch)
    (x : Rat)
    (hcurrent : x < b.alphaValue ⟨i - 1, by omega⟩)
    (htwoE : x < 2 * (ramificationIndex K : Rat)) :
    (x : WithTop Rat) <
      b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by omega, by omega, by omega⟩
  by_cases hleftZero : C.leftSwitch = 0
  · have hsegment := beli2019Lemma76_typeI_central_segment_eq_alpha
      a b D C hfirst idx (by simp only [idx]; omega)
        (by simpa only [idx] using hiEven) (by
          simp only [idx]
          omega) (by simpa only [idx] using hiRight)
    have hsegment' : b.truncatedPrefixDefect b
        ((-1) ^ (i / 2)) 0 i =
          (b.alphaValue ⟨i - 1, by omega⟩ : WithTop Rat) := by
      simpa only [idx, hleftZero, Nat.sub_zero] using hsegment
    rw [hsegment']
    exact_mod_cast hcurrent
  · have hleftPos : 0 < C.leftSwitch := Nat.pos_of_ne_zero hleftZero
    let boundary : Fin (n + 1) := ⟨C.leftSwitch - 1, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩
    let current : Fin (n + 1) := ⟨i - 1, by omega⟩
    have horderRaw := lemma76_typeI_target_even_order_eq_left
      a b D C hfirst i hiLeft hiRight hiEven
    have horder : b.order boundary.succ = b.order current.succ := by
      rw [← b.orderSequence_entryOrZero_eq_order boundary.succ,
        ← b.orderSequence_entryOrZero_eq_order current.succ]
      simpa only [boundary, current, Fin.val_succ,
        show C.leftSwitch - 1 + 1 = C.leftSwitch by omega,
        show i - 1 + 1 = i by omega] using horderRaw
    have hboundaryCurrent : boundary ≤ current := by
      change boundary.val ≤ current.val
      simp only [boundary, current]
      omega
    have halphaMono : b.alphaValue current ≤ b.alphaValue boundary :=
      b.alphaValue_le_of_rightEndpoint_orders_eq hboundaryCurrent horder
    have hcurrent' : x < b.alphaValue current := by
      simpa only [current] using hcurrent
    have hboundaryAlpha : x < b.alphaValue boundary :=
      hcurrent'.trans_le halphaMono
    have hprefix := beli2019Lemma76_typeI_boundary_gt
      a b D C hfirst hleftPos x (by
        simpa only [boundary] using hboundaryAlpha) htwoE
    by_cases heq : C.leftSwitch = i
    · simpa only [heq] using hprefix
    · have hleftStrict : C.leftSwitch < i :=
        lt_of_le_of_ne hiLeft heq
      have hsegmentEq := beli2019Lemma76_typeI_central_segment_eq_alpha
        a b D C hfirst idx (by simp only [idx]; omega)
          (by simpa only [idx] using hiEven) (by
            simpa only [idx] using hleftStrict) (by
              simpa only [idx] using hiRight)
      have hsegment : (x : WithTop Rat) <
          b.truncatedPrefixDefect b
            ((-1) ^ ((i - C.leftSwitch) / 2)) C.leftSwitch i := by
        rw [show b.truncatedPrefixDefect b
            ((-1) ^ ((i - C.leftSwitch) / 2)) C.leftSwitch i =
              b.truncatedPrefixDefect b
                ((-1) ^ ((idx.val - C.leftSwitch) / 2))
                  C.leftSwitch idx.val by rfl,
          hsegmentEq]
        exact_mod_cast (by simpa only [current, idx] using hcurrent')
      exact alternatingPrefixDefect_concat_gt b C.leftSwitch i
        hiLeft C.left_even hiEven (x : WithTop Rat) hprefix hsegment

end BONG.GoodBONG

end Bong
