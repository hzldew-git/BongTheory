/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74LeftEndpointComplete
import Bong.Bong.Beli2019Lemma76TypeICentralComplete

/-!
# Beli (2019), Lemma 7.6: endpoint-complete central source prefix

The complete left-endpoint form of Lemma 7.4(iii) removes the artificial
successor-coordinate hypothesis from the central type-I self-prefix estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.4(iii) computes the central target segment even when its right
endpoint is the final order coordinate. -/
theorem beli2019Lemma76_typeI_central_segment_eq_alpha_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((i.val - C.leftSwitch) / 2))
        C.leftSwitch i.val =
      (b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : WithTop ℚ) := by
  let left : Fin (n + 1) := ⟨C.leftSwitch, by
    have hiBound : i.val < n + 2 := i.lt_large
    omega⟩
  have horderRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le hiRight hiEven
  have horder : b.order left.castSucc = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order left.castSucc,
      ← b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩]
    simpa only [left, Fin.val_castSucc] using horderRaw
  have hdifferenceEven : Even (i.val - left.val) := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    exact ⟨d - e, by simp only [left]; omega⟩
  simpa only [left] using
    beli2019Lemma74_iii_leftEndpoint_complete
      b left i (by simp only [left]; exact hiLeft) hdifferenceEven horder

set_option maxHeartbeats 5000000 in
-- Boundary and segment estimates concatenate without a successor coordinate.
/-- The positive-switch central source self-prefix bound at every valid
coordinate, including the final internal boundary. -/
theorem beli2019Lemma76_typeI_central_sourceCapped_of_beta_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  let x : WithTop ℚ := b.representationAlphaValue c i
  let boundary : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  let current : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  have horderRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le hiRight hiEven
  have horder : b.order boundary.succ = b.order current.succ := by
    rw [← b.orderSequence_entryOrZero_eq_order boundary.succ,
      ← b.orderSequence_entryOrZero_eq_order current.succ]
    simpa only [boundary, current, Fin.val_succ,
      show C.leftSwitch - 1 + 1 = C.leftSwitch by omega,
      show i.val - 1 + 1 = i.val by omega] using horderRaw
  have hboundaryCurrent : boundary ≤ current := by
    change boundary.val ≤ current.val
    simp only [boundary, current]
    omega
  have halphaMono : b.alphaValue current ≤ b.alphaValue boundary :=
    b.alphaValue_le_of_rightEndpoint_orders_eq hboundaryCurrent horder
  have hxCurrent : x ≤ (b.alphaValue current : WithTop ℚ) := by
    dsimp only [x, current]
    exact_mod_cast hbeta
  have hxBoundaryAlpha : x ≤ (b.alphaValue boundary : WithTop ℚ) :=
    hxCurrent.trans (WithTop.coe_le_coe.mpr halphaMono)
  have htwoE : x ≤
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
    representationAlphaValue_le_twoE_of_crossGap_le b c i hcross
  have hprefix : x ≤ b.truncatedPrefixDefect b
      ((-1) ^ (C.leftSwitch / 2)) 0 C.leftSwitch := by
    apply beli2019Lemma76_typeI_boundary_lower
      a b D C hfirst hleftPos x
    · simpa only [boundary] using hxBoundaryAlpha
    · exact htwoE
  have hsegmentEq :=
    beli2019Lemma76_typeI_central_segment_eq_alpha_endpointComplete
      a b D C hfirst i hiEven hiLeft hiRight
  have hsegment : x ≤ b.truncatedPrefixDefect b
      ((-1) ^ ((i.val - C.leftSwitch) / 2))
        C.leftSwitch i.val := by
    rw [hsegmentEq]
    simpa only [current] using hxCurrent
  exact alternatingPrefixDefect_concat_lower b C.leftSwitch i.val
    hiLeft.le C.left_even hiEven x hprefix hsegment

set_option maxHeartbeats 5000000 in
-- The zero-switch plateau and positive-switch concatenation are both complete.
/-- The source self-prefix part of Lemma 7.9(ii), case 3, throughout the
central even type-I interval, including the final internal boundary. -/
theorem beli2019Lemma76_typeI_central_sourceCapped_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  by_cases hleftZero : C.leftSwitch = 0
  · have hplateau := lemma76_typeI_target_even_order_eq_left
      a b D C hfirst i.val hiLeft.le hiRight hiEven
    have hiTwo : 2 ≤ i.val := by
      rcases hiEven with ⟨d, hd⟩
      omega
    apply b.lemma79_even_sourceCapped_of_plateau_complete
      c i hiTwo hiEven
    · simpa only [hleftZero] using hplateau
    · exact hbeta
  · exact
      beli2019Lemma76_typeI_central_sourceCapped_of_beta_endpointComplete
        a b c D C hfirst (Nat.pos_of_ne_zero hleftZero) i hiEven
          hiLeft hiRight hcross hbeta

end BONG.GoodBONG

end Bong
