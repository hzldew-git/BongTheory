/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Beli2019Lemma76TypeIBoundaryLower
import Bong.Bong.Beli2019Lemma79EvenBetaReduction

/-!
# Beli (2019), Lemma 7.6: the central type-I interval

Even target orders form a constant plateau from the first canonical switch
to the second one.  Lemma 7.4(iii) computes each even segment exactly, and
the boundary dichotomy propagates through the domination principle.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Every even target order in the canonical type-I interval equals the
target order at the first switch. -/
theorem lemma76_typeI_target_even_order_eq_left
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k ≤ C.rightSwitch) (hkEven : Even k) :
    b.orderSequence.entryOrZero C.leftSwitch =
      b.orderSequence.entryOrZero k := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hbLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  by_cases hkAnchor : k ≤ D.anchor
  · have hbK := C.target_from_left k hleft hkAnchor hkEven
    exact hbLeft.trans hbK.symm
  · have hanchorK : D.anchor ≤ k :=
      (Nat.lt_of_not_ge hkAnchor).le
    have hdistance : Even (k - D.anchor) := by
      rcases hkEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hbAnchor := C.target_from_left D.anchor C.left_le_anchor
      le_rfl hanchorEven
    have hbK := C.target_from_anchor k hanchorK
      (hright.trans C.right_le_last) hdistance
    exact (hbLeft.trans hbAnchor.symm).trans hbK.symm

/-- Lemma 7.4(iii) computes the alternating target segment from the first
switch to a later even central coordinate. -/
theorem beli2019Lemma76_typeI_central_segment_eq_alpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((i.val - C.leftSwitch) / 2))
        C.leftSwitch i.val =
      (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  let left : Fin (n + 1) := ⟨C.leftSwitch, by
    have hiBound : i.val < n + 1 := by omega
    omega⟩
  let current : Fin (n + 1) := ⟨i.val, by omega⟩
  have horderRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le hiRight hiEven
  have horder : b.order left.castSucc = b.order current.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order left.castSucc,
      ← b.orderSequence_entryOrZero_eq_order current.castSucc]
    simpa only [left, current, Fin.val_castSucc] using horderRaw
  have hdifferenceEven : Even (current.val - left.val) := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    exact ⟨d - e, by simp only [left, current]; omega⟩
  have h74 := b.beli2019Lemma74_iii left current
    (by change left.val < current.val; simp only [left, current]; exact hiLeft)
    hdifferenceEven horder
  dsimp only at h74
  have hresult := h74.1.1.trans
    (congrArg (fun z : ℚ => (z : WithTop ℚ)) h74.1.2)
  simpa only [left, current] using hresult

set_option maxHeartbeats 4000000 in
-- The proof combines the dependent boundary and segment indices.
/-- The source self-prefix bound in the positive-switch central interval. -/
theorem beli2019Lemma76_typeI_central_sourceCapped_of_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int))
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  let x : WithTop ℚ := b.representationAlphaValue c i
  let boundary : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  let current : Fin (n + 1) := ⟨i.val - 1, by omega⟩
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
  have hsegmentEq := beli2019Lemma76_typeI_central_segment_eq_alpha
    a b D C hfirst i hiNext hiEven hiLeft hiRight
  have hsegment : x ≤ b.truncatedPrefixDefect b
      ((-1) ^ ((i.val - C.leftSwitch) / 2))
        C.leftSwitch i.val := by
    rw [hsegmentEq]
    simpa only [current] using hxCurrent
  exact alternatingPrefixDefect_concat_lower b C.leftSwitch i.val
    hiLeft.le C.left_even hiEven x hprefix hsegment

end BONG.GoodBONG

end Bong
