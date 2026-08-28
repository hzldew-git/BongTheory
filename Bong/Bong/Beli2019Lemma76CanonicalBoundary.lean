/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76Boundary
import Bong.Bong.Beli2019Lemma611TypeII

/-!
# Beli (2019), Lemma 7.6 at the canonical type-I switch

The canonical switch raises the target order on one parity class by one.
The pair-sum identities of Lemma 6.7 and the parity theorem of Lemma 6.6
show that the intervening adjacent gap is odd.  This supplies the remaining
order hypotheses of the boundary dichotomy.
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

/-- The two target orders of the same parity on opposite sides of the first
type-I switch differ by exactly one. -/
theorem lemma76_leftSwitch_skip
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch) :
    b.order ⟨C.leftSwitch, by
        exact C.left_le_anchor.trans_lt D.anchor_bound⟩ =
      b.order ⟨C.leftSwitch - 2, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ + 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hbefore := C.target_before_left (C.leftSwitch - 2)
    (by omega) (by
      rcases C.left_even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩)
  have hafter := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by
      exact (show C.leftSwitch - 2 < n + 2 by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega))] at hbefore
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (C.left_le_anchor.trans_lt D.anchor_bound)] at hafter
  have hbefore' :
      b.order ⟨C.leftSwitch - 2, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ = a.orderSequence.entryOrZero D.anchor + 1 := by
    simpa only [b.orderSequence_at] using hbefore
  have hafter' :
      b.order ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ =
        a.orderSequence.entryOrZero D.anchor + 2 := by
    simpa only [b.orderSequence_at] using hafter
  omega

/-- The adjacent target gap crossing the first type-I switch is odd. -/
theorem lemma76_leftSwitch_gap_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch) :
    Odd (b.orderGap ⟨C.leftSwitch - 1, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩) := by
  let left := C.leftSwitch
  let p := left - 2
  let R := a.orderSequence.entryOrZero D.anchor
  have hleftTwo : 2 ≤ left := by
    rcases C.left_even with ⟨d, hd⟩
    simp only [left] at hleftPos hd ⊢
    omega
  have hleftBound : left < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpBound : p < n + 2 := by omega
  have hpNextBound : p + 1 < n + 2 := by omega
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hsourceZero : a.orderSequence.entryOrZero 0 = R := by
    exact C.source_to_anchor 0 (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceLeft : a.orderSequence.entryOrZero left = R := by
    exact C.source_to_anchor left C.left_le_anchor C.left_even
  have hsourceEndpoint : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left :=
    hsourceZero.trans hsourceLeft.symm
  have hsourceP := a.entryOrZero_modEq_of_equal_even_endpoints
    (i := 0) (j := left) (k := p) (by omega) hleftBound
    (Nat.zero_le p) (by omega) hpBound (by
      simpa only [Nat.sub_zero] using C.left_even) hsourceEndpoint
  have hsourceNext := a.entryOrZero_modEq_of_equal_even_endpoints
    (i := 0) (j := left) (k := p + 1) (by omega) hleftBound
    (Nat.zero_le (p + 1)) (by omega) hpNextBound (by
      simpa only [Nat.sub_zero] using C.left_even) hsourceEndpoint
  rw [hsourceZero] at hsourceP hsourceNext
  have hpairParity : Even (D.anchor - p) := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    refine ⟨d - e + 1, ?_⟩
    have hleftAnchor := C.left_le_anchor
    simp only [left, p] at he hleftAnchor ⊢
    omega
  have hleftAnchor := C.left_le_anchor
  have hpair := D.profile.leftPairEq p (by
      simp only [p, left]
      omega) hpairParity
  have hsourceSum := hsourceP.add hsourceNext
  rw [hpair] at hsourceSum
  have hpEven : Even p := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by
      simp only [p, left]
      omega⟩
  have htargetP : b.orderSequence.entryOrZero p = R + 1 := by
    exact C.target_before_left p (by
      simp only [p, left]
      omega) hpEven
  have htargetNextMod : Int.ModEq 2
      (b.orderSequence.entryOrZero (p + 1)) (R + 1) := by
    have hcross := hsourceSum.sub
      (show Int.ModEq 2 (b.orderSequence.entryOrZero p) (R + 1) by
        rw [htargetP])
    have hnormalized : Int.ModEq 2
        (b.orderSequence.entryOrZero (p + 1)) (R - 1) := by
      convert hcross using 1 <;> ring
    have hshift : Int.ModEq 2 (R - 1) (R + 1) := by
      rw [Int.modEq_iff_dvd]
      exact ⟨1, by ring⟩
    exact hnormalized.trans hshift
  have htargetLeft : b.orderSequence.entryOrZero left = R + 2 :=
    C.target_from_left left le_rfl C.left_le_anchor C.left_even
  have hgapMod : Int.ModEq 2
      (b.orderSequence.entryOrZero left -
        b.orderSequence.entryOrZero (p + 1)) 1 := by
    have h := (show Int.ModEq 2
        (b.orderSequence.entryOrZero left) (R + 2) by
      rw [htargetLeft]).sub htargetNextMod
    convert h using 1 <;> ring
  let current : Fin (n + 1) := ⟨left - 1, by omega⟩
  have hcurrentSucc :
      current.succ = (⟨left, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have hcurrentCast :
      current.castSucc = (⟨p + 1, hpNextBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_castSucc, p]
    omega
  have hgapMod' : Int.ModEq 2 (b.orderGap current) 1 := by
    unfold orderGap
    rw [hcurrentSucc, hcurrentCast]
    rw [← b.orderSequence_entryOrZero_eq_order ⟨left, hleftBound⟩,
      ← b.orderSequence_entryOrZero_eq_order ⟨p + 1, hpNextBound⟩]
    exact hgapMod
  rw [Int.modEq_iff_dvd] at hgapMod'
  rcases hgapMod' with ⟨z, hz⟩
  change Odd (b.orderGap current)
  refine ⟨-z, ?_⟩
  omega

/-- Lemma 7.6 at the last even prefix before the canonical switch.  The
only remaining external input is the `β ≤ 1` conclusion of Lemma 6.9(i). -/
theorem beli2019Lemma76_switch_of_alpha_le_one
    [Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hprevAlpha : b.alphaValue ⟨C.leftSwitch - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1) :
    let p := C.leftSwitch - 2
    let current : Fin (n + 1) := ⟨p + 1, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      have hleftTwo : 2 ≤ C.leftSwitch := by
        rcases C.left_even with ⟨d, hd⟩
        omega
      omega⟩
    (b.orderGap current ≤ 2 * (ramificationIndex K : Int) →
        b.truncatedPrefixDefect b ((-1) ^ (C.leftSwitch / 2))
            0 C.leftSwitch =
          (b.alphaValue current : WithTop ℚ)) ∧
      (b.orderGap current = 2 * (ramificationIndex K : Int) + 1 →
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
          b.truncatedPrefixDefect b ((-1) ^ (C.leftSwitch / 2))
            0 C.leftSwitch) := by
  dsimp only
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hp : C.leftSwitch - 2 + 2 < n + 2 := by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega
  have hskip := lemma76_leftSwitch_skip a b D C hleftPos
  have hodd := lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  have hlower := beli2019Lemma76_boundary_of_canonical
    a b D C hleftPos
  have hcases := b.alternatingPrefixDefect_boundary_cases
    (C.leftSwitch - 2) hp ((-1) ^ (C.leftSwitch / 2))
    (by simpa only [show C.leftSwitch - 2 + 2 = C.leftSwitch by omega]
      using hskip)
    (by simpa only [show C.leftSwitch - 2 + 1 = C.leftSwitch - 1 by omega]
      using hodd)
    hprevAlpha (by
      convert hlower using 1
      · congr 4 <;>
          first | rfl | (apply Fin.ext; rfl) | (apply Fin.ext; omega)
      · congr 1
        omega)
  simpa only [show C.leftSwitch - 2 + 1 = C.leftSwitch - 1 by omega,
    show C.leftSwitch - 2 + 2 = C.leftSwitch by omega] using hcases

end BONG.GoodBONG

end Bong
