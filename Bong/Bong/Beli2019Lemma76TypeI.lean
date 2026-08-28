/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76CanonicalBoundary
import Bong.Bong.Beli2009BinaryRemarks

/-!
# Beli (2019), Lemma 7.6 in the type-I case

At the canonical type-I switch, the adjacent product crossing the switch has
odd valuation and hence quadratic defect zero.  The corresponding right
defect candidate proves the `beta <= 1` input from Lemma 6.9(i), completing
the boundary argument of Lemma 7.6 without an extra hypothesis.
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

/-- The `beta <= 1` instance of Lemma 6.9(i) immediately before the
canonical type-I switch. -/
theorem beli2019Lemma69_i_typeI_leftSwitch
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch) :
    b.alphaValue ⟨C.leftSwitch - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by omega⟩
  let crossing : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  have hpreviousCrossing : previous ≤ crossing := by
    change C.leftSwitch - 2 ≤ C.leftSwitch - 1
    omega
  have hgapOdd : Odd (b.orderGap crossing) := by
    simpa only [crossing] using
      lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  have ordUnit_neg_eq (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa using ord_neg K (z : K)
  have hproductOrder :
      ordUnit K (b.adjacentProduct crossing) =
        b.order crossing.castSucc + b.order crossing.succ := by
    have horderUnit (i : Fin (n + 2)) :
        ordUnit K (b.valueUnit i) = b.order i := by
      exact (b.toBONG.order_eq_ordUnit i).symm
    unfold adjacentProduct
    rw [ordUnit_neg_eq, ordUnit_mul, horderUnit, horderUnit]
  have hproductOdd : Odd (ordUnit K (b.adjacentProduct crossing)) := by
    rw [hproductOrder]
    unfold orderGap at hgapOdd
    rcases hgapOdd with ⟨z, hz⟩
    refine ⟨b.order crossing.castSucc + z, ?_⟩
    omega
  have hdefect : b.adjacentDefect crossing = 0 := by
    unfold adjacentDefect defectOrder
    rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hproductOdd]
    rfl
  have hskip := lemma76_leftSwitch_skip a b D C hleftPos
  have hcrossingSucc :
      crossing.succ = (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [crossing, Fin.val_succ]
    omega
  have hpreviousCast :
      previous.castSucc =
        (⟨C.leftSwitch - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have horderDifference :
      b.order crossing.succ - b.order previous.castSucc = 1 := by
    rw [hcrossingSucc, hpreviousCast]
    have hskip' :
        b.order ⟨C.leftSwitch, hleftBound⟩ =
          b.order ⟨C.leftSwitch - 2, by omega⟩ + 1 := by
      simpa only using hskip
    omega
  have hcandidate :
      b.rightDefectCandidate previous crossing = (1 : WithTop ℚ) := by
    unfold rightDefectCandidate
    rw [hdefect, horderDifference]
    norm_num
  have halpha := b.alpha_le_rightDefectCandidate hpreviousCrossing
  rw [← b.coe_alphaValue, hcandidate] at halpha
  exact_mod_cast halpha

/-- Lemma 7.6 at the canonical type-I switch, with its Lemma 6.9(i)
input discharged. -/
theorem beli2019Lemma76_typeI
    [Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch) :
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
  apply beli2019Lemma76_switch_of_alpha_le_one a b D C hfirst hleftPos
  exact beli2019Lemma69_i_typeI_leftSwitch a b D C hfirst hleftPos

end BONG.GoodBONG

end Bong
