/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeI
import Bong.Bong.Beli2019Lemma79EvenTypeIBoundaryAlpha

/-!
# Beli (2019), Lemma 7.6: reusable type-I boundary lower bounds

The two alternatives at the first canonical switch both dominate any
quantity bounded by the switch alpha and by `2e`.  A separate concatenation
lemma records the sign arithmetic for joining two even alternating blocks.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M : Lattice K V} {n : Nat}

/-- Two lower bounds on adjacent even alternating blocks concatenate to a
lower bound on the whole block. -/
theorem alternatingPrefixDefect_concat_lower
    (b : GoodBONG q M (n + 2)) (left right : Nat)
    (hleftRight : left ≤ right)
    (hleftEven : Even left) (hrightEven : Even right)
    (x : WithTop ℚ)
    (hprefix : x ≤
      b.truncatedPrefixDefect b ((-1) ^ (left / 2)) 0 left)
    (hsegment : x ≤
      b.truncatedPrefixDefect b ((-1) ^ ((right - left) / 2))
        left right) :
    x ≤ b.truncatedPrefixDefect b ((-1) ^ (right / 2)) 0 right := by
  have hdomination := b.truncatedPrefixDefect_domination b b
    ((-1) ^ (left / 2)) ((-1) ^ ((right - left) / 2))
      0 left right
  have hhalves : left / 2 + (right - left) / 2 = right / 2 := by
    rcases hleftEven with ⟨d, hd⟩
    rcases hrightEven with ⟨e, he⟩
    omega
  calc
    x ≤ min
        (b.truncatedPrefixDefect b ((-1) ^ (left / 2)) 0 left)
        (b.truncatedPrefixDefect b ((-1) ^ ((right - left) / 2))
          left right) := le_min hprefix hsegment
    _ ≤ b.truncatedPrefixDefect b
        (((-1) ^ (left / 2)) * ((-1) ^ ((right - left) / 2)))
          0 right := hdomination
    _ = b.truncatedPrefixDefect b ((-1) ^ (right / 2)) 0 right := by
      rw [← pow_add, hhalves]

/-- The first type-I switch prefix dominates every value bounded by both
the switch alpha and `2e`. -/
theorem beli2019Lemma76_typeI_boundary_lower
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (x : WithTop ℚ)
    (hbeta : x ≤
      (b.alphaValue ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ : WithTop ℚ))
    (htwoE : x ≤
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) :
    x ≤ b.truncatedPrefixDefect b
      ((-1) ^ (C.leftSwitch / 2)) 0 C.leftSwitch := by
  have hcases := beli2019Lemma76_typeI a b D C hfirst hleftPos
  dsimp only at hcases
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  let caseCurrent : Fin (n + 1) := ⟨C.leftSwitch - 2 + 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hcases' :
      (b.orderGap caseCurrent ≤ 2 * (ramificationIndex K : Int) →
          b.truncatedPrefixDefect b ((-1) ^ (C.leftSwitch / 2))
              0 C.leftSwitch = (b.alphaValue caseCurrent : WithTop ℚ)) ∧
        (b.orderGap caseCurrent = 2 * (ramificationIndex K : Int) + 1 →
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
            b.truncatedPrefixDefect b ((-1) ^ (C.leftSwitch / 2))
              0 C.leftSwitch) := by
    simpa only [caseCurrent] using hcases
  have hupper := lemma79_typeI_leftSwitch_gap_le_twoE_add_one
    a b D C hleftPos
  let current : Fin (n + 1) := ⟨C.leftSwitch - 1, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hcurrentEq : caseCurrent = current := by
    apply Fin.ext
    simp only [caseCurrent, current]
    omega
  have hupper' : b.orderGap caseCurrent ≤
      2 * (ramificationIndex K : Int) + 1 := by
    rw [hcurrentEq]
    simpa only [current] using hupper
  have hbeta' : x ≤ (b.alphaValue caseCurrent : WithTop ℚ) := by
    rw [hcurrentEq]
    simpa only [current] using hbeta
  by_cases hgap : b.orderGap caseCurrent ≤
      2 * (ramificationIndex K : Int)
  · rw [hcases'.1 hgap]
    exact hbeta'
  · have hgapEq : b.orderGap caseCurrent =
        2 * (ramificationIndex K : Int) + 1 := by
      omega
    exact htwoE.trans (hcases'.2 hgapEq)

end BONG.GoodBONG

end Bong
