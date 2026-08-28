/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaP4P6Proof

/-!
# Beli (2006), the odd equality branch of property P3

For an odd adjacent order gap, the adjacent square class has odd valuation
and hence zero relative quadratic defect.  Its local defect candidate is
therefore exactly the order gap.  Combined with the general lower bound for
gaps at most `2e`, this proves the odd equality branch of P3 without assuming
any alpha law.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- An odd adjacent order gap makes the corresponding adjacent defect zero. -/
theorem adjacentDefect_eq_zero_of_odd_orderGap
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hodd : Odd (b.orderGap i)) :
    b.adjacentDefect i = 0 := by
  let hi : i.castSucc.val + 1 < n + 1 :=
    Nat.add_lt_add_right i.isLt 1
  let parameter := b.toBONG.adjacentParameter i.castSucc hi
  have hparameterOrder : ordUnit K parameter = b.orderGap i := by
    dsimp only [parameter, hi]
    rw [b.toBONG.ordUnit_adjacentParameter i.castSucc
      (Nat.add_lt_add_right i.isLt 1)]
    rfl
  have hoddNeg : Odd (ordUnit K (-parameter)) := by
    rw [ordUnit_neg, hparameterOrder]
    exact hodd
  have hzero : quadraticDefect K (-parameter) = 0 :=
    quadraticDefect_eq_zero_of_odd_ordUnit (-parameter) hoddNeg
  have hproductZero : quadraticDefect K (b.adjacentProduct i) = 0 := by
    rw [b.adjacentProduct_eq_neg_adjacentParameter_mul_square i,
      quadraticDefect_mul_square]
    exact hzero
  unfold adjacentDefect defectOrder
  rw [hproductZero]
  rfl

/-- The local right candidate at an odd gap is the gap itself. -/
theorem rightDefectCandidate_self_eq_orderGap_of_odd
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hodd : Odd (b.orderGap i)) :
    b.rightDefectCandidate i i =
      (((b.orderGap i : Int) : ℚ) : WithTop ℚ) := by
  rw [rightDefectCandidate,
    b.adjacentDefect_eq_zero_of_odd_orderGap i hodd]
  unfold orderGap
  simp

/-- The odd equality direction of Beli (2006), property P3. -/
theorem alphaValue_eq_orderGap_of_odd_of_le_twoE
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : b.orderGap i ≤ 2 * (ramificationIndex K : Int))
    (hodd : Odd (b.orderGap i)) :
    b.alphaValue i = (b.orderGap i : ℚ) := by
  apply le_antisymm
  · have hupper := b.alpha_le_rightDefectCandidate (i := i) (j := i) le_rfl
    rw [b.rightDefectCandidate_self_eq_orderGap_of_odd i hodd,
      ← b.coe_alphaValue] at hupper
    exact_mod_cast hupper
  · exact b.orderGap_le_alphaValue_of_le_twoE i hgap

end BONG.GoodBONG

end Bong
