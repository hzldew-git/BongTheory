/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaProperties
import Bong.Bong.DefectArithmetic

/-!
# Beli (2006), property P7

For the reverse-dual BONG, values are inverted and reversed.  Hence order
gaps and half-gap candidates reverse, adjacent defects are unchanged, and
left and right defect candidates are interchanged.  Taking the two finite
minima proves P7 without an additional local-field law.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

@[simp]
theorem rev_succ_eq_rev_castSucc (i : Fin n) :
    Fin.rev i.succ = (Fin.rev i).castSucc := by
  apply Fin.ext
  simp

@[simp]
theorem rev_castSucc_eq_rev_succ (i : Fin n) :
    Fin.rev i.castSucc = (Fin.rev i).succ := by
  apply Fin.ext
  simp
  omega

/-- Values of a supplied reverse-dual good BONG. -/
theorem reverseDual_valueUnit
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin (n + 1)) :
    c.valueUnit i = (b.valueUnit (Fin.rev i))⁻¹ := by
  apply Units.ext
  change c.toBONG.value i =
    ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K)
  rw [← c.toBONG.quadratic_ambientVector, h i,
    b.toBONG.quadratic_reverseDualVector]

/-- Orders of a supplied reverse-dual good BONG. -/
theorem reverseDual_order
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin (n + 1)) :
    c.order i = -b.order (Fin.rev i) := by
  change c.toBONG.order i = -b.toBONG.order (Fin.rev i)
  have hv : c.toBONG.valueUnit i =
      (b.toBONG.valueUnit (Fin.rev i))⁻¹ :=
    b.reverseDual_valueUnit c h i
  rw [c.toBONG.order_eq_ordUnit, hv, ordUnit_inv,
    ← b.toBONG.order_eq_ordUnit]

/-- Adjacent order gaps reverse without a sign change. -/
theorem reverseDual_orderGap
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin n) :
    c.orderGap i = b.orderGap (Fin.rev i) := by
  unfold orderGap
  rw [b.reverseDual_order c h i.succ,
    b.reverseDual_order c h i.castSucc,
    rev_succ_eq_rev_castSucc, rev_castSucc_eq_rev_succ]
  ring

/-- Adjacent products of the reverse dual are inverses of the reversed
adjacent products. -/
theorem reverseDual_adjacentProduct
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (j : Fin n) :
    c.adjacentProduct j = (b.adjacentProduct (Fin.rev j))⁻¹ := by
  unfold adjacentProduct
  rw [b.reverseDual_valueUnit c h j.castSucc,
    b.reverseDual_valueUnit c h j.succ,
    rev_castSucc_eq_rev_succ, rev_succ_eq_rev_castSucc]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero (b.valueUnit (Fin.rev j).castSucc),
    Units.ne_zero (b.valueUnit (Fin.rev j).succ)]

/-- Embedded quadratic-defect order is invariant under inversion. -/
theorem defectOrder_inv_for_alpha (x : Kˣ) :
    defectOrder (K := K) x⁻¹ = defectOrder (K := K) x := by
  unfold defectOrder
  rw [quadraticDefect_inv]

/-- Adjacent defects reverse. -/
theorem reverseDual_adjacentDefect
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (j : Fin n) :
    c.adjacentDefect j = b.adjacentDefect (Fin.rev j) := by
  unfold adjacentDefect
  rw [b.reverseDual_adjacentProduct c h j, defectOrder_inv_for_alpha]

/-- Half-gap candidates reverse. -/
theorem reverseDual_halfGapCandidate
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin n) :
    c.halfGapCandidate i = b.halfGapCandidate (Fin.rev i) := by
  change (((((c.orderGap i : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) =
    (((((b.orderGap (Fin.rev i) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
  rw [b.reverseDual_orderGap c h i]

/-- A left candidate of the reverse dual is a right candidate of the
original BONG. -/
theorem reverseDual_leftDefectCandidate
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i j : Fin n) :
    c.leftDefectCandidate i j =
      b.rightDefectCandidate (Fin.rev i) (Fin.rev j) := by
  unfold leftDefectCandidate rightDefectCandidate
  rw [b.reverseDual_order c h i.succ,
    b.reverseDual_order c h j.castSucc,
    b.reverseDual_adjacentDefect c h j,
    rev_succ_eq_rev_castSucc, rev_castSucc_eq_rev_succ]
  congr 1
  norm_cast
  ring

/-- A right candidate of the reverse dual is a left candidate of the
original BONG. -/
theorem reverseDual_rightDefectCandidate
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i j : Fin n) :
    c.rightDefectCandidate i j =
      b.leftDefectCandidate (Fin.rev i) (Fin.rev j) := by
  unfold leftDefectCandidate rightDefectCandidate
  rw [b.reverseDual_order c h j.succ,
    b.reverseDual_order c h i.castSucc,
    b.reverseDual_adjacentDefect c h j,
    rev_succ_eq_rev_castSucc, rev_castSucc_eq_rev_succ]
  congr 1
  norm_cast
  ring

/-- The reverse-dual alpha is bounded below by the reversed original
alpha. -/
theorem alpha_reverse_le_reverseDual_alpha
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin n) :
    b.alpha (Fin.rev i) ≤ c.alpha i := by
  apply Finset.le_min' _ _ _
  intro x hx
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rcases hx with hhalf | hleft | hright
  · rw [hhalf, b.reverseDual_halfGapCandidate c h i]
    exact b.alpha_le_halfGapCandidate (Fin.rev i)
  · rcases hleft with ⟨j, hji, hj⟩
    rw [← hj, b.reverseDual_leftDefectCandidate c h i j]
    apply b.alpha_le_rightDefectCandidate
    exact Fin.rev_le_rev.mpr hji
  · rcases hright with ⟨j, hij, hj⟩
    rw [← hj, b.reverseDual_rightDefectCandidate c h i j]
    apply b.alpha_le_leftDefectCandidate
    exact Fin.rev_le_rev.mpr hij

/-- The reverse inequality between the two alpha minima. -/
theorem reverseDual_alpha_le_alpha_reverse
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (h : b.IsReverseDualGoodBONG c) (i : Fin n) :
    c.alpha i ≤ b.alpha (Fin.rev i) := by
  apply Finset.le_min' _ _ _
  intro x hx
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rcases hx with hhalf | hleft | hright
  · rw [hhalf, ← b.reverseDual_halfGapCandidate c h i]
    exact c.alpha_le_halfGapCandidate i
  · rcases hleft with ⟨j, hji, hj⟩
    let k : Fin n := Fin.rev j
    have hik : i ≤ k := by
      simpa only [k, Fin.rev_rev] using (Fin.rev_le_rev.mpr hji)
    have hk : Fin.rev k = j := by simp [k]
    rw [← hj, ← hk, ← b.reverseDual_rightDefectCandidate c h i k]
    exact c.alpha_le_rightDefectCandidate hik
  · rcases hright with ⟨j, hij, hj⟩
    let k : Fin n := Fin.rev j
    have hki : k ≤ i := by
      simpa only [k, Fin.rev_rev] using (Fin.rev_le_rev.mpr hij)
    have hk : Fin.rev k = j := by simp [k]
    rw [← hj, ← hk, ← b.reverseDual_leftDefectCandidate c h i k]
    exact c.alpha_le_leftDefectCandidate hki

/-- Beli (2006), property P7. -/
theorem satisfiesAlphaP7_proved (b : GoodBONG q L (n + 1)) :
    b.SatisfiesAlphaP7 := by
  intro c h i
  apply WithTop.coe_injective
  rw [c.coe_alphaValue, b.coe_alphaValue]
  exact le_antisymm (b.reverseDual_alpha_le_alpha_reverse c h i)
    (b.alpha_reverse_le_reverseDual_alpha c h i)

end BONG.GoodBONG

end Bong
