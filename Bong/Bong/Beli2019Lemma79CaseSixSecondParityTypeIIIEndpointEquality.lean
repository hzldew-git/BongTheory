/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIBoundaryWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 6: equality of right endpoints

At the boundary witness `T_j = R + 1`, equality of the two right alpha
endpoints lets Lemma 7.3(ii) propagate the parity of `T_i` back to
`T_{j+1}`.  Thus the adjacent pair at `j` has odd order.  Its zero defect,
together with the nonnegative central defect, closes condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The endpoint-equality subcase of the type-III boundary witness already
satisfies condition 2.1(ii). -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_eq
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1))
    (hthird : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val - 1)
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hendpoint : c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let last : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hjLast : j < last := by
    change j.val < last.val
    simp only [last, evenTargetPreviousAlphaIndex]
    omega
  have hlemma73 := c.beli2019Lemma73_ii j last hjLast
    (by simpa only [last] using hendpoint)
  have hlastOrder := hlemma73.order_modEq last hjLast.le le_rfl
  have hlastSucc : last.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [last, evenTargetPreviousAlphaIndex,
      evenTargetPreviousIndex, Fin.val_succ]
    omega
  rw [hlastSucc] at hlastOrder
  have hpreviousMod :=
    beli2019Lemma79_typeIII_caseSix_thirdPrevious_modEq_sourceLeft
      a b c D hfirst hdefect hnotOverlap i hthroughLast horders
  have hpreviousMod' : Int.ModEq 2
      (c.order (evenTargetPreviousIndex i))
      (a.orderSequence.entryOrZero D.outer.transition.lastZero) := by
    change Int.ModEq 2
      (c.orderSequence.entryOrZero (evenTargetPreviousIndex i).val)
      (a.orderSequence.entryOrZero D.outer.transition.lastZero) at hpreviousMod
    rw [c.orderSequence_entryOrZero_eq_order
      (evenTargetPreviousIndex i)] at hpreviousMod
    exact hpreviousMod
  have hnextMod : Int.ModEq 2 (c.order j.succ)
      (a.orderSequence.entryOrZero D.outer.transition.lastZero) :=
    hlastOrder.symm.trans hpreviousMod'
  have hpairMod : Int.ModEq 2 (c.order j.castSucc)
      (c.order j.succ + 1) := by
    rw [hjOrder]
    exact (hnextMod.add (Int.ModEq.refl 1)).symm
  have hpairOdd : Odd (c.order j.castSucc + c.order j.succ) :=
    odd_add_of_modEq_add_one hpairMod
  have hcentralNonneg :
      0 ≤ b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) := by
    have hnonneg := c.truncatedPrefixDefect_nonneg c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1)
    rw [hthird] at hnonneg
    exact_mod_cast hnonneg
  have hcurrentMod : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val) (c.order j.castSucc) := by
    have hshifted := horders.trans
      (hpreviousMod.add (Int.ModEq.refl 1))
    simpa only [hjOrder] using hshifted
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hleftBoundary := D.outer.transition.leftBoundary
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentUpper : b.orderSequence.entryOrZero i.val ≤
      c.order j.castSucc + 1 := by
    rw [hrightBoundary, hrightIndex] at hcurrentBoundary
    omega
  have hcurrentLe : b.orderSequence.entryOrZero i.val ≤
      c.order j.castSucc := by
    rw [Int.modEq_iff_dvd] at hcurrentMod
    rcases hcurrentMod with ⟨d, hd⟩
    omega
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      b.orderSequence.entryOrZero i.val :=
    (b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩).symm
  have hreference : b.order ⟨i.val, i.lt_large⟩ - 1 <
      c.order j.castSucc := by
    rw [hcurrentOrder]
    omega
  exact lemma79_caseSix_secondParity_of_odd_pair_above_reference
    b c i (b.order ⟨i.val, i.lt_large⟩ - 1) j (by omega)
      (by omega) hpairOdd hreference

end BONG.GoodBONG

end Bong
