/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79SecondaryCurrent
import Bong.Bong.Beli2019Lemma79TypeIIPrefixParity

/-!
# Beli (2019), Lemma 7.9(ii), case 5: the alpha bound

In the type-II core, the comparison alpha is at most one.  Equality of the
current comparison order with the plateau uses the primary candidate.  A
strictly smaller comparison order forces the pair alternative in condition
2.1(i), after which Lemma 2.7(ii) supplies the current-prefix secondary
candidate.  At the last core coordinate its defect vanishes by odd order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The representation alpha is at most one throughout case 5 of the proof
of Lemma 7.9(ii). -/
theorem beli2019Lemma79_typeII_core_alpha_le_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero < i.val)
    (hright : i.val + 1 < D.outer.transition.firstTwo)
    (hcPrevious : c.orderSequence.entryOrZero (i.val - 1) ≤
      b.orderSequence.entryOrZero D.outer.transition.lastZero)
    (heven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    b.representationAlphaValue c i ≤ 1 := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hiPrevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have htargetMiddle (j : Nat)
      (hleftJ : D.outer.transition.lastZero < j)
      (hrightJ : j + 1 < D.outer.transition.firstTwo) :
      b.orderSequence.entryOrZero j = T := by
    have hcommon := D.outer.transition.middle j hleftJ hrightJ
    have hsource := D.middle j hleftJ hrightJ
    exact hcommon.symm.trans (by simpa only [T] using hsource)
  have hbPrevious : b.orderSequence.entryOrZero (i.val - 1) = T := by
    by_cases heq : i.val - 1 = D.outer.transition.lastZero
    · rw [heq]
    · apply htargetMiddle (i.val - 1)
      · have := i.pos
        omega
      · omega
  have hbCurrent : b.orderSequence.entryOrZero i.val = T :=
    htargetMiddle i.val hleft hright
  have hnextCore := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst i.val hleft.le (by omega)
  by_cases hcEq : c.orderSequence.entryOrZero (i.val - 1) = T
  · have hprimary := b.representationAlphaValue_le_primary_nextAlpha
      c i (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega)
    have hprimary' : b.representationAlphaValue c i ≤
        ((b.orderSequence.entryOrZero i.val -
          c.orderSequence.entryOrZero (i.val - 1) : Int) : ℚ) +
          b.alphaValue ⟨i.val, by
            have hbound := D.outer.transition.firstTwo_le_rank
            omega⟩ := by
      simpa only [
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.lt_large,
        BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
        orderSequence_at] using hprimary
    rw [hbCurrent, hcEq, hnextCore] at hprimary'
    norm_num at hprimary' ⊢
    exact hprimary'
  · have hcStrict : c.orderSequence.entryOrZero (i.val - 1) < T :=
      lt_of_le_of_ne hcPrevious hcEq
    let O := (b.representationOrderCondition_iff c le_rfl).mp hbc
    rcases O.compare (i.val - 1) hiPrevious with hdirect |
        ⟨hpositive, hnextBound, hpair⟩
    · have hdirect' : b.orderSequence.entryOrZero (i.val - 1) ≤
          c.orderSequence.entryOrZero (i.val - 1) := by
        simpa only [
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence hiPrevious,
          BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
          orderSequence_at] using hdirect
      rw [hbPrevious] at hdirect'
      exact False.elim ((not_le_of_gt hcStrict) hdirect')
    · have hiInterior : 1 < i.val ∧ i.val + 1 < n + 2 := by
        constructor
        · omega
        · exact hright.trans_le D.outer.transition.firstTwo_le_rank
      have hbPreviousOrder :
          b.order ⟨i.val - 1, hiPrevious⟩ = T := by
        rw [← b.orderSequence_entryOrZero_eq_order]
        exact hbPrevious
      have hbCurrentOrder : b.order ⟨i.val, i.lt_large⟩ = T := by
        rw [← b.orderSequence_entryOrZero_eq_order]
        exact hbCurrent
      have hpair' :
          b.order ⟨i.val - 1, hiPrevious⟩ +
              b.order ⟨i.val, i.lt_large⟩ ≤
            c.order ⟨i.val - 2, by omega⟩ +
              c.order ⟨i.val - 1, hiPrevious⟩ := by
        simpa only [orderSequence_at, Nat.sub_add_cancel i.pos,
          show i.val - 1 - 1 = i.val - 2 by omega] using hpair
      have hpairT : T + T ≤
          c.order ⟨i.val - 2, by omega⟩ +
            c.order ⟨i.val - 1, hiPrevious⟩ := by
        rw [hbPreviousOrder, hbCurrentOrder] at hpair'
        exact hpair'
      have hcPreviousOrder : c.order ⟨i.val - 1, hiPrevious⟩ < T := by
        rw [← c.orderSequence_entryOrZero_eq_order]
        exact hcStrict
      by_cases hfar : i.val + 2 < D.outer.transition.firstTwo
      · have hbNext : b.orderSequence.entryOrZero (i.val + 1) = T :=
          htargetMiddle (i.val + 1) (by omega) hfar
        have hbNextOrder : b.order ⟨i.val + 1, hiInterior.2⟩ = T := by
          rw [← b.orderSequence_entryOrZero_eq_order]
          exact hbNext
        have hcross : c.order ⟨i.val - 1, hiPrevious⟩ ≤
            b.order ⟨i.val + 1, hiInterior.2⟩ := by
          rw [hbNextOrder]
          exact hcPreviousOrder.le
        have hsecondary := b.representationAlphaValue_le_secondaryCurrent
          c i hiInterior hcross
        have hfarAlpha :=
          a.beli2019Lemma69_i_typeII_targetCore_eq_one
            b D hfirst (i.val + 1) (by omega) (by omega)
        have hcap : b.prefixAlphaCap (i.val + 2) =
            (1 : WithTop ℚ) := by
          rw [b.prefixAlphaCap_of_internal (by omega) (by
            have hbound := D.outer.transition.firstTwo_le_rank
            omega)]
          have hfarAlphaTop :
              (b.alphaValue ⟨i.val + 1, by
                have hbound := D.outer.transition.firstTwo_le_rank
                omega⟩ : WithTop ℚ) = 1 := by
            exact_mod_cast hfarAlpha
          simpa only [show i.val + 2 - 1 = i.val + 1 by omega]
            using hfarAlphaTop
        have hdefectCap := b.truncatedPrefixDefect_le_leftCap
          c (-1) (i.val + 2) i.val
        rw [hcap] at hdefectCap
        let shift : Int :=
          b.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val + 1, hiInterior.2⟩ -
              c.order ⟨i.val - 2, by omega⟩ -
                c.order ⟨i.val - 1, hiPrevious⟩
        have hshift : shift ≤ 0 := by
          dsimp only [shift]
          rw [hbCurrentOrder, hbNextOrder]
          omega
        have hshiftTop : ((shift : ℚ) : WithTop ℚ) ≤ 0 := by
          exact_mod_cast hshift
        have hsecondaryUpper :
            b.representationSecondaryCurrentDefect c i hiInterior ≤ 1 := by
          unfold representationSecondaryCurrentDefect
          change ((shift : ℚ) : WithTop ℚ) +
            b.truncatedPrefixDefect c (-1) (i.val + 2) i.val ≤ 1
          calc
            ((shift : ℚ) : WithTop ℚ) +
                b.truncatedPrefixDefect c (-1) (i.val + 2) i.val ≤
              0 + 1 := add_le_add hshiftTop hdefectCap
            _ = 1 := by norm_num
        exact_mod_cast hsecondary.trans hsecondaryUpper
      · have hboundary : i.val + 2 =
            D.outer.transition.firstTwo := by omega
        have hnextIndex : i.val + 1 =
            D.outer.transition.firstTwo - 1 := by omega
        have hbNext : b.orderSequence.entryOrZero (i.val + 1) = T + 1 := by
          rw [hnextIndex, D.right_target]
        have hbNextOrder : b.order ⟨i.val + 1, hiInterior.2⟩ = T + 1 := by
          rw [← b.orderSequence_entryOrZero_eq_order]
          exact hbNext
        have hcross : c.order ⟨i.val - 1, hiPrevious⟩ ≤
            b.order ⟨i.val + 1, hiInterior.2⟩ := by
          rw [hbNextOrder]
          omega
        have hsecondary := b.representationAlphaValue_le_secondaryCurrent
          c i hiInterior hcross
        have hone : ordUnit K (1 : Kˣ) = 0 := by
          have h := ordUnit_mul K (1 : Kˣ) 1
          simp only [mul_one] at h
          omega
        have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
          have h := ordUnit_mul K (-1 : Kˣ) (-1)
          have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
          rw [hmul, hone] at h
          omega
        have hbaseOrder :
            ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val) =
              b.orderSequence.prefixSum i.val +
                c.orderSequence.prefixSum i.val := by
          rw [ordUnit_mul,
            b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
              i.val i.lt_large.le,
            c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
              i.val i.lt_large.le]
        have hrawOrder :
            ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 2) *
              c.prefixProduct i.val) =
              b.orderSequence.prefixSum i.val +
                c.orderSequence.prefixSum i.val +
                  b.orderSequence.entryOrZero i.val +
                    b.orderSequence.entryOrZero (i.val + 1) := by
          rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
            b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
              (i.val + 2) (by
                have hbound := D.outer.transition.firstTwo_le_rank
                omega),
            c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
              i.val i.lt_large.le,
            show i.val + 2 = (i.val + 1) + 1 by omega,
            b.orderSequence.prefixSum_succ,
            b.orderSequence.prefixSum_succ]
          ring
        have hrawOdd : Odd (ordUnit K
            ((-1 : Kˣ) * b.prefixProduct (i.val + 2) *
              c.prefixProduct i.val)) := by
          rw [hbaseOrder] at heven
          rcases heven with ⟨z, hz⟩
          refine ⟨z + T, ?_⟩
          rw [hrawOrder, hbCurrent, hbNext]
          omega
        have hdefectZero : defectOrder (K := K)
            ((-1 : Kˣ) * b.prefixProduct (i.val + 2) *
              c.prefixProduct i.val) = 0 := by
          unfold defectOrder
          rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hrawOdd]
          rfl
        have htruncated := b.truncatedPrefixDefect_le_defect
          c (-1) (i.val + 2) i.val
        rw [hdefectZero] at htruncated
        let shift : Int :=
          b.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val + 1, hiInterior.2⟩ -
              c.order ⟨i.val - 2, by omega⟩ -
                c.order ⟨i.val - 1, hiPrevious⟩
        have hshift : shift ≤ 1 := by
          dsimp only [shift]
          rw [hbCurrentOrder, hbNextOrder]
          omega
        have hshiftTop : ((shift : ℚ) : WithTop ℚ) ≤ 1 := by
          exact_mod_cast hshift
        have hsecondaryUpper :
            b.representationSecondaryCurrentDefect c i hiInterior ≤ 1 := by
          unfold representationSecondaryCurrentDefect
          change ((shift : ℚ) : WithTop ℚ) +
            b.truncatedPrefixDefect c (-1) (i.val + 2) i.val ≤ 1
          calc
            ((shift : ℚ) : WithTop ℚ) +
                b.truncatedPrefixDefect c (-1) (i.val + 2) i.val ≤
              1 + 0 := add_le_add hshiftTop htruncated
            _ = 1 := by norm_num
        exact_mod_cast hsecondary.trans hsecondaryUpper

end BONG.GoodBONG

end Bong
