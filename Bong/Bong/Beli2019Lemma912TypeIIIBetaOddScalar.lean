/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaOddParity

/-!
# Beli (2019), Lemma 9.12: the type-III odd-gap scalar parity split

This is the three-way parity argument at the end of the proof of condition
2.1(ii): an odd primary product, an odd source/comparison product, or an
earlier odd adjacent comparison pair gives the required explicit bound.
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
  {L N : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The abstract scalar core of the odd third-gap branch in Lemma 9.12.
Its hypotheses are exactly the prefix congruences and lower comparison-order
bounds established immediately before the parity split in the paper. -/
theorem beli2019Lemma912_typeIII_oddParity_scalar
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (source : GoodBONG q L (n + 2)) (target : GoodBONG q N (n + 2))
    (c : GoodBONG r M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (hiThree : 3 ≤ i.val)
    (base : Int)
    (hcomparison : target.representationAlphaValue c i ≤
      source.representationAlphaValue c i)
    (hsource : source.RepresentationDefectCondition c)
    (hsourceShort : Int.ModEq 2
      (source.orderSequence.prefixSum i.val)
      (target.orderSequence.prefixSum i.val))
    (htargetCurrent : Int.ModEq 2
      (target.order ⟨i.val, i.lt_large⟩) base)
    (hcomparisonSecond : Int.ModEq 2
      (c.order (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)))
      (base + 1))
    (hcomparisonLower : ∀ k : Fin (n + 2), 1 ≤ k.val →
      base + 1 ≤ c.order k)
    (hshiftNonneg : (0 : Rat) ≤
      ((target.order ⟨i.val, i.lt_large⟩ - base - 1 : Int) : Rat)) :
    target.representationAlphaValue c i ≤
      ((target.order ⟨i.val, i.lt_large⟩ - base - 1 : Int) : Rat) := by
  have hiTwo : 2 ≤ i.val := by omega
  have hcPreviousLower : base + 1 ≤
      c.order (evenTargetPreviousIndex i) :=
    hcomparisonLower _ (by
      simp only [evenTargetPreviousIndex]
      omega)
  rcases modEq_two_or_add_one
      (c.orderSequence.prefixSum (i.val - 1))
      (target.orderSequence.prefixSum (i.val + 1)) with
    hpreviousSame | hpreviousOpposite
  · have hcSucc : c.orderSequence.prefixSum i.val =
        c.orderSequence.prefixSum (i.val - 1) +
          c.orderSequence.entryOrZero (i.val - 1) := by
      simpa only [Nat.sub_add_cancel i.pos] using
        c.orderSequence.prefixSum_succ (i.val - 1)
    have htSucc : target.orderSequence.prefixSum (i.val + 1) =
        target.orderSequence.prefixSum i.val +
          target.orderSequence.entryOrZero i.val :=
      target.orderSequence.prefixSum_succ i.val
    rcases modEq_two_or_add_one
        (c.orderSequence.prefixSum i.val)
        (target.orderSequence.prefixSum i.val) with
      hcurrentSame | hcurrentOpposite
    · have hdiff := hcurrentSame.sub hpreviousSame
      rw [hcSucc, htSucc] at hdiff
      simp only [add_sub_cancel_left, sub_add_eq_sub_sub, sub_self,
        zero_sub] at hdiff
      have hcomparisonLast : Int.ModEq 2
          (c.order (evenTargetPreviousIndex i)) base := by
        have hcEntry : c.orderSequence.entryOrZero (i.val - 1) =
            c.order (evenTargetPreviousIndex i) := by
          simpa only [evenTargetPreviousIndex] using
            c.orderSequence_entryOrZero_eq_order
              (evenTargetPreviousIndex i)
        have htEntry : target.orderSequence.entryOrZero i.val =
            target.order ⟨i.val, i.lt_large⟩ := by
          rw [target.orderSequence_entryOrZero_eq_order
            ⟨i.val, i.lt_large⟩]
        rw [hcEntry, htEntry] at hdiff
        have hnegCurrent := htargetCurrent.neg
        have hnegBase : Int.ModEq 2 (-base) base := by
          rw [Int.modEq_iff_dvd]
          refine ⟨base, by ring⟩
        exact hdiff.trans (hnegCurrent.trans hnegBase)
      have hcomparisonSecondPlus : Int.ModEq 2
          (c.order
              (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) + 1)
          base := by
        have hplus := hcomparisonSecond.add (Int.ModEq.refl 1)
        have hbaseTwo : Int.ModEq 2 (base + 1 + 1) base := by
          rw [Int.modEq_iff_dvd]
          exact ⟨-1, by ring⟩
        exact hplus.trans hbaseTwo
      have hfirstLast : Int.ModEq 2
          (c.order (evenTargetPreviousIndex i))
          (c.order
            (⟨1, by have hlt := i.lt_large; omega⟩ : Fin (n + 2)) + 1) :=
        hcomparisonLast.trans hcomparisonSecondPlus.symm
      rcases exists_odd_adjacent_order_sum_of_endpoint_parity
          c i hiThree hfirstLast with ⟨j, hjOne, hjlt, hjOdd⟩
      have hjLower : base + 1 ≤ c.order j.castSucc := by
        exact hcomparisonLower j.castSucc (by
          simpa only [Fin.val_castSucc] using hjOne)
      have hjStrict : base < c.order j.castSucc := by omega
      have hgamma :=
        caseSix_previousAlpha_le_current_sub_reference_sub_one_of_odd_pair
          c i base j hjlt hjOdd hjStrict
      have hbound :=
        representationAlphaValue_le_order_sub_of_comparisonAlpha_mixed
          target c i (base + 1) hiTwo (by
            push_cast at hgamma ⊢
            linarith)
      push_cast at hbound ⊢
      linarith
    · have hsourcePlus := hsourceShort.add (Int.ModEq.refl 1)
      have hcomparisonSource : Int.ModEq 2
          (c.orderSequence.prefixSum i.val)
          (source.orderSequence.prefixSum i.val + 1) :=
        hcurrentOpposite.trans hsourcePlus.symm
      have hsourceComparison : Int.ModEq 2
          (source.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val + 1) :=
        modEq_two_add_one_left_iff_right hcomparisonSource.symm
      have hproductOdd :=
        source.comparisonPrefixProduct_order_odd_of_modEq_add_one
          c i hsourceComparison
      have hzero := truncatedPrefixDefect_eq_zero_of_odd_order
        (alphaV := alphaV) (alphaW := alphaW)
        source c i.val hproductOdd
      have hsourceTop := hsource i
      rw [hzero] at hsourceTop
      have hsourceZero : source.representationAlphaValue c i ≤ 0 := by
        exact_mod_cast hsourceTop
      exact (hcomparison.trans hsourceZero).trans hshiftNonneg
  · have hsumOdd : Odd
        (target.orderSequence.prefixSum (i.val + 1) +
          c.orderSequence.prefixSum (i.val - 1)) := by
      have hodd := odd_add_of_modEq_add_one hpreviousOpposite
      simpa only [add_comm] using hodd
    have hproductOdd :=
      signed_mixed_prefixProduct_order_odd_of_sum_odd target c i hsumOdd
    have hbound :=
      representationAlphaValue_le_order_sub_of_primaryProduct_odd_mixed
        (alphaV := alphaV) (alphaW := alphaW)
        target c i (base + 1) hproductOdd hcPreviousLower
    push_cast at hbound ⊢
    linarith

end BONG.GoodBONG

end Bong
