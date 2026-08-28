/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaOddScalar

/-!
# Beli (2019), Lemma 9.12: the type-III odd small-gap branch

When `S₄-S₃` is odd and smaller than `2e`, property P3 gives
`beta₃ = S₄-S₃`.  In the only nontrivial minimum branch, equality of
right alpha endpoints and Lemma 7.3(ii) put the right target tail in the
parity class of `R₁`.  The scalar parity theorem then proves `B_i ≤ beta_i`.
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
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- The odd branch below `2e` in the proof of Lemma 9.12(ii). -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_lt_odd
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (hfirstThird : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hsourceSecondLower :
      (a.castLength hlength).order (0 : Fin (T + 3)) ≤
        (a.castLength hlength).order (1 : Fin (T + 3)))
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 ≤ i.val)
    (hgapLt : (I.bong.castLength hlength).orderGap
        (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 2)) <
      2 * (ramificationIndex K : Int))
    (hgapOdd : Odd ((I.bong.castLength hlength).orderGap
      (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 2)))) :
    (I.bong.castLength hlength).representationAlphaValue c i ≤
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have hlt := i.lt_large; omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceAlpha
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let zero : Fin (T + 3) := ⟨0, by omega⟩
  let one : Fin (T + 3) := ⟨1, by omega⟩
  let two : Fin (T + 3) := ⟨2, by omega⟩
  let three : Fin (T + 3) := ⟨3, by
    have hlt := i.lt_large
    omega⟩
  let currentOrder : Fin (T + 3) := ⟨i.val, i.lt_large⟩
  let first : Fin (T + 2) := ⟨2, by
    have hlt := i.lt_large
    omega⟩
  let current : Fin (T + 2) := ⟨i.val - 1, by
    have hlt := i.lt_large
    omega⟩
  let base : Int := source.order zero
  have hzeroOut : zero = (0 : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have honeOut : one = (1 : Fin (T + 3)) := by
    apply Fin.ext
    change 1 = 1 % (T + 3)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have htwoOut : two = (2 : Fin (T + 3)) := by
    apply Fin.ext
    change 2 = 2 % (T + 3)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have htargetZero : target.order zero = source.order zero := by
    simp only [target, source, GoodBONG.order_castLength]
    convert beli2019Lemma912TypeIIIIndexPData_order_zero a D I using 1 <;>
      congr 1 <;> apply Fin.ext <;> rfl
  have htargetOne : target.order one = source.order one + 1 := by
    simp only [target, source, GoodBONG.order_castLength]
    have honeRaw : (⟨one.val, by omega⟩ : Fin (3 + T)) =
        (1 : Fin (3 + T)) := by
      apply Fin.ext
      change 1 = 1 % (3 + T)
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [honeRaw]
    exact beli2019Lemma912TypeIIIIndexPData_order_one a D I
  have htargetTwo : target.order two = source.order two + 1 := by
    simp only [target, source, GoodBONG.order_castLength]
    have htwoRaw : (⟨two.val, by omega⟩ : Fin (3 + T)) =
        (2 : Fin (3 + T)) := by
      apply Fin.ext
      change 2 = 2 % (3 + T)
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [htwoRaw]
    exact beli2019Lemma912TypeIIIIndexPData_order_two a D I
  have htargetThree : target.order three = source.order three := by
    exact
      beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength three (by rfl)
  have htargetCurrent : target.order currentOrder =
      source.order currentOrder := by
    exact
      beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength currentOrder (by simpa only [currentOrder] using hi)
  have hfirstCast : first.castSucc = two := by
    apply Fin.ext
    rfl
  have hfirstSucc : first.succ = three := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ = currentOrder := by
    apply Fin.ext
    simp only [current, currentOrder, Fin.val_succ]
    omega
  have htargetTwoBase : target.order two = base + 1 := by
    have hfirstThird' : source.order zero = source.order two := by
      simpa only [source, zero, two, hzeroOut, htwoOut] using hfirstThird
    rw [htargetTwo, ← hfirstThird']
  have hgapLe : target.orderGap first ≤
      2 * (ramificationIndex K : Int) := by
    exact (by simpa only [target, first] using hgapLt.le)
  have hfirstAlpha : target.alphaValue first =
      (target.orderGap first : Rat) :=
    (target.beli2009Lemma27_iii first hgapLe).2.mpr
      (Or.inr (by simpa only [target, first] using hgapOdd))
  have hshiftEq :
      (((target.order currentOrder - target.order three : Int) : Rat) +
          target.alphaValue first) =
        ((target.order currentOrder - base - 1 : Int) : Rat) := by
    rw [hfirstAlpha]
    unfold orderGap
    rw [hfirstSucc, hfirstCast, htargetTwoBase]
    push_cast
    ring
  have halphaFormula :=
    beli2019Lemma912_typeIII_alphaValue_eq_min_sourceAlpha_shift
      (alpha := sourceAlpha) a D I hlength i hi
  have halphaFormula' : target.alphaValue current =
      min (source.alphaValue current)
        ((target.order currentOrder - base - 1 : Int) : Rat) := by
    simpa only [target, source, current, currentOrder, first, three,
      hshiftEq] using halphaFormula
  have hcomparison : target.representationAlphaValue c i ≤
      source.representationAlphaValue c i :=
    beli2019Lemma912_typeIII_representationAlphaValue_le_source
      (alpha := sourceAlpha) a c D I hlength i hi
  have hsourceAlphaTop := source.representationAlpha_le_leftAlpha c hsource i
  rw [← source.coe_representationAlphaValue c i] at hsourceAlphaTop
  have hleft : target.representationAlphaValue c i ≤
      source.alphaValue current := by
    apply hcomparison.trans
    exact WithTop.coe_le_coe.mp (by
      simpa only [current] using hsourceAlphaTop)
  by_cases hsourceShift : source.alphaValue current ≤
      ((target.order currentOrder - base - 1 : Int) : Rat)
  · rw [halphaFormula']
    exact le_min hleft (hleft.trans hsourceShift)
  · have htargetAlphaEq : target.alphaValue current =
        ((target.order currentOrder - base - 1 : Int) : Rat) := by
      rw [halphaFormula', min_eq_right]
      exact (lt_of_not_ge hsourceShift).le
    have htargetAlphaShift : target.alphaValue current =
        (((target.order currentOrder - target.order three : Int) : Rat) +
          target.alphaValue first) :=
      htargetAlphaEq.trans hshiftEq.symm
    have hendpointEq : target.alphaRightEndpoint first =
        target.alphaRightEndpoint current := by
      unfold alphaRightEndpoint
      rw [hfirstSucc, hcurrentSucc, htargetAlphaShift]
      push_cast
      ring
    have hthreeMod : Int.ModEq 2 (target.order three) base := by
      rcases (show Odd (target.orderGap first) by
        simpa only [target, first] using hgapOdd) with ⟨d, hd⟩
      unfold orderGap at hd
      rw [hfirstSucc, hfirstCast, htargetTwoBase] at hd
      rw [Int.modEq_iff_dvd]
      refine ⟨-(d + 1), ?_⟩
      omega
    have htargetCurrentMod : Int.ModEq 2
        (target.order currentOrder) base := by
      by_cases hiEq : i.val = 3
      · have hcurrentThree : currentOrder = three := by
          apply Fin.ext
          simpa only [currentOrder, three] using hiEq
        rw [hcurrentThree]
        exact hthreeMod
      · have hfirstCurrent : first < current := by
          change 2 < i.val - 1
          omega
        have htail := target.beli2019Lemma73_ii
          first current hfirstCurrent hendpointEq
        have hmod := htail.order_modEq current hfirstCurrent.le le_rfl
        rw [hcurrentSucc, hfirstSucc] at hmod
        exact hmod.trans hthreeMod
    have hsourceOneMod : Int.ModEq 2 (source.order one)
        (source.order zero) := by
      apply int_modEq_two_of_even_sub
      have hzeroCast : (0 : Fin (T + 2)).castSucc = zero := by
        apply Fin.ext
        rfl
      have hzeroSucc : (0 : Fin (T + 2)).succ = one := by
        apply Fin.ext
        rfl
      unfold orderGap at hfirstGapEven
      simpa only [source, hzeroCast, hzeroSucc] using hfirstGapEven
    have hcomparisonSecond : Int.ModEq 2 (c.order one) (base + 1) := by
      have hplus := hsourceOneMod.add (Int.ModEq.refl 1)
      have hsecond' : c.order one = source.order one + 1 := by
        simpa only [source, one, honeOut] using hsecond
      rw [hsecond']
      simpa only [base] using hplus
    have hcomparisonOneLower : base + 1 ≤ c.order one := by
      have hsecond' : c.order one = source.order one + 1 := by
        simpa only [source, one, honeOut] using hsecond
      rw [hsecond']
      have hlower : source.order zero ≤ source.order one := by
        simpa only [source, zero, one, hzeroOut, honeOut] using
          hsourceSecondLower
      simp only [base]
      omega
    have hcomparisonThird :=
      beli2019Lemma912_typeIII_comparisonThird_gt_first
        source c hfirst hsecond hfirstThird hfirstGapEven
    have hcomparisonTwoLower : base + 1 ≤ c.order two := by
      have hfirst' : source.order zero = c.order zero := by
        simpa only [source, zero, hzeroOut] using hfirst
      have hbaseLt : base < c.order two := by
        rw [show base = c.order zero by simpa only [base] using hfirst']
        simpa only [zero, two, hzeroOut, htwoOut] using hcomparisonThird
      omega
    have hcomparisonLower : ∀ k : Fin (T + 3), 1 ≤ k.val →
        base + 1 ≤ c.order k := by
      intro k hk
      exact comparison_order_ge_of_first_two_parity_anchors
        c (base + 1) (by omega) (by simpa only [one] using hcomparisonOneLower)
          (by simpa only [two] using hcomparisonTwoLower) k hk
    have hsourcePrefixThree : source.orderSequence.prefixSum 3 =
        source.order zero + source.order one + source.order two := by
      rw [source.orderSequence.prefixSum_succ 2,
        source.orderSequence.prefixSum_succ 1,
        source.orderSequence.prefixSum_one,
        BeliOrderSequence.entryOrZero_of_lt source.orderSequence (by omega),
        BeliOrderSequence.entryOrZero_of_lt source.orderSequence (by omega)]
      rfl
    have htargetPrefixThree : target.orderSequence.prefixSum 3 =
        target.order zero + target.order one + target.order two := by
      rw [target.orderSequence.prefixSum_succ 2,
        target.orderSequence.prefixSum_succ 1,
        target.orderSequence.prefixSum_one,
        BeliOrderSequence.entryOrZero_of_lt target.orderSequence (by omega),
        BeliOrderSequence.entryOrZero_of_lt target.orderSequence (by omega)]
      rfl
    have hprefixThree : Int.ModEq 2
        (source.orderSequence.prefixSum 3)
        (target.orderSequence.prefixSum 3) := by
      rw [hsourcePrefixThree, htargetPrefixThree, htargetZero,
        htargetOne, htargetTwo]
      rw [Int.modEq_iff_dvd]
      exact ⟨1, by ring⟩
    have hsourceShort : Int.ModEq 2
        (source.orderSequence.prefixSum i.val)
        (target.orderSequence.prefixSum i.val) := by
      apply prefixSum_modEq_of_prefix_and_tail
        source.orderSequence target.orderSequence (by omega) hprefixThree
      intro k hkThree hkCurrent
      have hkBound : k < T + 3 := hkCurrent.trans i.lt_large
      let idx : Fin (T + 3) := ⟨k, hkBound⟩
      have horder :=
        beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
          a D I hlength idx (by simpa only [idx] using hkThree)
      rw [BeliOrderSequence.entryOrZero_of_lt source.orderSequence hkBound,
        BeliOrderSequence.entryOrZero_of_lt target.orderSequence hkBound]
      change Int.ModEq 2 (source.order idx) (target.order idx)
      rw [horder]
    have hshiftNonneg : (0 : Rat) ≤
        ((target.order currentOrder - base - 1 : Int) : Rat) := by
      rw [← htargetAlphaEq]
      exact (target.alpha_p2 current).1
    have hscalar := beli2019Lemma912_typeIII_oddParity_scalar
      (alphaV := sourceAlpha) (alphaW := comparisonAlpha)
      source target c i hi base hcomparison hsource hsourceShort
        htargetCurrentMod (by simpa only [one] using hcomparisonSecond)
        hcomparisonLower hshiftNonneg
    rw [htargetAlphaEq]
    exact hscalar

end BONG.GoodBONG

end Bong
