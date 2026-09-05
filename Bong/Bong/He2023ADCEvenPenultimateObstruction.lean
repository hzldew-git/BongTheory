/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenTerminalObstruction
import Bong.Bong.SelfPrefixDomination

/-!
# The penultimate defect obstruction in He (2025), Lemma 6.5(ii)

All intermediate defects retain their endpoint alpha caps. Empty target
prefixes and the omitted secondary candidate at n = 2 are treated explicitly.
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
  {L : Lattice K V} {M : Lattice K W}

/-- Pairs with extremal negative order gap have a signed prefix capped
defect at least 2e. This includes the empty prefix without an alpha_0. -/
theorem heADCExtremalPairs_prefixDefect {m : Nat} (a : GoodBONG q L (m + 1))
    (p : Nat) (hp : 2 * p ≤ m + 1)
    (hgap : ∀ t (ht : t < p), a.orderGap ⟨2 * t, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a ((-1) ^ p) 0 (2 * p) := by
  cases p with
  | zero =>
      simp [truncatedPrefixDefect, prefixAlphaCap_zero, GoodBONG.prefixProduct,
        defectOrder_one]
  | succ p =>
      have H := a.truncatedPrefixDefect_alternating_ge 0 p (by omega)
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) (fun t ht ↦ ?_)
      · simpa only [zero_add] using H
      · have C := a.heADC2025Proposition34 ⟨2 * t, by omega⟩
        have hd := C.alphaZeroDefect (C.alphaZero.mpr (hgap t (by omega)))
        simpa only [heADCAdjacentCappedDefect, heHuAdjacentCappedDefect, zero_add] using hd

/-- The mixed capped defect in Lemma 6.5(ii) is at least 2e. -/
theorem heADCEvenPenultimate_mixedDefect (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 1)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int))
    (hTarget : ∀ i : Fin (2 * k + 2),
      b.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] ⟨i.val, by omega⟩) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (2 * k + 2) (2 * k) := by
  have hsource := a.heADCExtremalPairs_prefixDefect (k + 1) (by omega) (fun t ht ↦ ?_)
  · have htarget := b.heADCExtremalPairs_prefixDefect k (by omega) (fun t ht ↦ ?_)
    · have hdom := a.truncatedPrefixDefect_selfPrefixes_domination b
        ((-1) ^ (k + 1)) ((-1) ^ k) (2 * (k + 1)) (2 * k)
      have H := (le_min hsource htarget).trans hdom
      have hsign : (-1 : Kˣ) ^ (k + 1) * (-1) ^ k = -1 := by
        rw [← pow_add]
        exact (show Odd (k + 1 + k) from ⟨k, by omega⟩).neg_one_pow
      simpa only [hsign, show 2 * (k + 1) = 2 * k + 2 by omega] using H
    · have heven : Even (2 * t) := ⟨t, by omega⟩
      have hodd : ¬ Even (2 * t + 1) := by rintro ⟨s, hs⟩; omega
      have hleft := hTarget ⟨2 * t, by omega⟩
      have hright := hTarget ⟨2 * t + 1, by omega⟩
      simp only [heADCMaximalOrderProfile, dif_pos (show 2 * t < 2 * k by omega),
        if_pos heven] at hleft
      simp only [heADCMaximalOrderProfile, dif_pos (show 2 * t + 1 < 2 * k by omega),
        if_neg hodd] at hright
      change b.order ⟨2 * t + 1, by omega⟩ - b.order ⟨2 * t, by omega⟩ = _
      rw [hleft, hright, sub_zero]
  · by_cases htk : t = k
    · subst t
      change a.order ⟨2 * k + 1, by omega⟩ - a.order ⟨2 * k, by omega⟩ = _
      rw [hprevious, hlast]
      omega
    · have heven : Even (2 * t) := ⟨t, by omega⟩
      have hodd : ¬ Even (2 * t + 1) := by rintro ⟨s, hs⟩; omega
      have hleft := hhead ⟨2 * t, by omega⟩
      have hright := hhead ⟨2 * t + 1, by omega⟩
      simp only [if_pos heven] at hleft
      simp only [if_neg hodd] at hright
      change a.order ⟨2 * t + 1, by omega⟩ - a.order ⟨2 * t, by omega⟩ = _
      rw [hleft, hright, sub_zero]

/-- The order-profile form of He (2025), Lemma 6.5(ii), with failure
at the single paper index n-1, including n = 2. -/
theorem heADC2025Lemma65ii_of_orders (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 1)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int))
    (hTarget : ∀ i : Fin (2 * k + 2),
      b.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] ⟨i.val, by omega⟩) :
    let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
      ⟨2 * k + 1, by omega, by omega, by omega⟩
    ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 1) (2 * k + 1) := by
  let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
    ⟨2 * k + 1, by omega, by omega, by omega⟩
  change ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
    a.truncatedPrefixDefect b 1 (2 * k + 1) (2 * k + 1)
  have hprevB : b.order ⟨2 * k, by omega⟩ = 0 := by
    simpa [heADCMaximalOrderProfile] using hTarget ⟨2 * k, by omega⟩
  have hheads : a.orderSequence.prefixSum (2 * k) = b.orderSequence.prefixSum (2 * k) := by
    apply BeliOrderSequence.prefixSum_eq_of_entryOrZero_eq_before
    intro j hj
    rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega),
      BeliOrderSequence.entryOrZero_of_lt _ (by omega), orderSequence_at, orderSequence_at]
    have hb := hTarget ⟨j, by omega⟩
    simp only [heADCMaximalOrderProfile, dif_pos hj] at hb
    exact (hhead ⟨j, hj⟩).trans hb.symm
  have hodd : Odd (ordUnit K (a.prefixProduct (2 * k + 1) * b.prefixProduct (2 * k + 1))) := by
    rw [ordUnit_mul,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum _ (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum _ (by omega),
      BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_succ,
      a.orderSequence.entryOrZero_of_lt (show 2 * k < 2 * k + 3 by omega),
      b.orderSequence.entryOrZero_of_lt (show 2 * k < 2 * k + 2 by omega)]
    simp only [orderSequence_at, hheads, hprevious, hprevB]
    exact ⟨b.orderSequence.prefixSum (2 * k), by ring⟩
  have hhalf : (0 : WithTop ℚ) < a.representationHalfGap b i := by
    simp only [representationHalfGap, i, show 2 * k + 1 - 1 = 2 * k by omega,
      hlast, hprevB, sub_zero]
    apply WithTop.coe_lt_coe.mpr
    push_cast
    linarith
  have hprimary : (0 : WithTop ℚ) < a.representationPrimaryDefect b i := by
    have hmix := heADCEvenPenultimate_mixedDefect k a b hhead hprevious hlast hTarget
    have hbound := add_le_add
      (le_rfl : ((((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ)) : WithTop ℚ) ≤ _)
      hmix
    have hsum : ((((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ)) : WithTop ℚ) +
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) = 1 := by
      have hq : ((1 - 2 * (ramificationIndex K : Int) : Int) : ℚ) +
          2 * (ramificationIndex K : ℚ) = 1 := by push_cast; ring
      rw [← WithTop.coe_add]
      exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hq
    rw [hsum] at hbound
    have hpos := (show (0 : WithTop ℚ) < 1 by norm_num).trans_le hbound
    simpa only [representationPrimaryDefect, i,
      show 2 * k + 1 - 1 = 2 * k by omega, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
      hlast, hprevB, sub_zero] using hpos
  have hprime : (0 : WithTop ℚ) < a.representationAlphaPrime b i := by
    by_cases hi : 1 < i.val ∧ i.val + 1 < 2 * k + 3
    · rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
      refine lt_min hprimary ?_
      apply lt_of_not_ge
      intro hsecondary
      have hpair := a.sourcePair_le_targetPair_of_secondary_le_zero b i hi hsecondary
      have hk : 0 < k := by dsimp only [i] at hi; omega
      have hoddIndex : ¬ Even (2 * k - 1) := by rintro ⟨s, hs⟩; omega
      have hpreB : b.order ⟨2 * k - 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
        have H := hTarget ⟨2 * k - 1, by omega⟩
        simpa only [heADCMaximalOrderProfile, dif_pos (show 2 * k - 1 < 2 * k by omega),
          if_neg hoddIndex] using H
      have hnext := a.good ⟨2 * k, by omega⟩ (by change 2 * k + 2 < 2 * k + 3; omega)
      change a.order ⟨2 * k, by omega⟩ ≤ a.order ⟨2 * k + 2, by omega⟩ at hnext
      rw [hprevious] at hnext
      simp only [i, show 2 * k + 1 - 2 = 2 * k - 1 by omega,
        show 2 * k + 1 - 1 = 2 * k by omega, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
        hlast, hpreB, hprevB] at hpair
      omega
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b i hi]
      exact hprimary
  intro h
  rw [a.truncatedPrefixDefect_eq_zero_of_odd_order b (2 * k + 1) hodd,
    a.coe_representationAlphaValue b i, a.representationAlpha_eq_min_halfGap_prime b i] at h
  exact (not_le_of_gt (lt_min hhalf hprime)) h

section PublishedTargets

variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Lemma 6.5(ii), for arbitrary good BONGs on both named
unit-uniformizer maximal target classes. -/
theorem heADC2025Lemma65ii (k : Nat) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 2))
    (_hL : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hmodel :
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW1Even k (ε * uniformizerPowerUnit K 1)))
        M (heADCN1Even k (ε * uniformizerPowerUnit K 1)).lattice ∨
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)))
        M (heADCN2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)).lattice)
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 1)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int)) :
    let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
      ⟨2 * k + 1, by omega, by omega, by omega⟩
    ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 1) (2 * k + 1) :=
  heADC2025Lemma65ii_of_orders k a b hhead hprevious hlast
    (heADCUniformizerTest_orders k ε hε b hM hmodel)

end PublishedTargets

end BONG.GoodBONG

end Bong
