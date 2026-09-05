/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma44
import Bong.Bong.HeHu2022Lemma57
import Bong.Bong.HeHu2022Lemma59
import Bong.Bong.Beli2019Lemma79CentralEarlyArithmetic

/-!
# He--Hu 2022, Lemma 5.10

This file formalizes the three equivalent central-representation assertions
in Lemma 5.10 of the published paper.  For odd paper rank `N = 2*k+3`, the
middle assertion keeps both quantifiers in their printed form:

* the two first-column tests use one sharp witness for `cTilde#`; and
* in the exceptional ternary case, condition (iii) is required for some
  `N_2^3(delta*pi)` with valuation-unit `delta`.

Paper indices are one based; all `Fin` indices below are zero based.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The finite testing assertion in He--Hu, Lemma 5.10(ii), for odd rank
`N=2*k+3`.  The final clause is deliberately existential, matching the word
"some" in the published statement. -/
noncomputable def HeHuLemma510TestConditions {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m) : Prop :=
  (a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 →
      (a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
        1 < a.order ⟨2 * k + 4, by omega⟩) →
      ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
        a.CentralRepresentationConditions
            (heHuLemma59Target (K := K) (heHuLemma59C a k) k) ∧
          a.CentralRepresentationConditions
            (heHuLemma59Target (K := K)
              (heHuLemma59C a k *
                heHuSharp (heHuLemma59CTilde a k) hc) k)) ∧
    (k = 0 →
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 →
      0 < a.order ⟨2 * k + 4, by omega⟩ →
      defectOrder (K := K) (a.prefixProduct 4) = ⊤ →
      ∃ delta : Kˣ, ∃ hdelta : IsValuationUnit K (delta : K),
        a.CentralRepresentationConditions
          (heHuLemma311OddSecondUnitUniformizerTail delta hdelta))

/-- Under the even predecessor conditions, Lemma 5.6 supplies conditions
(i)--(ii) of Theorem 2.8 for an arbitrary integral odd-rank target.  Beli's
Lemma 2.16 therefore identifies the original condition (iii) with its revised
form (iii'). -/
theorem heHuLemma510_original_iff_prime
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * k + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega)) :
    a.CentralRepresentationConditions b ↔
      a.CentralRepresentationConditionsPrime b := by
  have hOrder := a.heHu2022Lemma56i b (by omega) ⟨k + 1, by omega⟩ hm
    hI1 hBIntegral
  have hDefect := a.heHu2022Lemma56ii b (by omega) ⟨k + 1, by omega⟩ hm
    hAIntegral hBIntegral hI1 hI2
  have htriggers := a.beli2019Lemma216
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b (by omega) hOrder hDefect
  exact a.centralRepresentationConditions_iff_prime b htriggers

/-- The exceptional ternary test occurring in Lemma 5.10(ii) is integral. -/
theorem heHuLemma510ExceptionalTarget_integral
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    UnderlyingLatticeIsIntegral
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta) := by
  apply heHuIntegral_of_firstOrder_nonneg
    (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
  rw [heHuLemma311OddSecondUnitUniformizerTail_order]
  norm_num

/-- A literal prefix segment has the same prefix products as its parent.
This is the scalar transport used when Lemma 5.10 deletes the last target
coefficient. -/
theorem heHuLemma510_prefixProduct_eq
    {p : Nat} (b : GoodBONG r M (p + 2))
    (w : BONG.SegmentWitness b.toBONG 0 (p + 1) (by omega))
    (t : Nat) (ht : t ≤ p + 1) :
    (w.toGoodBONG b.good).prefixProduct t = b.prefixProduct t := by
  induction t with
  | zero =>
      unfold GoodBONG.prefixProduct
      simp
  | succ t ih =>
      have htShort : t < p + 1 := by omega
      have htLong : t < p + 2 := by omega
      change w.bong.prefixProduct (t + 1) =
        b.toBONG.prefixProduct (t + 1)
      have ih' := ih (by omega)
      change w.bong.prefixProduct t = b.toBONG.prefixProduct t at ih'
      rw [w.bong.prefixProduct_succ t htShort,
        b.toBONG.prefixProduct_succ t htLong, ih']
      have hv := w.valueUnit_eq ⟨t, htShort⟩
      have hsource : w.sourceIndex ⟨t, htShort⟩ =
          (⟨t, htLong⟩ : Fin (p + 2)) := by
        apply Fin.ext
        simp
      rw [hsource] at hv
      exact congrArg (fun z => b.toBONG.prefixProduct t * z) hv

/-- Removing the final coefficient can only enlarge a target prefix alpha
cap.  At internal boundaries this is Beli's Lemma 2.1 localization
inequality; at the new endpoint the shorter cap is infinity. -/
theorem heHuLemma510_prefixAlphaCap_le
    [Beli2009AlphaLocalizationLaws.{u, w} K]
    {p : Nat} (b : GoodBONG r M (p + 2))
    (w : BONG.SegmentWitness b.toBONG 0 (p + 1) (by omega))
    (t : Nat) (ht : t ≤ p + 1) :
    b.prefixAlphaCap t ≤ (w.toGoodBONG b.good).prefixAlphaCap t := by
  by_cases htZero : t = 0
  · subst t
    simp
  by_cases htLast : t = p + 1
  · subst t
    rw [(w.toGoodBONG b.good).prefixAlphaCap_last]
    exact le_top
  have htPos : 0 < t := by omega
  have htInternal : t < p + 1 := by omega
  rw [b.prefixAlphaCap_of_internal htPos (by omega),
    (w.toGoodBONG b.good).prefixAlphaCap_of_internal htPos htInternal]
  let s : AlphaLocalizationIndex (p + 1) := {
    start := 0
    pivot := t - 1
    stop := p
    start_le_pivot := by omega
    pivot_lt_stop := by omega
    stop_lt := by omega }
  have hloc := b.beli2009Lemma21_le_segmentAlpha s w
  rw [b.coe_alphaValue, (w.toGoodBONG b.good).coe_alphaValue]
  simpa only [s, AlphaLocalizationIndex.pivotFin,
    AlphaLocalizationIndex.localPivot, Nat.sub_zero] using hloc

/-- The capped mixed defects for the full target are bounded by those for
the target with its last coefficient deleted. -/
theorem heHuLemma510_truncatedPrefixDefect_le
    [Beli2009AlphaLocalizationLaws.{u, w} K]
    {ma p : Nat} (a : GoodBONG q L (ma + 1))
    (b : GoodBONG r M (p + 2))
    (w : BONG.SegmentWitness b.toBONG 0 (p + 1) (by omega))
    (epsilon : Kˣ) (i t : Nat) (ht : t ≤ p + 1) :
    a.truncatedPrefixDefect b epsilon i t ≤
      a.truncatedPrefixDefect (w.toGoodBONG b.good) epsilon i t := by
  unfold truncatedPrefixDefect
  rw [← b.heHuLemma510_prefixProduct_eq w t ht]
  exact min_le_min le_rfl
    (min_le_min le_rfl (b.heHuLemma510_prefixAlphaCap_le w t ht))

/-- Integrality descends to the canonical prefix lattice. -/
theorem heHuLemma510_prefix_integral
    {p : Nat} (b : GoodBONG r M (p + 1))
    (hBIntegral : Lattice.IsIntegral r M)
    (w : BONG.PrefixWitness b.toBONG p (by omega)) :
    Lattice.IsIntegral
      (r.restrict w.carrier w.nondegenerate) w.lattice := by
  rw [Lattice.isIntegral_iff_forall]
  intro x hx
  have hparent := (Lattice.isIntegral_iff_forall r M).mp hBIntegral
    (x : W) (w.contained x hx)
  change Dyadic.IsIntegral K (r.quadratic (x : W))
  exact hparent

/-- Proposition 2.7(v) in the target form needed in the terminal
`alpha_n=0` branch: an integral odd target ending in order zero is a
first-column odd space. -/
theorem heHuLemma510_target_represents_oddFirst
    {k : Nat} (b : GoodBONG r M (2 * k + 3))
    (hBIntegral : Lattice.IsIntegral r M)
    (hTargetPrevious : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hTargetLast : b.order ⟨2 * k + 2, by omega⟩ = 0) :
    ∃ epsilon : Kˣ,
      IsValuationUnit K (epsilon : K) ∧
        DiagonalRepresents
          (b.prefixValues (2 * k + 3) le_rfl)
          (diagonalUnitCoefficients
            (heHuOddFirst (K := K) k epsilon)) := by
  let last : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hlastEven : Even last.val := ⟨k + 1, by simp only [last]; omega⟩
  let j : Fin (2 * k + 3) := ⟨2 * k + 1, by omega⟩
  have hjOdd : Odd j.val := ⟨k, by simp only [j]⟩
  have hjOrder : b.order j =
      -(2 * (ramificationIndex K : Int)) := by
    simpa only [j] using hTargetPrevious
  have hnext : j.val + 1 < 2 * k + 3 := by
    simp only [j]
    omega
  have hnextEven : Even (b.order ⟨j.val + 1, hnext⟩) := by
    have hindex : (⟨j.val + 1, hnext⟩ : Fin (2 * k + 3)) = last := by
      apply Fin.ext
      rfl
    rw [hindex, hTargetLast]
    exact Even.zero
  rcases b.heHu2022Proposition27v hBIntegral j hjOdd hjOrder hnext
      hnextEven with ⟨w⟩
  rcases w with
    ⟨pairs, hpairCount, hextended, epsilon, squareFactor,
      hepsilonUnit, hepsilonClass, hnormal⟩
  have hpairs : pairs = k + 1 := by
    simp only [j] at hpairCount
    omega
  subst pairs
  rcases hnormal with ⟨f⟩
  refine ⟨epsilon, hepsilonUnit, ?_⟩
  have hdiagRaw : DiagonalRepresents
      (b.prefixValues (2 * (k + 1) + 1) hextended)
      (diagonalUnitCoefficients
        (Fin.snoc
          (standardHyperbolicEndpointTower (K := K) (k + 1)) epsilon)) := by
    refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
    intro x
    have hq := f.map_quadratic x
    have hq' :
        diagonalQuadratic
            (diagonalUnitCoefficients
              (Fin.snoc
                (standardHyperbolicEndpointTower
                  (K := K) (k + 1)) epsilon))
            (f.toLinearEquiv x) =
          diagonalQuadratic
            (b.prefixValues (2 * (k + 1) + 1) hextended) x := by
      simpa only [BONG.GoodBONG.prefixDiagonalSpace,
        hyperbolicEndpointTowerWithLineSpace,
        QuadraticSpace.finiteDiagonal_quadratic_apply,
        diagonalUnitCoefficients] using hq
    exact hq'
  rw [heHuLemma43_snoc_standard_eq_oddFirst (K := K) k epsilon]
    at hdiagRaw
  let hdim : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have hcast := heHuLemma43_diagonalRepresents_castLengths
    hdim hdim hdiagRaw
  have hsourceEq :
      (fun i : Fin (2 * k + 3) =>
        b.prefixValues (2 * (k + 1) + 1) hextended
          (Fin.cast hdim.symm i)) =
        b.prefixValues (2 * k + 3) le_rfl := by
    funext i
    unfold BONG.GoodBONG.prefixValues
    congr 1
  have htargetEq :
      (fun i : Fin (2 * k + 3) =>
        diagonalUnitCoefficients (heHuOddFirst (K := K) k epsilon)
          (Fin.cast hdim.symm i)) =
        diagonalUnitCoefficients (heHuOddFirst (K := K) k epsilon) := by
    funext i
    unfold diagonalUnitCoefficients
    congr 1
  rw [hsourceEq, htargetEq] at hcast
  exact hcast

/-- Every nonterminal central trigger for an odd target descends to the
even target obtained by deleting its last coefficient.  Lemma 4.4 then
supplies the required representation. -/
theorem heHuLemma510_nonterminal_representation
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [Beli2009AlphaLocalizationLaws.{u, w} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * k + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (i : CentralRepresentationIndex (m + 3) (2 * k + 3))
    (hi : i.val ≤ 2 * k + 3)
    (htrigger : a.centralDefectTrigger b i) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega)) := by
  let wp := b.toBONG.prefixWitness (2 * k + 2) (by omega)
  let bp := wp.toGoodBONG b.good
  have hbpIntegral : Lattice.IsIntegral
      (r.restrict wp.carrier wp.nondegenerate) wp.lattice :=
    b.heHuLemma510_prefix_integral hBIntegral wp
  have hprime : a.CentralRepresentationConditionsPrime bp :=
    a.heHu2022Lemma44SufficiencyPrime bp (by omega) hAIntegral
      hbpIntegral hI1 hI2
  let j : CentralRepresentationIndex (m + 3) (2 * k + 2) := {
    val := i.val
    one_lt := i.one_lt
    lt_large := i.lt_large
    le_small_succ := by omega }
  have horder :
      bp.order ⟨i.val - 2, by omega⟩ =
        b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ := by
    change wp.bong.order ⟨i.val - 2, by omega⟩ =
      b.toBONG.order ⟨i.val - 2, by omega⟩
    have ho := wp.toSegmentWitness.order_eq
      ⟨i.val - 2, by omega⟩
    have hsource : wp.sourceIndex ⟨i.val - 2, by omega⟩ =
        (⟨i.val - 2, by omega⟩ : Fin (2 * k + 3)) := by
      apply Fin.ext
      simp only [wp, BONG.SegmentWitness.sourceIndex_val,
        Nat.zero_add]
    rw [hsource] at ho
    exact ho
  have hprevious : a.centralPreviousDefect b i ≤
      a.centralPreviousDefect bp j := by
    simpa only [centralPreviousDefect, j] using
      a.heHuLemma510_truncatedPrefixDefect_le b wp.toSegmentWitness
        (-1) i.val (i.val - 2) (by omega)
  have hcurrent : a.centralCurrentDefect b i ≤
      a.centralCurrentDefect bp j := by
    simpa only [centralCurrentDefect, j] using
      a.heHuLemma510_truncatedPrefixDefect_le b wp.toSegmentWitness
        (-1) (i.val + 1) (i.val - 1) (by omega)
  have htrigger' : a.centralDefectTrigger bp j := by
    unfold centralDefectTrigger at htrigger ⊢
    simp only [j]
    constructor
    · rw [horder]
      exact htrigger.1
    · rw [horder]
      exact htrigger.2.trans_le (add_le_add hprevious hcurrent)
  have hrep := hprime j htrigger'
  have htarget :
      bp.prefixValues (j.val - 1) (by
        have := j.le_small_succ
        omega) =
        b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) := by
    funext t
    have htIndex : t.val < i.val - 1 := by
      simpa only [j] using t.isLt
    have htShort : t.val < 2 * k + 2 := by omega
    have htLong : t.val < 2 * k + 3 := by omega
    change wp.bong.value ⟨t.val, htShort⟩ =
      b.toBONG.value ⟨t.val, htLong⟩
    have hv := wp.toSegmentWitness.value_eq ⟨t.val, htShort⟩
    have hsource : wp.sourceIndex ⟨t.val, htShort⟩ =
        (⟨t.val, htLong⟩ : Fin (2 * k + 3)) := by
      apply Fin.ext
      simp only [wp, BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]
    rw [hsource] at hv
    exact hv
  rw [htarget] at hrep
  simpa only [j] using hrep

/-- In the terminal `alpha_n=0` branch, the odd last source order makes the
current mixed defect zero.  The trigger then forces the target's final gap
to be `2e`, so Proposition 2.7(v) and Lemma 3.14(ii) give the required
codimension-one representation. -/
theorem heHuLemma510_alphaZero_terminal_representation
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * k + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI2O (2 * k + 3) (by omega) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0)
    (i : CentralRepresentationIndex (m + 3) (2 * k + 3))
    (hi : i.val = 2 * k + 4)
    (htrigger : a.centralDefectTrigger b i) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega)) := by
  have hSourceBoundary : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) :=
    a.heHu2022Lemma54i (n := 2 * k + 3) (by omega)
      ⟨k + 1, by omega⟩ (by omega) hI1 hAlpha
  have hSourceNextCases :
      a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 4, by omega⟩ = 1 :=
    hOdd.1 hAlpha
  let targetLast : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hTargetLastEven : Even targetLast.val := ⟨k + 1, by
    simp only [targetLast]
    omega⟩
  have hTargetLastNonnegative : 0 ≤ b.order targetLast :=
    ((b.heHu2022Proposition27i hBIntegral).oddIndexed
      targetLast targetLast le_rfl hTargetLastEven hTargetLastEven).1
  have hTargetIndex :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (2 * k + 3)) = targetLast := by
    apply Fin.ext
    simp only [targetLast]
    omega
  have hSourceIndex :
      (⟨i.val, by
        have := i.lt_large
        omega⟩ : Fin (m + 3)) =
        ⟨2 * k + 4, by omega⟩ := by
    apply Fin.ext
    exact hi
  have hOrderTrigger : b.order targetLast <
      a.order ⟨2 * k + 4, by omega⟩ := by
    have h := htrigger.1
    rw [hTargetIndex, hSourceIndex] at h
    exact h
  have hSourceNext : a.order ⟨2 * k + 4, by omega⟩ = 1 := by
    rcases hSourceNextCases with hzero | hone
    · rw [hzero] at hOrderTrigger
      exact (not_lt_of_ge hTargetLastNonnegative hOrderTrigger).elim
    · exact hone
  have hTargetLast : b.order targetLast = 0 := by
    rw [hSourceNext] at hOrderTrigger
    omega
  let targetParity := b.heHu2022Proposition27ii hBIntegral targetLast
    hTargetLastEven hTargetLast
  have hTargetOrdersEven (t : Nat) (ht : t < 2 * k + 3) :
      Even (b.orderSequence.entryOrZero t) := by
    let tFin : Fin (2 * k + 3) := ⟨t, ht⟩
    rw [b.orderSequence_entryOrZero_eq_order tFin]
    exact targetParity.precedingOrdersEven tFin
      (by
        apply Fin.mk_le_mk.mpr
        change t ≤ 2 * k + 2
        omega)
  have hTargetPrefixEven :
      Even (b.orderSequence.prefixSum (2 * k + 3)) :=
    b.orderSequence.prefixSum_even_of_entries_even (2 * k + 3)
      hTargetOrdersEven
  have hSourceOrdersEven (t : Nat) (ht : t < 2 * k + 4) :
      Even (a.orderSequence.entryOrZero t) := by
    let tFin : Fin (m + 3) := ⟨t, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order tFin]
    by_cases htBoundary : t = 2 * k + 3
    · have hindex : tFin = ⟨2 * k + 3, by omega⟩ := by
        apply Fin.ext
        exact htBoundary
      rw [hindex, hSourceBoundary]
      exact ⟨-(ramificationIndex K : Int), by ring⟩
    · have htInitial : t < 2 * k + 3 := by omega
      rcases Nat.even_or_odd t with htEven | htOdd
      · have horder := hI1.oddOrder ⟨t, htInitial⟩ htEven.add_one
        have hindex : tFin = ⟨t, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hindex, horder]
        exact Even.zero
      · have htEvenDomain : t < 2 * k + 2 := by
          rcases htOdd with ⟨d, hd⟩
          omega
        have horder := hI1.evenOrder ⟨t, htEvenDomain⟩ htOdd.add_one
        have hindex : tFin = ⟨t, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hindex, horder]
        exact ⟨-(ramificationIndex K : Int), by ring⟩
  have hSourcePrefixEven :
      Even (a.orderSequence.prefixSum (2 * k + 4)) :=
    a.orderSequence.prefixSum_even_of_entries_even (2 * k + 4)
      hSourceOrdersEven
  have hSourcePrefixOdd :
      Odd (a.orderSequence.prefixSum (2 * k + 5)) := by
    rw [a.orderSequence.prefixSum_succ]
    have hentry : a.orderSequence.entryOrZero (2 * k + 4) = 1 := by
      rw [a.orderSequence_entryOrZero_eq_order
        (⟨2 * k + 4, by omega⟩ : Fin (m + 3)), hSourceNext]
    rw [hentry]
    exact hSourcePrefixEven.add_odd (by norm_num)
  have hMixedOdd : Odd (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
        b.prefixProduct (2 * k + 3))) := by
    rw [ordUnit_mul, ordUnit_mul, ordUnit_neg_one_eq_zero,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 5) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) le_rfl]
    exact (Even.zero.add_odd hSourcePrefixOdd).add_even hTargetPrefixEven
  have hCurrentZero : a.centralCurrentDefect b i = 0 := by
    have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
      (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
      b (-1) (2 * k + 5) (2 * k + 3) hMixedOdd
    unfold centralCurrentDefect
    rw [hi]
    convert hzero using 1 <;> congr 1 <;> omega
  have hPreviousStrict :
      (((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) :
          WithTop ℚ) < a.centralPreviousDefect b i := by
    have h := htrigger.2
    rw [hTargetIndex, hSourceIndex, hTargetLast, hSourceNext,
      hCurrentZero, add_zero] at h
    convert h using 1 <;> norm_cast <;> ring
  let targetGap : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  have hPreviousCap : a.centralPreviousDefect b i ≤
      (b.alphaValue targetGap : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      i.val (i.val - 2)
    unfold centralPreviousDefect
    rw [hi] at hcap ⊢
    have hsub : 2 * k + 4 - 2 = 2 * k + 2 := by omega
    rw [hsub] at hcap ⊢
    rw [b.prefixAlphaCap_of_internal (i := 2 * k + 2)
      (by omega) (by omega)] at hcap
    have hgapIndex :
        (⟨2 * k + 2 - 1, by omega⟩ : Fin (2 * k + 2)) = targetGap := by
      apply Fin.ext
      simp only [targetGap]
      omega
    rw [hgapIndex] at hcap
    exact hcap
  have hTargetAlphaStrict :
      2 * (ramificationIndex K : ℚ) - 1 <
        b.alphaValue targetGap := by
    exact_mod_cast hPreviousStrict.trans_le hPreviousCap
  have hTargetAlphaLower :
      2 * (ramificationIndex K : ℚ) ≤ b.alphaValue targetGap :=
    by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      letI : Beli2009AlphaParityLaws.{u, w} K :=
        beliUniversalAlphaParityLaws
      exact b.alphaValue_ge_twoE_of_gt_twoE_sub_one targetGap
        hTargetAlphaStrict
  have hTargetGapLower : 2 * (ramificationIndex K : Int) ≤
      b.orderGap targetGap :=
    by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      letI : Beli2009AlphaParityLaws.{u, w} K :=
        beliUniversalAlphaParityLaws
      exact b.orderGap_ge_twoE_of_alphaValue_ge_twoE_early targetGap
        hTargetAlphaLower
  have hTargetPreviousLower :
      -(2 * (ramificationIndex K : Int)) ≤
        b.order ⟨2 * k + 1, by omega⟩ := by
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    exact ((b.heHu2022Proposition27i hBIntegral).evenIndexed
      ⟨2 * k + 1, by omega⟩ ⟨2 * k + 1, by omega⟩
        le_rfl hodd hodd).1
  have hTargetPrevious : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    unfold orderGap at hTargetGapLower
    have hleft : targetGap.castSucc =
        (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 3)) := by
      apply Fin.ext
      rfl
    have hright : targetGap.succ = targetLast := by
      apply Fin.ext
      rfl
    rw [hleft, hright, hTargetLast] at hTargetGapLower
    omega
  have hSourceFirst : a.order 0 = 0 := by
    have h := hI1.oddOrder (⟨0, by omega⟩ : Fin (2 * k + 3))
      (by norm_num)
    convert h using 1
    congr 1
  rcases a.heHuLemma45_sourcePrefix_evenFirst sourceLaws (by omega)
      hSourceFirst hSourceBoundary with ⟨mu, hmu, hSourceModel⟩
  rcases b.heHuLemma510_target_represents_oddFirst hBIntegral
      hTargetPrevious (by simpa only [targetLast] using hTargetLast) with
    ⟨epsilon, hepsilon, hTargetModel⟩
  have hModel := heHu2022Lemma314ii (K := K) k mu epsilon hmu hepsilon
  have hrep := hTargetModel.trans hModel |>.trans hSourceModel
  exact prefixRepresents_cast b a (by omega) (by omega) hrep

/-- In the terminal `alpha_n=1` branch, Lemma 2.11 and the two terms of the
central trigger first force the current defect to be positive.  The `I2^O`
bound and equation (5.1) then force the last source gap to be odd, whereas
the same positivity forces the corresponding mixed product to have even
order.  Adding the odd source pair makes the current mixed product odd, a
contradiction.  This is Case II in the reverse implication of Lemma 5.10. -/
theorem heHuLemma510_alphaOne_terminalTrigger_false
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * k + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI2O (2 * k + 3) (by omega) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (i : CentralRepresentationIndex (m + 3) (2 * k + 3))
    (hi : i.val = 2 * k + 4)
    (htrigger : a.centralDefectTrigger b i) : False := by
  have hRBefore : a.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    have h := hI1.evenOrder
      (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 2)) (by
        change Even (2 * k + 2)
        exact ⟨k + 1, by omega⟩)
    exact h
  have hRAt : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    have h := hI1.oddOrder
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)) (by
        change Odd (2 * k + 3)
        exact ⟨k + 1, by omega⟩)
    exact h
  have hGapUpper :
      a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ ≤
        2 * (ramificationIndex K : Int) - 1 :=
    a.heHu2022Lemma54ii_gap (n := 2 * k + 3) (by omega)
      ⟨k + 1, by omega⟩ (by omega) hI1 hOdd hAlpha
  have hLocalRaw := a.heHu2022Lemma54ii_defect
    (n := 2 * k + 3) (by omega) ⟨k + 1, by omega⟩ (by omega)
      hAIntegral hI1 hOdd hAlpha
  have hLocal :
      a.truncatedPrefixDefect a (-1) (2 * k + 2) (2 * k + 4) =
        ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    unfold heHuAdjacentCappedDefect at hLocalRaw
    convert hLocalRaw using 1 <;> norm_cast <;> omega
  have h211 := a.heHu2022Lemma211LongSource k b (by omega)
    hAIntegral hBIntegral hRBefore hRAt hAlpha hLocal
  have hCommonCap :
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) ≤
        (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b 1
      (2 * k + 3) (2 * k + 3)
    rw [a.prefixAlphaCap_of_internal (i := 2 * k + 3)
      (by omega) (by omega)] at hcap
    have hindex :
        (⟨2 * k + 3 - 1, by omega⟩ : Fin (m + 2)) =
          ⟨2 * k + 2, by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hindex, hAlpha] at hcap
    exact hcap
  let targetLast : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hTargetLastEven : Even targetLast.val := ⟨k + 1, by
    simp only [targetLast]
    omega⟩
  have hTargetLastNonnegative : 0 ≤ b.order targetLast :=
    ((b.heHu2022Proposition27i hBIntegral).oddIndexed
      targetLast targetLast le_rfl hTargetLastEven hTargetLastEven).1
  have hTargetIndex :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (2 * k + 3)) = targetLast := by
    apply Fin.ext
    simp only [targetLast]
    omega
  have hSourceIndex :
      (⟨i.val, by
        have := i.lt_large
        omega⟩ : Fin (m + 3)) =
          ⟨2 * k + 4, by omega⟩ := by
    apply Fin.ext
    exact hi
  have hOrderTrigger : b.order targetLast <
      a.order ⟨2 * k + 4, by omega⟩ := by
    have h := htrigger.1
    rw [hTargetIndex, hSourceIndex] at h
    exact h
  have hDefectTrigger :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order targetLast : ℚ) -
          (a.order ⟨2 * k + 4, by omega⟩ : ℚ) : ℚ) :
            WithTop ℚ)) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
    have h := htrigger.2
    rw [hTargetIndex, hSourceIndex] at h
    exact h
  have hDefectTriggerInt :
      ((((2 * (ramificationIndex K : Int) +
          b.order targetLast -
          a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
    convert hDefectTrigger using 1 <;> norm_cast <;> ring
  have h211Central :
      ((((a.order ⟨2 * k + 3, by omega⟩ -
          b.order targetLast : Int) : ℚ) : WithTop ℚ) +
        a.centralPreviousDefect b i ≤
          a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3)) := by
    unfold centralPreviousDefect
    rw [hi]
    convert h211 using 1 <;> congr 1 <;> omega
  have hCurrentNonnegative : (0 : WithTop ℚ) ≤
      a.centralCurrentDefect b i := by
    unfold centralCurrentDefect
    exact a.truncatedPrefixDefect_nonneg
      (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
      b (-1) (i.val + 1) (i.val - 1)
  have hCurrentPositive : (0 : WithTop ℚ) <
      a.centralCurrentDefect b i := by
    by_contra hnot
    have hCurrentZero : a.centralCurrentDefect b i = 0 :=
      le_antisymm (le_of_not_gt hnot) hCurrentNonnegative
    have hNumerical :
        (((2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ -
            a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) < 1 := by
      calc
        (((2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ -
            a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) =
            ((((a.order ⟨2 * k + 3, by omega⟩ -
                b.order targetLast : Int) : ℚ) : WithTop ℚ) +
              (((2 * (ramificationIndex K : Int) +
                b.order targetLast -
                a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
                  WithTop ℚ)) := by
                    norm_cast
                    ring
        _ < ((((a.order ⟨2 * k + 3, by omega⟩ -
                b.order targetLast : Int) : ℚ) : WithTop ℚ) +
              (a.centralPreviousDefect b i +
                a.centralCurrentDefect b i)) :=
          WithTop.add_lt_add_left (by simp) hDefectTriggerInt
        _ = (((((a.order ⟨2 * k + 3, by omega⟩ -
                b.order targetLast : Int) : ℚ) : WithTop ℚ) +
              a.centralPreviousDefect b i) +
                a.centralCurrentDefect b i) := by ac_rfl
        _ ≤ a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
              a.centralCurrentDefect b i := by
          gcongr
        _ = a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) := by
          rw [hCurrentZero, add_zero]
        _ ≤ 1 := hCommonCap
    have hNumericalInt :
        2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ -
            a.order ⟨2 * k + 4, by omega⟩ < 1 := by
      exact_mod_cast hNumerical
    omega
  let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
  have hBoundaryGap : a.orderGap boundary =
      a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap
    have hleft : boundary.castSucc =
        (⟨2 * k + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      rfl
    have hright : boundary.succ =
        (⟨2 * k + 3, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      rfl
    rw [hleft, hright, hRAt]
    simp
  have hSourceNextShape :
      a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
        (Even (a.order ⟨2 * k + 3, by omega⟩) ∧
          2 - 2 * (ramificationIndex K : Int) ≤
            a.order ⟨2 * k + 3, by omega⟩ ∧
          a.order ⟨2 * k + 3, by omega⟩ ≤ 0) := by
    have hshape := (a.heHu2022Proposition26 boundary).alphaOne
      (by simpa only [boundary] using hAlpha) |>.1
    rw [hBoundaryGap] at hshape
    exact hshape
  have hAlternative :
      a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
        1 < a.order ⟨2 * k + 4, by omega⟩ := by
    by_contra hnot
    have hRNextNot : a.order ⟨2 * k + 3, by omega⟩ ≠ 1 := by
      intro h
      exact hnot (Or.inl h)
    have hRLastNot : ¬ 1 < a.order ⟨2 * k + 4, by omega⟩ := by
      intro h
      exact hnot (Or.inr h)
    have hRNextEven : Even (a.order ⟨2 * k + 3, by omega⟩) :=
      (hSourceNextShape.resolve_left hRNextNot).1
    have hRLast : a.order ⟨2 * k + 4, by omega⟩ = 1 := by
      have hpositive : 0 < a.order ⟨2 * k + 4, by omega⟩ :=
        lt_of_le_of_lt hTargetLastNonnegative hOrderTrigger
      omega
    have hTargetLast : b.order targetLast = 0 := by
      rw [hRLast] at hOrderTrigger
      omega
    have hSourceInitialOrdersEven (t : Nat) (ht : t < 2 * k + 3) :
        Even (a.orderSequence.entryOrZero t) := by
      let tFin : Fin (m + 3) := ⟨t, by omega⟩
      rw [a.orderSequence_entryOrZero_eq_order tFin]
      rcases Nat.even_or_odd t with htEven | htOdd
      · have horder := hI1.oddOrder ⟨t, ht⟩ htEven.add_one
        have hindex : tFin = ⟨t, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hindex, horder]
        exact Even.zero
      · have htEvenDomain : t < 2 * k + 2 := by
          rcases htOdd with ⟨d, hd⟩
          omega
        have horder := hI1.evenOrder ⟨t, htEvenDomain⟩ htOdd.add_one
        have hindex : tFin = ⟨t, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hindex, horder]
        exact ⟨-(ramificationIndex K : Int), by ring⟩
    have hSourceInitialPrefixEven :
        Even (a.orderSequence.prefixSum (2 * k + 3)) :=
      a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3)
        hSourceInitialOrdersEven
    have hSourceThroughNextEven :
        Even (a.orderSequence.prefixSum (2 * k + 4)) := by
      rw [a.orderSequence.prefixSum_succ,
        a.orderSequence_entryOrZero_eq_order
          (⟨2 * k + 3, by omega⟩ : Fin (m + 3))]
      exact hSourceInitialPrefixEven.add hRNextEven
    have hSourceExtendedOdd :
        Odd (a.orderSequence.prefixSum (2 * k + 5)) := by
      rw [a.orderSequence.prefixSum_succ,
        a.orderSequence_entryOrZero_eq_order
          (⟨2 * k + 4, by omega⟩ : Fin (m + 3)), hRLast]
      exact hSourceThroughNextEven.add_odd odd_one
    let targetParity := b.heHu2022Proposition27ii hBIntegral targetLast
      hTargetLastEven hTargetLast
    have hTargetOrdersEven (t : Nat) (ht : t < 2 * k + 3) :
        Even (b.orderSequence.entryOrZero t) := by
      let tFin : Fin (2 * k + 3) := ⟨t, ht⟩
      rw [b.orderSequence_entryOrZero_eq_order tFin]
      exact targetParity.precedingOrdersEven tFin (by
        apply Fin.mk_le_mk.mpr
        change t ≤ 2 * k + 2
        omega)
    have hTargetPrefixEven :
        Even (b.orderSequence.prefixSum (2 * k + 3)) :=
      b.orderSequence.prefixSum_even_of_entries_even (2 * k + 3)
        hTargetOrdersEven
    have hMixedOdd : Odd (ordUnit K
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          b.prefixProduct (2 * k + 3))) := by
      rw [ordUnit_mul, ordUnit_mul, ordUnit_neg_one_eq_zero,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * k + 5) (by omega),
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * k + 3) le_rfl]
      exact (Even.zero.add_odd hSourceExtendedOdd).add_even hTargetPrefixEven
    have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
      (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
      b (-1) (2 * k + 5) (2 * k + 3) hMixedOdd
    have hCurrentZero : a.centralCurrentDefect b i = 0 := by
      unfold centralCurrentDefect
      rw [hi]
      convert hzero using 1 <;> congr 1 <;> omega
    rw [hCurrentZero] at hCurrentPositive
    exact (lt_irrefl 0 hCurrentPositive).elim
  have hAlphaNext := hOdd.2 hAlpha hAlternative
  have hCurrentCap : a.centralCurrentDefect b i ≤
      (a.alphaValue ⟨2 * k + 4, by omega⟩ : WithTop ℚ) := by
    have hcap := a.centralCurrentDefect_le_leftCap b i
    rw [hi] at hcap
    rw [a.prefixAlphaCap_of_internal (i := 2 * k + 5)
      (by omega) (by omega)] at hcap
    have hindex :
        (⟨2 * k + 5 - 1, by omega⟩ : Fin (m + 2)) =
          ⟨2 * k + 4, by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hindex] at hcap
    exact hcap
  have hCurrentThreshold : a.centralCurrentDefect b i ≤
      (((a.heHuOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
        WithTop ℚ) :=
    hCurrentCap.trans (by exact_mod_cast hAlphaNext)
  have hThreshold :
      (((2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) <
        a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
          (((a.heHuOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
            WithTop ℚ) := by
    calc
      (((2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
          ((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            (((2 * (ramificationIndex K : Int) +
              b.order targetLast -
              a.order ⟨2 * k + 4, by omega⟩ : Int) : ℚ) :
                WithTop ℚ)) := by
                  norm_cast
                  ring
      _ < ((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            (a.centralPreviousDefect b i +
              a.centralCurrentDefect b i)) :=
        WithTop.add_lt_add_left (by simp) hDefectTriggerInt
      _ = (((((a.order ⟨2 * k + 3, by omega⟩ -
              b.order targetLast : Int) : ℚ) : WithTop ℚ) +
            a.centralPreviousDefect b i) +
              a.centralCurrentDefect b i) := by ac_rfl
      _ ≤ a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            a.centralCurrentDefect b i := by
        gcongr
      _ ≤ a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            (((a.heHuOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) := by
        gcongr
  let sourceGap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hGapNotEven : ¬ Even sourceGap := by
    intro hEven
    have hThresholdFormula : a.heHuOddThreshold (2 * k + 3) (by omega) =
        2 * (ramificationIndex K : Int) -
          a.order ⟨2 * k + 4, by omega⟩ +
          a.order ⟨2 * k + 3, by omega⟩ - 1 := by
      simp only [heHuOddThreshold, sourceGap, hEven, if_pos]
    have hCommonShift :
        a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) +
            (((a.heHuOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) ≤
          (1 : WithTop ℚ) +
            (((a.heHuOddThreshold (2 * k + 3) (by omega) : Int) : ℚ) :
              WithTop ℚ) := by
      gcongr
    have hcontr := hThreshold.trans_le hCommonShift
    rw [hThresholdFormula] at hcontr
    have heq :
        (1 : WithTop ℚ) +
            ((((2 * (ramificationIndex K : Int) -
              a.order ⟨2 * k + 4, by omega⟩ +
              a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
                WithTop ℚ)) =
          (((2 * (ramificationIndex K : Int) -
            a.order ⟨2 * k + 4, by omega⟩ +
            a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) := by
      norm_cast
      ring
    rw [heq] at hcontr
    exact (lt_irrefl _ hcontr)
  have hGapOdd : Odd sourceGap :=
    (Int.even_or_odd sourceGap).resolve_left hGapNotEven
  have hThresholdFormula : a.heHuOddThreshold (2 * k + 3) (by omega) =
      2 * (ramificationIndex K : Int) -
        a.order ⟨2 * k + 4, by omega⟩ +
        a.order ⟨2 * k + 3, by omega⟩ := by
    simp [heHuOddThreshold, sourceGap, hGapNotEven]
  have hCommonNonnegative : (0 : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) :=
    a.truncatedPrefixDefect_nonneg
      (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
      b 1 (2 * k + 3) (2 * k + 3)
  have hCommonPositive : (0 : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 (2 * k + 3) (2 * k + 3) := by
    by_contra hnot
    have hzero : a.truncatedPrefixDefect b 1 (2 * k + 3)
        (2 * k + 3) = 0 :=
      le_antisymm (le_of_not_gt hnot) hCommonNonnegative
    rw [hzero, zero_add, hThresholdFormula] at hThreshold
    exact (lt_irrefl _ hThreshold).elim
  have hCommonOrderEven : Even (ordUnit K
      (a.prefixProduct (2 * k + 3) *
        b.prefixProduct (2 * k + 3))) := by
    rcases Int.even_or_odd (ordUnit K
      (a.prefixProduct (2 * k + 3) *
        b.prefixProduct (2 * k + 3))) with hEven | hOddOrder
    · exact hEven
    · have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
        (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
        b 1 (2 * k + 3) (2 * k + 3) (by
          simpa only [one_mul] using hOddOrder)
      rw [hzero] at hCommonPositive
      exact (lt_irrefl 0 hCommonPositive).elim
  have hCommonSumEven : Even
      (a.orderSequence.prefixSum (2 * k + 3) +
        b.orderSequence.prefixSum (2 * k + 3)) := by
    rw [ordUnit_mul,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) le_rfl] at hCommonOrderEven
    exact hCommonOrderEven
  have hSourcePairOdd : Odd
      (a.order ⟨2 * k + 3, by omega⟩ +
        a.order ⟨2 * k + 4, by omega⟩) := by
    rcases hGapOdd with ⟨z, hz⟩
    refine ⟨z + a.order ⟨2 * k + 3, by omega⟩, ?_⟩
    simp only [sourceGap] at hz
    omega
  have hSourceExtended :
      a.orderSequence.prefixSum (2 * k + 5) =
        a.orderSequence.prefixSum (2 * k + 3) +
          a.order ⟨2 * k + 3, by omega⟩ +
          a.order ⟨2 * k + 4, by omega⟩ := by
    rw [a.orderSequence.prefixSum_succ,
      a.orderSequence.prefixSum_succ,
      a.orderSequence_entryOrZero_eq_order
        (⟨2 * k + 3, by omega⟩ : Fin (m + 3)),
      a.orderSequence_entryOrZero_eq_order
        (⟨2 * k + 4, by omega⟩ : Fin (m + 3))]
  have hMixedOdd : Odd (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
        b.prefixProduct (2 * k + 3))) := by
    rw [ordUnit_mul, ordUnit_mul, ordUnit_neg_one_eq_zero,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 5) (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (2 * k + 3) le_rfl, hSourceExtended]
    have hOddSum := hCommonSumEven.add_odd hSourcePairOdd
    convert Even.zero.add_odd hOddSum using 1 <;> ring
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
    (alphaV := sourceLaws) (alphaW := beliUniversalAlphaLaws)
    b (-1) (2 * k + 5) (2 * k + 3) hMixedOdd
  have hCurrentZero : a.centralCurrentDefect b i = 0 := by
    unfold centralCurrentDefect
    rw [hi]
    convert hzero using 1 <;> congr 1 <;> omega
  rw [hCurrentZero] at hCurrentPositive
  exact (lt_irrefl 0 hCurrentPositive).elim

/-- Lemma 5.10, implication `(i) -> (ii)`: the universal condition (iii)
specializes to the two first-column tests and, in the exceptional ternary
case, to one second-column test. -/
theorem heHu2022Lemma510Universal_to_tests
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hAll : HeHuAllCentralRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a) :
    a.HeHuLemma510TestConditions k hm := by
  constructor
  · intro hAlpha hTrigger
    have h58 := a.heHu2022Lemma58 (n := 2 * k + 1) (by omega)
      ⟨k + 1, by omega⟩ hm hAIntegral hI1 hI2 hAlpha hTrigger
    have h58' :
        ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
          defectOrder (K := K) (heHuLemma59CTilde a k) =
              ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
                WithTop ℚ) ∧
            IsValuationUnit K
              (heHuSharp (heHuLemma59CTilde a k) hc : K) ∧
            defectOrder (K := K)
                (heHuSharp (heHuLemma59CTilde a k) hc) =
              (((2 * (ramificationIndex K : Int) +
                  a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
                WithTop ℚ) := by
      simpa only [heHuLemma59CTilde_eq_lemma58Prefix] using h58
    rcases h58' with ⟨hc, _hraw, _hunit, _hsharp⟩
    refine ⟨hc, ?_, ?_⟩
    · exact hAll (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
        (heHuLemma59Target_integral (K := K) (heHuLemma59C a k) k)
    · exact hAll
        (heHuLemma59Target (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k)
        (heHuLemma59Target_integral (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k)
  · intro hk _hAlpha _hR5 _hprefix
    subst k
    let delta : Kˣ := 1
    have hdelta : IsValuationUnit K (delta : K) := by
      simp [delta, IsValuationUnit]
    refine ⟨delta, hdelta, ?_⟩
    apply hAll (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
    apply heHuIntegral_of_firstOrder_nonneg
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
    rw [heHuLemma311OddSecondUnitUniformizerTail_order]
    norm_num

/-- Lemma 5.10, implication `(ii) -> (iii)`.  The `alpha_N=0` branch uses
`I3^E(N-1)` except in the published ternary square-prefix exception, where
Lemma 5.7 rules out the existential second-column test.  The `alpha_N=1`
branch is exactly the simultaneous two-test obstruction of Lemma 5.9. -/
theorem heHu2022Lemma510Tests_to_i2O
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hTests : a.HeHuLemma510TestConditions k hm) :
    a.HeHuI2O (2 * k + 3) (by omega) (by omega) := by
  constructor
  · intro hAlpha
    have hBoundary := a.heHu2022Lemma54i (n := 2 * k + 3) (by omega)
      ⟨k + 1, by omega⟩ (by omega) hI1 hAlpha
    have hNextNonnegative : 0 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
      let C := a.heHu2022Proposition27i hAIntegral
      have hEven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
      exact (C.oddIndexed ⟨2 * k + 4, by omega⟩
        ⟨2 * k + 4, by omega⟩ le_rfl hEven hEven).1
    by_cases hZero : a.order ⟨2 * k + 4, by omega⟩ = 0
    · exact Or.inl hZero
    by_cases hOne : a.order ⟨2 * k + 4, by omega⟩ = 1
    · exact Or.inr hOne
    exfalso
    have hGreater : 1 < a.order ⟨2 * k + 4, by omega⟩ := by omega
    have hLargeGap : 2 * (ramificationIndex K : Int) <
        a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ := by
      rw [hBoundary]
      omega
    have hI3Conclusion := hI3 (by omega) hLargeGap
    by_cases hkZero : k = 0
    · subst k
      have hR4 : a.order ⟨3, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
        simpa only using hBoundary
      by_cases hDefectEq : a.heHuPrefixDefect 4 =
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ)
      · have hforced := hI3Conclusion.2 (Or.inr ⟨by omega, hDefectEq⟩)
        exact (ne_of_gt hGreater) hforced
      · let j : Fin (m + 3) := ⟨3, by omega⟩
        have hjOdd : Odd j.val := ⟨1, by norm_num [j]⟩
        let C := a.heHu2022Proposition27iiiiv hAIntegral j hjOdd (by
          simpa only [j] using hR4)
        have hTruncated :
            (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) ≤
              a.truncatedPrefixDefect a (1 : Kˣ) 0 4 := by
          simpa [j] using C.alternatingPrefixDefect
        have hRaw := hTruncated.trans
          (a.truncatedPrefixDefect_le_defect a (1 : Kˣ) 0 4)
        have hPrefixLower :
            (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) ≤
              a.heHuPrefixDefect 4 := by
          simpa [heHuPrefixDefect, GoodBONG.prefixProduct] using hRaw
        have hPrefixStrict :
            (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) <
              a.heHuPrefixDefect 4 := by
          have hne : a.heHuPrefixDefect 4 ≠
              (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) := by
            exact_mod_cast hDefectEq
          exact lt_of_le_of_ne hPrefixLower hne.symm
        have hPrefixSquare : IsSquare (a.prefixProduct 4) := by
          apply isSquare_of_two_mul_e_lt_defectOrder
          have hStrictNat :
              ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) <
                a.heHuPrefixDefect 4 := by
            convert hPrefixStrict using 1 <;> norm_num
          simpa only [heHuPrefixDefect] using hStrictNat
        have hPrefixTop : defectOrder (K := K) (a.prefixProduct 4) = ⊤ :=
          defectOrder_eq_top_of_isSquare (K := K) hPrefixSquare
        rcases hTests.2 rfl hAlpha (by omega)
            hPrefixTop with ⟨delta, hdelta, hCentral⟩
        let b := heHuLemma311OddSecondUnitUniformizerTail delta hdelta
        have hBIntegral := heHuLemma510ExceptionalTarget_integral
          (K := K) delta hdelta
        unfold UnderlyingLatticeIsIntegral at hBIntegral
        let targetLaws : Beli2006AlphaLaws.{u, u} K :=
          beliUniversalAlphaLaws
        have hPrime :=
          (a.heHuLemma510_original_iff_prime sourceLaws targetLaws b
            (by omega) hAIntegral hBIntegral hI1 hI2).mp (by
              simpa only [b] using hCentral)
        exact (a.heHu2022Lemma57_not_centralRepresentationConditionsPrime
          (sourceLaws := sourceLaws)
          (m := m + 1) (by omega) hAIntegral hI1 hR4 hGreater hPrefixTop
          delta hdelta) hPrime
    · have hFour : 4 ≤ 2 * k + 2 := by omega
      have hforced := hI3Conclusion.2 (Or.inl hFour)
      exact (ne_of_gt hGreater) hforced
  · intro hAlpha hTrigger
    by_contra hBound
    have hAlphaNext :
        (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) <
          a.alphaValue ⟨2 * k + 4, by omega⟩ := by
      exact lt_of_not_ge hBound
    rcases a.heHu2022Lemma59 k hm hAIntegral hI1 hI2 hI3 hAlphaNext
        hAlpha hTrigger with
      ⟨hc, _hFirstTrigger, _hSecondTrigger, _hNotBoth, hFailure⟩
    rcases hTests.1 hAlpha hTrigger with
      ⟨hcTests, hCentralFirst, hCentralSecond⟩
    have hcEq : hcTests = hc := Subsingleton.elim _ _
    subst hcTests
    let targetLaws : Beli2006AlphaLaws.{u, u} K :=
      beliUniversalAlphaLaws
    have hPrimeFirst :=
      (a.heHuLemma510_original_iff_prime sourceLaws targetLaws
        (heHuLemma59Target (K := K) (heHuLemma59C a k) k) hm
        hAIntegral
        (heHuLemma59Target_integral (K := K) (heHuLemma59C a k) k)
        hI1 hI2).mp hCentralFirst
    have hPrimeSecond :=
      (a.heHuLemma510_original_iff_prime sourceLaws targetLaws
        (heHuLemma59Target (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k)
        hm hAIntegral
        (heHuLemma59Target_integral (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k)
        hI1 hI2).mp hCentralSecond
    rcases hFailure with hNotFirst | hNotSecond
    · exact hNotFirst hPrimeFirst
    · exact hNotSecond hPrimeSecond

/-- Lemma 5.10, implication `(iii) -> (i)`: `I2^O(n)` supplies every
terminal revised central condition.  Nonterminal indices descend to the
even prefix and Lemma 4.4; the two terminal alpha cases are exactly the two
case lemmas above. -/
theorem heHu2022Lemma510I2O_to_universal
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI2O (2 * k + 3) (by omega) (by omega)) :
    HeHuAllCentralRepresentationConditions.{u, v, w}
      (n := 2 * k + 2) a := by
  intro W _ _ r M b hBIntegral
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    beliUniversalAlphaLaws
  apply (a.heHuLemma510_original_iff_prime sourceLaws targetLaws b hm
    hAIntegral hBIntegral hI1 hI2).mpr
  intro i htrigger
  by_cases hiNonterminal : i.val ≤ 2 * k + 3
  · exact a.heHuLemma510_nonterminal_representation
      (sourceLaws := sourceLaws) b hm hAIntegral
      hBIntegral hI1 hI2 i hiNonterminal htrigger
  · have hiTerminal : i.val = 2 * k + 4 := by
      have := i.le_small_succ
      omega
    have hI2Cases := hI2
    dsimp only [HeHuI2E] at hI2Cases
    rcases hI2Cases with hAlphaZero | ⟨hAlphaOne, _hAdjacent⟩
    · exact a.heHuLemma510_alphaZero_terminal_representation
        (sourceLaws := sourceLaws) b hm
        hAIntegral hBIntegral hI1 hOdd hAlphaZero i hiTerminal htrigger
    · exact (a.heHuLemma510_alphaOne_terminalTrigger_false
        (sourceLaws := sourceLaws) b hm
        hAIntegral hBIntegral hI1 hOdd hAlphaOne i hiTerminal htrigger).elim

/-- He--Hu, Lemma 5.10, complete equivalence of the universal form of
Theorem 2.8(iii), the finite list of published test lattices, and condition
`I2^O(n)`.  The ambient `n`-universality assumption is retained verbatim from
the published lemma even though the central-condition equivalence below uses
only its stated integral and BONG hypotheses. -/
theorem heHu2022Lemma510
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega)) :
    Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) →
      ((HeHuAllCentralRepresentationConditions.{u, v, u}
          (n := 2 * k + 2) a ↔
        a.HeHuLemma510TestConditions k hm) ∧
       (a.HeHuLemma510TestConditions k hm ↔
        a.HeHuI2O (2 * k + 3) (by omega) (by omega))) := by
  intro _hAmbient
  constructor
  · constructor
    · exact a.heHu2022Lemma510Universal_to_tests hm hAIntegral hI1 hI2
    · intro hTests
      have hOdd := a.heHu2022Lemma510Tests_to_i2O hm hAIntegral hI1 hI2 hI3
        hTests
      intro X _ _ s N b hB
      exact (a.heHu2022Lemma510I2O_to_universal
        (sourceLaws := sourceLaws) hm hAIntegral hI1 hI2 hOdd) b hB
  · constructor
    · exact a.heHu2022Lemma510Tests_to_i2O hm hAIntegral hI1 hI2 hI3
    · intro hOdd
      apply a.heHu2022Lemma510Universal_to_tests hm hAIntegral hI1 hI2
      intro X _ _ s N b hB
      exact (a.heHu2022Lemma510I2O_to_universal
        (sourceLaws := sourceLaws) hm hAIntegral hI1 hI2 hOdd) b hB

end BONG.GoodBONG

end Bong
