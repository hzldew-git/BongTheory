/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma38
import Bong.Bong.HeHu2022Lemma211Parity
import Bong.Bong.Beli2009AlphaLocalizationProof
import Bong.Bong.Beli2009JordanFundamentalWeight

/-!
# He (2024), Lemma 3.9

The paper's odd rank `n >= 3` is written as `2 * t + 3`.  Part (i) is the
published truncation argument: remove the last target coefficient, invoke
Lemma 3.8 at the resulting even rank, and transport the two capped defects
back to the original target.  Part (ii) is the terminal parity contradiction
through Lemma 3.7.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- He, Lemma 3.9(i), with an arbitrary source tail beyond `n + 1`.  The
prefix target used in the publisher proof is constructed from the first
`n - 1` BONG vectors, rather than postulated abstractly. -/
theorem he2022ClassicLemma39iLongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRnMinusOne : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : CentralRepresentationIndex (m + 4) (2 * t + 3) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  dsimp only
  let i : CentralRepresentationIndex (m + 4) (2 * t + 3) :=
    { val := 2 * t + 3
      one_lt := by omega
      lt_large := by omega
      le_small_succ := by omega }
  unfold HeClassicPublishedCentralConditionAt
  intro htrigger
  let s : AlphaLocalizationIndex (2 * t + 2) :=
    { start := 0
      pivot := 2 * t
      stop := 2 * t + 1
      start_le_pivot := by omega
      pivot_lt_stop := by omega
      stop_lt := by omega }
  let w : BONG.SegmentWitness b.toBONG s.start s.length s.bound :=
    b.toBONG.segmentWitness s.start s.length s.bound
  let bpRaw := w.toGoodBONG b.good
  have hAlphaLength : s.stop - s.start = 2 * t + 1 := by
    simp only [s]
    omega
  let bp := bpRaw.castLength (congrArg (fun z => z + 1) hAlphaLength)
  have hOrderEq (j : Fin (2 * t + 2)) :
      bp.order j = b.order ⟨j.val, by omega⟩ := by
    rw [show bp = bpRaw.castLength
      (congrArg (fun z => z + 1) hAlphaLength) by rfl,
      GoodBONG.order_castLength]
    change w.bong.order _ = b.order _
    rw [w.order_eq]
    congr 1
    apply Fin.ext
    simp only [BONG.SegmentWitness.sourceIndex_val, s]
    omega
  have hValueUnitEq (j : Fin (2 * t + 2)) :
      bp.valueUnit j = b.valueUnit ⟨j.val, by omega⟩ := by
    rw [show bp = bpRaw.castLength
      (congrArg (fun z => z + 1) hAlphaLength) by rfl,
      GoodBONG.valueUnit_castLength_fundamental]
    change w.bong.valueUnit _ = b.valueUnit _
    rw [w.valueUnit_eq]
    congr 1
    apply Fin.ext
    simp only [BONG.SegmentWitness.sourceIndex_val, s]
    omega
  have hValueEq (j : Fin (2 * t + 2)) :
      bp.value j = b.value ⟨j.val, by omega⟩ := by
    have h := congrArg (fun z : Kˣ => (z : K)) (hValueUnitEq j)
    exact h
  have hPrefixProduct (length : Nat) (hlength : length <= 2 * t + 2) :
      bp.prefixProduct length = b.prefixProduct length := by
    induction length with
    | zero => simp [GoodBONG.prefixProduct]
    | succ length ih =>
        have hlt : length < 2 * t + 2 := by omega
        unfold GoodBONG.prefixProduct at ih ⊢
        rw [bp.toBONG.prefixProduct_succ length hlt,
          b.toBONG.prefixProduct_succ length (by omega), ih (by omega)]
        exact congrArg (fun z => b.toBONG.prefixProduct length * z)
          (hValueUnitEq ⟨length, hlt⟩)
  have hAlphaLe :
      b.alphaValue ⟨2 * t, by omega⟩ <=
        bp.alphaValue ⟨2 * t, by omega⟩ := by
    have hloc := b.beli2009Lemma21_le_segmentAlpha s w
    rw [← b.coe_alphaValue, ← bpRaw.coe_alphaValue] at hloc
    have hlocQ := WithTop.coe_le_coe.mp hloc
    have hcast := GoodBONG.alphaValue_castLength_fundamental
      bpRaw hAlphaLength ⟨2 * t, by omega⟩
    have hglobal : s.pivotFin = (⟨2 * t, by omega⟩ : Fin (2 * t + 2)) := by
      apply Fin.ext
      rfl
    have hlocal : s.localPivot =
        Fin.cast hAlphaLength.symm
          (⟨2 * t, by omega⟩ : Fin (2 * t + 1)) := by
      apply Fin.ext
      simp only [s, AlphaLocalizationIndex.localPivot, Fin.val_cast]
      omega
    rw [hglobal, hlocal] at hlocQ
    rw [show bp = bpRaw.castLength
      (congrArg (fun z => z + 1) hAlphaLength) by rfl, hcast]
    exact hlocQ
  have hBPrefixClassic :
      Lattice.IsClassicIntegral
        (r.restrict w.carrier w.nondegenerate) w.lattice := by
    rw [bp.isClassicIntegral_iff_firstOrders]
    have hfull := (b.isClassicIntegral_iff_firstOrders).1 hBClassic
    constructor
    · rw [hOrderEq]
      exact hfull.1
    · rw [hOrderEq, hOrderEq]
      exact hfull.2
  let ip : CentralRepresentationIndex (m + 4) (2 * t + 2) :=
    { val := 2 * t + 3
      one_lt := by omega
      lt_large := by omega
      le_small_succ := by omega }
  have hPreviousCap : b.prefixAlphaCap (2 * t + 1) <=
      bp.prefixAlphaCap (2 * t + 1) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega),
      bp.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast hAlphaLe
  have hCurrentCap : b.prefixAlphaCap (2 * t + 2) <=
      bp.prefixAlphaCap (2 * t + 2) := by
    rw [bp.prefixAlphaCap_last]
    exact le_top
  have hPreviousLe :
      a.truncatedPrefixDefect b (-1) (2 * t + 3) (2 * t + 1) <=
        a.truncatedPrefixDefect bp (-1) (2 * t + 3)
          (2 * t + 1) := by
    unfold truncatedPrefixDefect
    rw [hPrefixProduct (2 * t + 1) (by omega)]
    exact min_le_min le_rfl (min_le_min le_rfl hPreviousCap)
  have hCurrentLe :
      a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
        a.truncatedPrefixDefect bp (-1) (2 * t + 4)
          (2 * t + 2) := by
    unfold truncatedPrefixDefect
    rw [hPrefixProduct (2 * t + 2) le_rfl]
    exact min_le_min le_rfl (min_le_min le_rfl hCurrentCap)
  have hPrefixTrigger : a.centralDefectTrigger bp ip := by
    constructor
    · have hraw := htrigger.1
      change b.order ⟨2 * t + 1, by omega⟩ <
        a.order ⟨2 * t + 3, by omega⟩ at hraw
      change bp.order ⟨2 * t + 1, by omega⟩ <
        a.order ⟨2 * t + 3, by omega⟩
      rw [hOrderEq]
      exact hraw
    · have hraw := htrigger.2
      have hsum := hraw.trans_le (add_le_add hPreviousLe hCurrentLe)
      unfold centralPreviousDefect centralCurrentDefect
      rw [hOrderEq]
      convert hsum using 1
      all_goals
        simp only [ip]
        congr 2
  have hPrefixCondition := a.he2022ClassicLemma38LongSource t bp hm
    hAClassic hBPrefixClassic hRnMinusOne hRn hAlpha hSourceEquality
  have hrep := hPrefixCondition hPrefixTrigger
  have hTargetValues :
      bp.prefixValues (2 * t + 2) (by omega) =
        b.prefixValues (2 * t + 2) (by omega) := by
    funext j
    unfold prefixValues
    simpa using hValueEq j
  change DiagonalRepresents
    (bp.prefixValues (2 * t + 2) (by omega))
    (a.prefixValues (2 * t + 3) (by omega)) at hrep
  rw [hTargetValues] at hrep
  exact hrep

/-- Exact-rank specialization of He, Lemma 3.9(i). -/
theorem he2022ClassicLemma39i (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRnMinusOne : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : CentralRepresentationIndex (2 * t + 4) (2 * t + 3) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  exact a.he2022ClassicLemma39iLongSource (m := 2 * t) t b (by omega)
    hAClassic hBClassic hRnMinusOne hRn hAlpha hSourceEquality

/-- He, Lemma 3.9(ii), with an arbitrary source tail beyond `n + 2`. -/
theorem he2022ClassicLemma39iiLongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 5 <= m + 5)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRnMinusOne : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (hRnOne : a.order ⟨2 * t + 3, by omega⟩ = 0)
    (hRnTwo : a.order ⟨2 * t + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * t + 4, by omega⟩ = 1) :
    let i : CentralRepresentationIndex (m + 5) (2 * t + 3) :=
      { val := 2 * t + 4
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  dsimp only
  let i : CentralRepresentationIndex (m + 5) (2 * t + 3) :=
    { val := 2 * t + 4
      one_lt := by omega
      lt_large := by omega
      le_small_succ := by omega }
  unfold HeClassicPublishedCentralConditionAt
  intro htrigger
  exfalso
  let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  let sourceLast : Fin (m + 5) := ⟨2 * t + 4, by omega⟩
  have hTargetNonnegative : 0 <= b.order targetLast := by
    have hparity : Even targetLast.val := by
      refine ⟨t + 1, ?_⟩
      simp only [targetLast]
      omega
    exact ((b.he2022ClassicProposition24 hBClassic).oddIndexed
      targetLast targetLast le_rfl hparity hparity).1
  have hOrderTrigger : b.order targetLast < a.order sourceLast := by
    have hraw := htrigger.1
    have htarget :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * t + 3)) = targetLast := by
      apply Fin.ext
      change 2 * t + 4 - 2 = 2 * t + 2
      omega
    have hsource :
        (⟨i.val, i.lt_large⟩ : Fin (m + 5)) = sourceLast := by
      apply Fin.ext
      rfl
    rw [htarget, hsource] at hraw
    exact hraw
  rcases hRnTwo with hSourceLastZero | hSourceLastOne
  · rw [hSourceLastZero] at hOrderTrigger
    omega
  · have hTargetLastZero : b.order targetLast = 0 := by
      rw [hSourceLastOne] at hOrderTrigger
      omega
    let sourceParityIndex : Fin (m + 5) := ⟨2 * t + 2, by omega⟩
    have hSourceIndexEven : Even sourceParityIndex.val := by
      refine ⟨t + 1, ?_⟩
      simp only [sourceParityIndex]
      omega
    have hSourceParity :=
      (a.he2022ClassicProposition24 hAClassic).zeroAtPaperOdd
        sourceParityIndex hSourceIndexEven (by
          simpa only [sourceParityIndex] using hRn)
    have hSourceInitialOrdersEven (k : Nat) (hk : k < 2 * t + 3) :
        Even (a.orderSequence.entryOrZero k) := by
      let kFin : Fin (m + 5) := ⟨k, by omega⟩
      rw [a.orderSequence_entryOrZero_eq_order kFin]
      exact hSourceParity.2 kFin (by
        apply Fin.mk_le_mk.mpr
        omega)
    have hSourceInitialPrefixEven :
        Even (a.orderSequence.prefixSum (2 * t + 3)) :=
      a.orderSequence.prefixSum_even_of_entries_even (2 * t + 3)
        hSourceInitialOrdersEven
    have hSourceThroughNextEven :
        Even (a.orderSequence.prefixSum (2 * t + 4)) := by
      rw [a.orderSequence.prefixSum_succ,
        a.orderSequence_entryOrZero_eq_order
          (⟨2 * t + 3, by omega⟩ : Fin (m + 5)), hRnOne]
      exact hSourceInitialPrefixEven.add Even.zero
    have hSourceExtendedOdd :
        Odd (a.orderSequence.prefixSum (2 * t + 5)) := by
      rw [a.orderSequence.prefixSum_succ,
        a.orderSequence_entryOrZero_eq_order sourceLast,
        hSourceLastOne]
      exact hSourceThroughNextEven.add_odd odd_one
    have hTargetIndexEven : Even targetLast.val := by
      refine ⟨t + 1, ?_⟩
      simp only [targetLast]
      omega
    have hTargetParity :=
      (b.he2022ClassicProposition24 hBClassic).zeroAtPaperOdd
        targetLast hTargetIndexEven hTargetLastZero
    have hTargetOrdersEven (k : Nat) (hk : k < 2 * t + 3) :
        Even (b.orderSequence.entryOrZero k) := by
      let kFin : Fin (2 * t + 3) := ⟨k, hk⟩
      rw [b.orderSequence_entryOrZero_eq_order kFin]
      exact hTargetParity.2 kFin (by
        apply Fin.mk_le_mk.mpr
        omega)
    have hTargetPrefixEven :
        Even (b.orderSequence.prefixSum (2 * t + 3)) :=
      b.orderSequence.prefixSum_even_of_entries_even (2 * t + 3)
        hTargetOrdersEven
    have hNegOneOrder : ordUnit K (-1 : Kˣ) = 0 := by
      rw [ordUnit_neg]
      have hone := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at hone
      omega
    have hMixedOdd : Odd (ordUnit K
        ((-1 : Kˣ) * a.prefixProduct (2 * t + 5) *
          b.prefixProduct (2 * t + 3))) := by
      rw [ordUnit_mul, ordUnit_mul, hNegOneOrder,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * t + 5) (by omega),
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * t + 3) le_rfl]
      exact (Even.zero.add_odd hSourceExtendedOdd).add_even hTargetPrefixEven
    have hNextMixedZero :
        a.truncatedPrefixDefect b (-1) (2 * t + 5) (2 * t + 3) = 0 :=
      a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws)
        b (-1) (2 * t + 5) (2 * t + 3) hMixedOdd
    have hLarge :
        ((((2 * (ramificationIndex K : Int) + b.order targetLast -
          a.order sourceLast : Int) : ℚ) : WithTop ℚ)) <
          a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) +
            a.truncatedPrefixDefect b (-1) (2 * t + 5)
              (2 * t + 3) := by
      have hraw := htrigger.2
      norm_cast at hraw ⊢
    have hGap := a.he2022ClassicLemma37GapLongSource
      (m := m + 1) t b (by omega) hAClassic hBClassic
        hRnMinusOne hRn hAlpha hSourceEquality hNextMixedZero hLarge
    rw [hSourceLastOne, hRnOne] at hGap
    have hePositive := ramificationIndex_pos (K := K)
    omega

/-- Exact-rank specialization of He, Lemma 3.9(ii). -/
theorem he2022ClassicLemma39ii (t : Nat)
    (a : GoodBONG q L (2 * t + 5))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRnMinusOne : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRn : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (hRnOne : a.order ⟨2 * t + 3, by omega⟩ = 0)
    (hRnTwo : a.order ⟨2 * t + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * t + 4, by omega⟩ = 1) :
    let i : CentralRepresentationIndex (2 * t + 5) (2 * t + 3) :=
      { val := 2 * t + 4
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  exact a.he2022ClassicLemma39iiLongSource (m := 2 * t) t b (by omega)
    hAClassic hBClassic hRnMinusOne hRn hAlpha hSourceEquality hRnOne hRnTwo

end BONG.GoodBONG

end Bong
