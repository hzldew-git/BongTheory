/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma510
import Bong.Bong.HeHu2022Lemma45
import Bong.Bong.HeHu2022Lemma313
import Bong.Dyadic.UnitDefectClassification

/-!
# He--Hu 2022, Lemma 5.11

This file formalizes the three equivalent long-representation assertions in
Lemma 5.11 of the published paper.  For odd paper rank `N = 2*k+3`, the
finite test consists of the two maximal lattices `N_1^N(c)` and `N_2^N(c)`,
where `c=(-1)^((N+1)/2) a_(1,N+2)`.  We normalize `c` inside its square
class before choosing literal good BONGs; the stated test spaces themselves
remain exactly `W_1^N(c)` and `W_2^N(c)` up to this explicit square-class
identification.

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

/-- The numerical premise of Theorem 2.8(iv) for the terminal paper index
`i=N+1`, after a maximal rank-`N` test has last order `s`. -/
def HeHuLemma511TerminalTrigger {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat)
    (hm : 2 * k + 3 ≤ m) (s : Int) : Prop :=
  s + 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ ∧
    a.order ⟨2 * k + 4, by omega⟩ +
        2 * (ramificationIndex K : Int) ≤
      s + 2 * (ramificationIndex K : Int)

/-- The finite testing assertion in He--Hu, Lemma 5.11(ii).  The parameter
is the normalized representative of the printed square class
`c=(-1)^(k+2)a_(1,N+2)`; Lemma 5.9 proves that normalization preserves that
square class. -/
noncomputable def HeHuLemma511TestConditions {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m) : Prop :=
  let c := heHuLemma59C a k
  let cn := heHuLemma59NormalizedParameter (K := K) c
  let s := heHuLemma59Parity (K := K) c
  a.HeHuLemma511TerminalTrigger k hm s →
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuOddFirst (K := K) k cn))
        (a.prefixValues (2 * k + 5) (by omega)) ∧
      DiagonalRepresents
        (diagonalUnitCoefficients (heHuOddSecond (K := K) k cn))
        (a.prefixValues (2 * k + 5) (by omega))

/-- Paper index `i=N+1` in the terminal long-representation test. -/
def heHuLemma511TerminalIndex {m : Nat} (k : Nat)
    (hm : 2 * k + 3 ≤ m) :
    LongRepresentationIndex (m + 3) (2 * k + 3) where
  val := 2 * k + 4
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- The canonical first-column maximal test used in Lemma 5.11 has the
published quadratic space `W_1^N(cn)`.  The proof exposes the square factors
in the half-hyperbolic BONG rather than identifying its literal coefficients
definitionally with `[1,-1]`. -/
theorem heHuLemma511FirstTarget_represents_oddFirst
    (x : Kˣ) (k : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma59Target (K := K) x k).valueUnit)
      (diagonalUnitCoefficients
        (heHuOddFirst (K := K) k
          (heHuLemma59NormalizedParameter (K := K) x))) := by
  let cn := heHuLemma59NormalizedParameter (K := K) x
  let tail := BONG.unaryModelGoodBONG cn
  let hIntegral : Lattice.IsIntegral
      (QuadraticSpace.rescaleUnit cn (QuadraticSpace.line K))
      (BONG.unaryModelLattice (K := K)) := by
    simpa only [cn, tail] using heHuLemma59UnaryIntegral (K := K) x
  let line : Fin 1 → Kˣ := Fin.cons cn Fin.elim0
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients tail.valueUnit)
      (diagonalUnitCoefficients line) := by
    have hvalues : tail.valueUnit = line := by
      funext i
      fin_cases i
      change (BONG.unaryModelBONG cn).valueUnit 0 = cn
      exact BONG.unaryModelBONG_valueUnit cn 0
    rw [hvalues]
    exact diagonalRepresents_refl _
  have hlift := heHuLemma45Lemma310_represents_tower
    tail hIntegral (k + 1) line htail
  let raw := heHu2022Lemma310BONG tail hIntegral (k + 1)
  let model := heHuFinFamilyCast (by omega :
      2 * (k + 1) + 1 = 1 + 2 * (k + 1))
    (Fin.append
      (standardHyperbolicEndpointTower (K := K) (k + 1)) line)
  let hdim : 1 + 2 * (k + 1) = 2 * k + 3 := by omega
  have hliftCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) hdim hdim raw.valueUnit model hlift
  have hsource :
      (heHuLemma59Target (K := K) x k).valueUnit =
        heHuFinFamilyCast hdim raw.valueUnit := by
    funext i
    simp only [heHuLemma59Target, raw, tail, cn, heHuFinFamilyCast,
      valueUnit_castLength_heHu]
    congr 2
  have htarget : heHuFinFamilyCast hdim model =
      heHuOddFirst (K := K) k cn := by
    simp only [model, heHuFinFamilyCast_trans]
    rw [← Fin.snoc_eq_append,
      heHuLemma43_snoc_standard_eq_oddFirst (K := K) k cn]
    rfl
  rw [← hsource, htarget] at hliftCast
  simpa only [cn] using hliftCast

/-- Lemma 3.10 lifts an even-valuation Table 1 ternary identification to
the corresponding odd-dimensional second-column test. -/
theorem heHuLemma511LiftEvenTail_represents_oddSecond
    {V' : Type u} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'}
    (b : GoodBONG q' L' 3) (hIntegral : Lattice.IsIntegral q' L')
    (c : Kˣ) (hc : Even (ordUnit K c)) (k : Nat)
    (hTail : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuOddSecondTailEven (K := K) c))) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHu2022Lemma310BONG b hIntegral k).valueUnit)
      (diagonalUnitCoefficients (heHuOddSecond (K := K) k c)) := by
  have hlift := heHuLemma45Lemma310_represents_tower
    b hIntegral k (heHuOddSecondTailEven (K := K) c) hTail
  let model := heHuFinFamilyCast (by omega : 2 * k + 3 = 3 + 2 * k)
    (Fin.append (standardHyperbolicEndpointTower (K := K) k)
      (heHuOddSecondTailEven (K := K) c))
  let hdim : 3 + 2 * k = 2 * k + 3 := by omega
  have hliftCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : 3 + 2 * k = 3 + 2 * k) hdim
      (heHu2022Lemma310BONG b hIntegral k).valueUnit model hlift
  have htarget : heHuFinFamilyCast hdim model =
      heHuOddSecond (K := K) k c := by
    rw [heHuOddSecond_of_even k c hc]
    simp only [model, heHuFinFamilyCast_trans]
    rfl
  rw [htarget] at hliftCast
  simpa only [heHuFinFamilyCast_self] using hliftCast

/-- Lemma 3.10 lifts an odd-valuation Table 1 ternary identification to
the corresponding odd-dimensional second-column test. -/
theorem heHuLemma511LiftOddTail_represents_oddSecond
    {V' : Type u} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'}
    (b : GoodBONG q' L' 3) (hIntegral : Lattice.IsIntegral q' L')
    (c : Kˣ) (hc : ¬ Even (ordUnit K c)) (k : Nat)
    (hTail : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuOddSecondTailOdd (K := K) c))) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHu2022Lemma310BONG b hIntegral k).valueUnit)
      (diagonalUnitCoefficients (heHuOddSecond (K := K) k c)) := by
  have hlift := heHuLemma45Lemma310_represents_tower
    b hIntegral k (heHuOddSecondTailOdd (K := K) c) hTail
  let model := heHuFinFamilyCast (by omega : 2 * k + 3 = 3 + 2 * k)
    (Fin.append (standardHyperbolicEndpointTower (K := K) k)
      (heHuOddSecondTailOdd (K := K) c))
  let hdim : 3 + 2 * k = 2 * k + 3 := by omega
  have hliftCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : 3 + 2 * k = 3 + 2 * k) hdim
      (heHu2022Lemma310BONG b hIntegral k).valueUnit model hlift
  have htarget : heHuFinFamilyCast hdim model =
      heHuOddSecond (K := K) k c := by
    rw [heHuOddSecond_of_not_even k c hc]
    simp only [model, heHuFinFamilyCast_trans]
    rfl
  rw [htarget] at hliftCast
  simpa only [heHuFinFamilyCast_self] using hliftCast

/-- The universal long condition specializes to the first published test
`N_1^N(c)`.  The returned coefficient space is the normalized representative
of the same square class, linked to the literal maximal lattice above. -/
theorem heHu2022Lemma511Universal_to_firstTest
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a)
    (hTrigger : a.HeHuLemma511TerminalTrigger k hm
      (heHuLemma59Parity (K := K) (heHuLemma59C a k))) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuOddFirst (K := K) k
          (heHuLemma59NormalizedParameter (K := K)
            (heHuLemma59C a k))))
      (a.prefixValues (2 * k + 5) (by omega)) := by
  let c := heHuLemma59C a k
  let first := heHuLemma59Target (K := K) c k
  let idx := heHuLemma511TerminalIndex k hm
  have hlong := hAll first (heHuLemma59Target_integral (K := K) c k)
  have htrigger :
      ((if hi : idx.val ≤ 2 * k + 3 then
          a.order ⟨idx.val + 1, idx.succ_lt_large⟩ ≤
            first.order ⟨idx.val - 1, by
              have := idx.one_lt
              have := hi
              omega⟩
        else True) ∧
        first.order ⟨idx.val - 2, by
            have := idx.one_lt
            have := idx.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨idx.val + 1, idx.succ_lt_large⟩ ∧
        a.order ⟨idx.val, by have := idx.succ_lt_large; omega⟩ +
            2 * (ramificationIndex K : Int) ≤
          first.order ⟨idx.val - 2, by
            have := idx.one_lt
            have := idx.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int)) := by
    have hlast : first.order ⟨2 * k + 2, by omega⟩ =
        heHuLemma59Parity (K := K) c := by
      simpa only [first] using heHuLemma59Target_lastOrder (K := K) c k
    constructor
    · rw [dif_neg (by simp only [idx, heHuLemma511TerminalIndex]; omega)]
      trivial
    · constructor
      · have htargetIndex :
            (⟨idx.val - 2, by
              have := idx.one_lt
              have := idx.le_small_succ
              omega⟩ : Fin (2 * k + 3)) =
              ⟨2 * k + 2, by omega⟩ := by
            apply Fin.ext
            change idx.val - 2 = 2 * k + 2
            simp only [idx, heHuLemma511TerminalIndex]
            omega
        have hnextIndex :
            (⟨idx.val + 1, idx.succ_lt_large⟩ : Fin (m + 3)) =
              ⟨2 * k + 5, by omega⟩ := by
          apply Fin.ext
          change idx.val + 1 = 2 * k + 5
          simp only [idx, heHuLemma511TerminalIndex]
        rw [htargetIndex, hlast, hnextIndex]
        exact hTrigger.1
      · have htargetIndex :
            (⟨idx.val - 2, by
              have := idx.one_lt
              have := idx.le_small_succ
              omega⟩ : Fin (2 * k + 3)) =
              ⟨2 * k + 2, by omega⟩ := by
            apply Fin.ext
            change idx.val - 2 = 2 * k + 2
            simp only [idx, heHuLemma511TerminalIndex]
            omega
        have hcurrentIndex :
            (⟨idx.val, by have := idx.succ_lt_large; omega⟩ :
              Fin (m + 3)) = ⟨2 * k + 4, by omega⟩ := by
          apply Fin.ext
          change idx.val = 2 * k + 4
          simp only [idx, heHuLemma511TerminalIndex]
        rw [hcurrentIndex, htargetIndex, hlast]
        exact hTrigger.2
  have hrep := hlong idx htrigger
  have hmodel := heHuLemma511FirstTarget_represents_oddFirst (K := K) c k
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients first.valueUnit)
      (a.prefixValues (2 * k + 5) (by omega)) := by
    have hcast : DiagonalRepresents
        (first.prefixValues (2 * k + 3) (by omega))
        (a.prefixValues (2 * k + 5) (by omega)) :=
      prefixRepresents_cast first a
        (show idx.val - 1 = 2 * k + 3 by
          simp only [idx, heHuLemma511TerminalIndex]
          omega)
        (show idx.val + 1 = 2 * k + 5 by
          simp only [idx, heHuLemma511TerminalIndex]) hrep
    have hvalues : first.prefixValueUnits (2 * k + 3) (by omega) =
        first.valueUnit := by
      funext i
      rfl
    have hcoeff : diagonalUnitCoefficients first.valueUnit =
        first.prefixValues (2 * k + 3) (by omega) := by
      rw [← first.diagonalUnitCoefficients_prefixValueUnits
        (2 * k + 3) (by omega), hvalues]
    rw [hcoeff]
    exact hcast
  exact hmodel.symm_of_sameRank.trans hfull

/-- A reusable specialization of the universal long condition to any
rank-`N` maximal-test BONG whose final order is known.  The equal-rank
identification `hModel` is the semantic bridge from the literal lattice to
the published coefficient space. -/
theorem heHuLemma511Universal_to_test_of_target
    {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (b : GoodBONG s N (2 * k + 3))
    (hBIntegral : Lattice.IsIntegral s N)
    (lastOrder : Int)
    (hLast : b.order ⟨2 * k + 2, by omega⟩ = lastOrder)
    (model : Fin (2 * k + 3) → Kˣ)
    (hModel : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients model))
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a)
    (hTrigger : a.HeHuLemma511TerminalTrigger k hm lastOrder) :
    DiagonalRepresents (diagonalUnitCoefficients model)
      (a.prefixValues (2 * k + 5) (by omega)) := by
  let idx := heHuLemma511TerminalIndex k hm
  have hlong := hAll b hBIntegral
  have htrigger :
      ((if hi : idx.val ≤ 2 * k + 3 then
          a.order ⟨idx.val + 1, idx.succ_lt_large⟩ ≤
            b.order ⟨idx.val - 1, by
              have := idx.one_lt
              have := hi
              omega⟩
        else True) ∧
        b.order ⟨idx.val - 2, by
            have := idx.one_lt
            have := idx.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨idx.val + 1, idx.succ_lt_large⟩ ∧
        a.order ⟨idx.val, by have := idx.succ_lt_large; omega⟩ +
            2 * (ramificationIndex K : Int) ≤
          b.order ⟨idx.val - 2, by
            have := idx.one_lt
            have := idx.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int)) := by
    constructor
    · rw [dif_neg (by simp only [idx, heHuLemma511TerminalIndex]; omega)]
      trivial
    · have htargetIndex :
          (⟨idx.val - 2, by
            have := idx.one_lt
            have := idx.le_small_succ
            omega⟩ : Fin (2 * k + 3)) =
            ⟨2 * k + 2, by omega⟩ := by
          apply Fin.ext
          change idx.val - 2 = 2 * k + 2
          simp only [idx, heHuLemma511TerminalIndex]
          omega
      have hnextIndex :
          (⟨idx.val + 1, idx.succ_lt_large⟩ : Fin (m + 3)) =
            ⟨2 * k + 5, by omega⟩ := by
        apply Fin.ext
        change idx.val + 1 = 2 * k + 5
        simp only [idx, heHuLemma511TerminalIndex]
      have hcurrentIndex :
          (⟨idx.val, by have := idx.succ_lt_large; omega⟩ :
            Fin (m + 3)) = ⟨2 * k + 4, by omega⟩ := by
        apply Fin.ext
        change idx.val = 2 * k + 4
        simp only [idx, heHuLemma511TerminalIndex]
      constructor
      · rw [htargetIndex, hLast, hnextIndex]
        exact hTrigger.1
      · rw [hcurrentIndex, htargetIndex, hLast]
        exact hTrigger.2
  have hrep := hlong idx htrigger
  have hcast : DiagonalRepresents
      (b.prefixValues (2 * k + 3) (by omega))
      (a.prefixValues (2 * k + 5) (by omega)) :=
    prefixRepresents_cast b a
      (show idx.val - 1 = 2 * k + 3 by
        simp only [idx, heHuLemma511TerminalIndex]
        omega)
      (show idx.val + 1 = 2 * k + 5 by
        simp only [idx, heHuLemma511TerminalIndex]) hrep
  have hvalues : b.prefixValueUnits (2 * k + 3) (by omega) =
      b.valueUnit := by
    funext i
    rfl
  have hcoeff : diagonalUnitCoefficients b.valueUnit =
      b.prefixValues (2 * k + 3) (by omega) := by
    rw [← b.diagonalUnitCoefficients_prefixValueUnits
      (2 * k + 3) (by omega), hvalues]
  rw [← hcoeff] at hcast
  exact hModel.symm_of_sameRank.trans hcast

/-- In the even-valuation row, the second published test is obtained from
the literal Lemma 3.11(ii) ternary BONG with defect `2e-1`, followed by the
half-hyperbolic construction of Lemma 3.10. -/
theorem heHu2022Lemma511Universal_to_secondTest_of_even
    [GoodBONGClassificationLaws.{u, u, u} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a)
    (hEven : Even (ordUnit K (heHuLemma59C a k)))
    (hTrigger : a.HeHuLemma511TerminalTrigger k hm 0) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuOddSecond (K := K) k
          (heHuLemma59NormalizedParameter (K := K)
            (heHuLemma59C a k))))
      (a.prefixValues (2 * k + 5) (by omega)) := by
  let c := heHuLemma59C a k
  let delta := normalizedUnitPart K c
  have hdelta : IsValuationUnit K (delta : K) := by
    exact normalizedUnitPart_isValuationUnit K c
  have hparity : heHuLemma59Parity (K := K) c = 0 :=
    heHuLemma59Parity_eq_zero_of_even c hEven
  have hcn : heHuLemma59NormalizedParameter (K := K) c = delta := by
    rw [heHuLemma59NormalizedParameter, hparity]
    simp only [uniformizerPowerUnit, zpow_zero, mul_one, delta]
  let d := 2 * ramificationIndex K - 1
  have hdpos : 0 < d := by
    have he := ramificationIndex_pos (K := K)
    dsimp only [d]
    omega
  have hdodd : Odd d := by
    refine ⟨ramificationIndex K - 1, ?_⟩
    have he := ramificationIndex_pos (K := K)
    dsimp only [d]
    omega
  have hdlt : d < 2 * ramificationIndex K := by
    dsimp only [d]
    omega
  rcases Dyadic.exists_unit_quadraticDefect_eq_odd
      (K := K) d hdpos hdodd hdlt with ⟨kappa, hkappa, hkappaDefectNat⟩
  have hkappaDefect : defectOrder (K := K) kappa =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
    rw [Beli2009FinalRemarksProof.defectOrder_eq_natCast_of_quadraticDefect_eq
      (K := K) kappa d hkappaDefectNat]
    congr 1
    have he := ramificationIndex_pos (K := K)
    have hdNat : d + 1 = 2 * ramificationIndex K := by
      dsimp only [d]
      omega
    have hdRat : (d : ℚ) + 1 = 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hdNat
    linarith
  let tail := heHuLemma311OddSecondUnitTail
    delta kappa hdelta hkappa hkappaDefect
  have hTailIntegral : Lattice.IsIntegral _ _ :=
    heHuIntegral_of_firstOrder_nonneg tail (by
      rw [heHuLemma311OddSecondUnitTail_order]
      norm_num)
  let raw := heHu2022Lemma310BONG tail hTailIntegral k
  let hdim : 3 + 2 * k = 2 * k + 3 := by omega
  let target := raw.castLength hdim
  have hLast : target.order ⟨2 * k + 2, by omega⟩ = 0 := by
    rw [show target = raw.castLength hdim by rfl, GoodBONG.order_castLength]
    have h := heHu2022Lemma310TailOrders tail hTailIntegral k (2 : Fin 3)
    rw [heHuLemma311OddSecondUnitTail_order] at h
    simpa [raw] using h
  have hTailModel :=
    heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven
      delta kappa hdelta hkappa hkappaDefect
  have hdeltaEven : Even (ordUnit K delta) := by
    rw [(isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdelta]
    exact ⟨0, by norm_num⟩
  have hRawModel := heHuLemma511LiftEvenTail_represents_oddSecond
    tail hTailIntegral delta hdeltaEven k hTailModel
  have hModelCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) hdim (rfl : 2 * k + 3 = 2 * k + 3)
      raw.valueUnit (heHuOddSecond (K := K) k delta) hRawModel
  have hTargetValues : target.valueUnit =
      heHuFinFamilyCast hdim raw.valueUnit := by
    funext i
    simp only [target, heHuFinFamilyCast, valueUnit_castLength_heHu]
    congr 1
  have hModel : DiagonalRepresents
      (diagonalUnitCoefficients target.valueUnit)
      (diagonalUnitCoefficients (heHuOddSecond (K := K) k delta)) := by
    rw [hTargetValues]
    simpa only [heHuFinFamilyCast_self] using hModelCast
  have hResult := a.heHuLemma511Universal_to_test_of_target hm target
    (heHuHalfHyperbolicExtension_isIntegral hTailIntegral k) 0 hLast
    (heHuOddSecond (K := K) k delta) hModel hAll hTrigger
  rw [hcn]
  exact hResult

/-- In the odd-valuation row, the second published test is the exceptional
discriminant-endpoint ternary BONG of Lemma 5.7, again lifted by Lemma 3.10. -/
theorem heHu2022Lemma511Universal_to_secondTest_of_not_even
    [GoodBONGClassificationLaws.{u, u, u} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a)
    (hNotEven : ¬ Even (ordUnit K (heHuLemma59C a k)))
    (hTrigger : a.HeHuLemma511TerminalTrigger k hm 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuOddSecond (K := K) k
          (heHuLemma59NormalizedParameter (K := K)
            (heHuLemma59C a k))))
      (a.prefixValues (2 * k + 5) (by omega)) := by
  let c := heHuLemma59C a k
  let delta := normalizedUnitPart K c
  have hdelta : IsValuationUnit K (delta : K) := by
    exact normalizedUnitPart_isValuationUnit K c
  have hparity : heHuLemma59Parity (K := K) c = 1 :=
    heHuLemma59Parity_eq_one_of_not_even c hNotEven
  have hcn : heHuLemma59NormalizedParameter (K := K) c =
      heHuLemma57Parameter (K := K) delta := by
    rw [heHuLemma59NormalizedParameter, hparity]
    rfl
  let tail := heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  have hTailIntegral : Lattice.IsIntegral _ _ :=
    heHuIntegral_of_firstOrder_nonneg tail (by
      rw [heHuLemma311OddSecondUnitUniformizerTail_order]
      norm_num)
  let raw := heHu2022Lemma310BONG tail hTailIntegral k
  let hdim : 3 + 2 * k = 2 * k + 3 := by omega
  let target := raw.castLength hdim
  have hLast : target.order ⟨2 * k + 2, by omega⟩ = 1 := by
    rw [show target = raw.castLength hdim by rfl, GoodBONG.order_castLength]
    have h := heHu2022Lemma310TailOrders tail hTailIntegral k (2 : Fin 3)
    rw [heHuLemma311OddSecondUnitUniformizerTail_order] at h
    simpa [raw] using h
  have hParameterNotEven :
      ¬ Even (ordUnit K (heHuLemma57Parameter (K := K) delta)) := by
    rw [heHuLemma57Parameter_order delta hdelta]
    exact Int.not_even_iff_odd.mpr odd_one
  have hTailModel : DiagonalRepresents
      (diagonalUnitCoefficients tail.valueUnit)
      (diagonalUnitCoefficients
        (heHuOddSecondTailOdd (K := K)
          (heHuLemma57Parameter (K := K) delta))) := by
    have h := heHuLemma57Target_represents_oddSecond
      (K := K) delta hdelta
    rw [heHuOddSecond_of_not_even 0 _ hParameterNotEven] at h
    have hzero :
        Fin.append (standardHyperbolicEndpointTower (K := K) 0)
            (heHuOddSecondTailOdd (K := K)
              (heHuLemma57Parameter (K := K) delta)) =
          heHuOddSecondTailOdd (K := K)
            (heHuLemma57Parameter (K := K) delta) := by
      have hz := heHuStandardTower_zero_append (K := K)
        (heHuOddSecondTailOdd (K := K)
          (heHuLemma57Parameter (K := K) delta))
      simpa only [heHuFinFamilyCast_self] using hz
    rw [hzero] at h
    simpa only [tail] using h
  have hRawModel := heHuLemma511LiftOddTail_represents_oddSecond
    tail hTailIntegral (heHuLemma57Parameter (K := K) delta)
      hParameterNotEven k hTailModel
  have hModelCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) hdim (rfl : 2 * k + 3 = 2 * k + 3)
      raw.valueUnit
      (heHuOddSecond (K := K) k
        (heHuLemma57Parameter (K := K) delta)) hRawModel
  have hTargetValues : target.valueUnit =
      heHuFinFamilyCast hdim raw.valueUnit := by
    funext i
    simp only [target, heHuFinFamilyCast, valueUnit_castLength_heHu]
    congr 1
  have hModel : DiagonalRepresents
      (diagonalUnitCoefficients target.valueUnit)
      (diagonalUnitCoefficients
        (heHuOddSecond (K := K) k
          (heHuLemma57Parameter (K := K) delta))) := by
    rw [hTargetValues]
    simpa only [heHuFinFamilyCast_self] using hModelCast
  have hResult := a.heHuLemma511Universal_to_test_of_target hm target
    (heHuHalfHyperbolicExtension_isIntegral hTailIntegral k) 1 hLast
    (heHuOddSecond (K := K) k
      (heHuLemma57Parameter (K := K) delta)) hModel hAll hTrigger
  rw [hcn]
  exact hResult

/-- Lemma 5.11, implication `(i) -> (ii)`: the universal long condition
specializes to the two maximal test lattices printed in Definition 3.4. -/
theorem heHu2022Lemma511Universal_to_tests
    [GoodBONGClassificationLaws.{u, u, u} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 2) a) :
    a.HeHuLemma511TestConditions k hm := by
  dsimp only [HeHuLemma511TestConditions]
  intro hTrigger
  let c := heHuLemma59C a k
  have hFirst := a.heHu2022Lemma511Universal_to_firstTest hm hAll hTrigger
  refine ⟨hFirst, ?_⟩
  by_cases hEven : Even (ordUnit K c)
  · have hparity : heHuLemma59Parity (K := K) c = 0 :=
      heHuLemma59Parity_eq_zero_of_even c hEven
    apply a.heHu2022Lemma511Universal_to_secondTest_of_even hm hAll hEven
    change a.HeHuLemma511TerminalTrigger k hm
      (heHuLemma59Parity (K := K) c) at hTrigger
    rw [hparity] at hTrigger
    exact hTrigger
  · have hparity : heHuLemma59Parity (K := K) c = 1 :=
      heHuLemma59Parity_eq_one_of_not_even c hEven
    apply a.heHu2022Lemma511Universal_to_secondTest_of_not_even hm hAll hEven
    change a.HeHuLemma511TerminalTrigger k hm
      (heHuLemma59Parity (K := K) c) at hTrigger
    rw [hparity] at hTrigger
    exact hTrigger

/-- A nonnegative middle gap forces the odd threshold `G_N` to be at most
`2e-1`.  This is the elementary parity estimate used twice in the proof of
Lemma 5.11(ii) implies (iii). -/
theorem heHuLemma511OddThreshold_le_twoE_sub_one_of_nonnegativeGap
    {m n : Nat} (a : GoodBONG q L (m + 1)) (hm : n + 2 ≤ m)
    (hGap : 0 ≤ a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) :
    a.heHuOddThreshold n hm ≤ 2 * (ramificationIndex K : Int) - 1 := by
  unfold heHuOddThreshold
  by_cases hEven : Even
      (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩)
  · rw [if_pos hEven]
    omega
  · rw [if_neg hEven]
    have hPositive :
        0 < a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by
      by_contra hNotPositive
      have hZero :
          a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ = 0 := by
        omega
      apply hEven
      rw [hZero]
      exact Even.zero
    omega

/-- Under the hypotheses preceding Lemma 5.11, a terminal gap larger than
`2e` forces the two intermediate source orders to have precisely the shape
used in the published determinant argument: `R_(N+1)` is even and
`R_(N+2)` is either zero or one. -/
theorem heHuLemma511_largeGap_terminalShape
    [GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI2O (2 * k + 3) (by omega) (by omega))
    (hLarge : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩) :
    Even (a.order ⟨2 * k + 3, by omega⟩) ∧
      (a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 4, by omega⟩ = 1) := by
  have hI2' := hI2
  unfold HeHuI2E at hI2'
  dsimp only at hI2'
  rcases hI2' with hAlphaZero | ⟨hAlphaOne, _⟩
  · have hBoundaryOrder : a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) :=
      a.heHu2022Lemma54i (n := 2 * k + 3) (by omega)
        ⟨k + 1, by omega⟩ (by omega) hI1 hAlphaZero
    have hNextCases : a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 4, by omega⟩ = 1 :=
      hOdd.1 hAlphaZero
    refine ⟨?_, hNextCases⟩
    rw [hBoundaryOrder]
    exact ⟨-(ramificationIndex K : Int), by ring⟩
  · let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
    let nextBoundary : Fin (m + 2) := ⟨2 * k + 4, by omega⟩
    have hBoundaryBase : a.order ⟨2 * k + 2, by omega⟩ = 0 :=
      hI1.oddOrder ⟨2 * k + 2, by omega⟩ (by
        change Odd (2 * k + 3)
        exact ⟨k + 1, by omega⟩)
    have hBoundaryGap : a.orderGap boundary =
        a.order ⟨2 * k + 3, by omega⟩ := by
      unfold orderGap
      rw [show boundary.castSucc =
          (⟨2 * k + 2, by omega⟩ : Fin (m + 3)) by apply Fin.ext; rfl,
        show boundary.succ =
          (⟨2 * k + 3, by omega⟩ : Fin (m + 3)) by apply Fin.ext; rfl,
        hBoundaryBase]
      simp
    have hBoundaryShape :
        a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
          (Even (a.order ⟨2 * k + 3, by omega⟩) ∧
            2 - 2 * (ramificationIndex K : Int) ≤
              a.order ⟨2 * k + 3, by omega⟩ ∧
            a.order ⟨2 * k + 3, by omega⟩ ≤ 0) := by
      have hShape := (a.heHu2022Proposition26 boundary).alphaOne
        (by simpa only [boundary] using hAlphaOne) |>.1
      rw [hBoundaryGap] at hShape
      exact hShape
    have hNextGap : a.orderGap nextBoundary =
        a.order ⟨2 * k + 5, by omega⟩ -
          a.order ⟨2 * k + 4, by omega⟩ := by
      unfold orderGap
      rw [show nextBoundary.castSucc =
          (⟨2 * k + 4, by omega⟩ : Fin (m + 3)) by apply Fin.ext; rfl,
        show nextBoundary.succ =
          (⟨2 * k + 5, by omega⟩ : Fin (m + 3)) by apply Fin.ext; rfl]
    have hNextAlpha : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue nextBoundary :=
      ((a.heHu2022Proposition26 nextBoundary).compareTwoE.2.2).2 (by
        rw [hNextGap]
        exact hLarge)
    let middle : Fin (m + 3) := ⟨2 * k + 4, by omega⟩
    have hMiddleEvenIndex : Even middle.val := ⟨k + 2, by
      simp only [middle]
      omega⟩
    have hMiddleNonnegative : 0 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
      have h := ((a.heHu2022Proposition27i hIntegral).oddIndexed
        middle middle le_rfl hMiddleEvenIndex hMiddleEvenIndex).1
      simpa only [middle] using h
    have hBoundaryNotOne : a.order ⟨2 * k + 3, by omega⟩ ≠ 1 := by
      intro hOne
      have hMiddleGeOne := a.heHu2022Remark52_order_ge_one
        (n := 2 * k + 3) (by omega) ⟨k + 1, by omega⟩
          (by omega) hIntegral hOne
      have hMiddleGeOne' : 1 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
        simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using
          hMiddleGeOne
      have hGapNonnegative :
          0 ≤ a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩ := by omega
      have hThreshold :=
        a.heHuLemma511OddThreshold_le_twoE_sub_one_of_nonnegativeGap
          (n := 2 * k + 3) (by omega) hGapNonnegative
      have hAlphaUpper := hOdd.2 hAlphaOne (Or.inl hOne)
      have hThresholdRat :
          (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) ≤
            2 * (ramificationIndex K : ℚ) - 1 := by
        exact_mod_cast hThreshold
      have := hAlphaUpper.trans hThresholdRat
      linarith
    have hBoundaryEven : Even (a.order ⟨2 * k + 3, by omega⟩) :=
      (hBoundaryShape.resolve_left hBoundaryNotOne).1
    have hBoundaryNonpositive : a.order ⟨2 * k + 3, by omega⟩ ≤ 0 :=
      (hBoundaryShape.resolve_left hBoundaryNotOne).2.2
    have hMiddleLeOne : a.order ⟨2 * k + 4, by omega⟩ ≤ 1 := by
      by_contra hNotLe
      have hMiddleGtOne : 1 < a.order ⟨2 * k + 4, by omega⟩ := by omega
      have hGapNonnegative :
          0 ≤ a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩ := by omega
      have hThreshold :=
        a.heHuLemma511OddThreshold_le_twoE_sub_one_of_nonnegativeGap
          (n := 2 * k + 3) (by omega) hGapNonnegative
      have hAlphaUpper := hOdd.2 hAlphaOne (Or.inr hMiddleGtOne)
      have hThresholdRat :
          (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) ≤
            2 * (ramificationIndex K : ℚ) - 1 := by
        exact_mod_cast hThreshold
      have := hAlphaUpper.trans hThresholdRat
      linarith
    refine ⟨hBoundaryEven, ?_⟩
    omega

/-- Lemma 5.11, implication `(ii) -> (iii)`.  If the terminal gap were
larger than `2e`, both published maximal spaces would represent the same
codimension-two source prefix.  Lemma 3.13 says that exactly one can do so. -/
theorem heHu2022Lemma511Tests_to_i3O
    [GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI2O (2 * k + 3) (by omega) (by omega))
    (hTests : a.HeHuLemma511TestConditions k hm) :
    a.HeHuI3O (2 * k + 3) (by omega) (by omega) := by
  unfold HeHuI3O
  apply le_of_not_gt
  intro hLarge
  have hLargeNormal : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 5, by omega⟩ -
        a.order ⟨2 * k + 4, by omega⟩ := by
    simpa only [show 2 * k + 3 + 2 = 2 * k + 5 by omega,
      show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hLarge
  have hShape := a.heHuLemma511_largeGap_terminalShape hm hIntegral
    hI1 hI2 hOdd hLargeNormal
  let c := heHuLemma59C a k
  let cn := heHuLemma59NormalizedParameter (K := K) c
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hParityGap : heHuLemma59Parity (K := K) c =
      if Even gap then 0 else 1 := by
    apply heHuLemma59Parity_eq_gapParity c gap
    simpa only [c, gap] using
      a.heHuLemma59_c_order_sub_gap_even k hm hI1
  have hParityMiddle : heHuLemma59Parity (K := K) c =
      a.order ⟨2 * k + 4, by omega⟩ := by
    rcases hShape.2 with hMiddleZero | hMiddleOne
    · have hGapEven : Even gap := by
        have h := (Even.zero : Even (0 : Int)).sub hShape.1
        simpa only [gap, hMiddleZero] using h
      rw [if_pos hGapEven] at hParityGap
      simpa only [hMiddleZero] using hParityGap
    · have hGapOdd : Odd gap := by
        have h := (odd_one : Odd (1 : Int)).sub_even hShape.1
        simpa only [gap, hMiddleOne] using h
      have hGapNotEven : ¬ Even gap := Int.not_even_iff_odd.mpr hGapOdd
      rw [if_neg hGapNotEven] at hParityGap
      simpa only [hMiddleOne] using hParityGap
  have hTerminal : a.HeHuLemma511TerminalTrigger k hm
      (heHuLemma59Parity (K := K) c) := by
    unfold HeHuLemma511TerminalTrigger
    rw [hParityMiddle]
    constructor <;> omega
  have hRepresentations :
      DiagonalRepresents
          (diagonalUnitCoefficients (heHuOddFirst (K := K) k cn))
          (a.prefixValues (2 * k + 5) (by omega)) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients (heHuOddSecond (K := K) k cn))
          (a.prefixValues (2 * k + 5) (by omega)) := by
    dsimp only [HeHuLemma511TestConditions] at hTests
    simpa only [c, cn] using hTests hTerminal
  let target := a.prefixValueUnits (2 * k + 5) (by omega)
  have hFirst : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) k cn))
      (diagonalUnitCoefficients target) := by
    simpa only [target, diagonalUnitCoefficients_prefixValueUnits] using
      hRepresentations.1
  have hSecond : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond (K := K) k cn))
      (diagonalUnitCoefficients target) := by
    simpa only [target, diagonalUnitCoefficients_prefixValueUnits] using
      hRepresentations.2
  have hsign : -((-1 : Kˣ) ^ (k + 1)) = (-1 : Kˣ) ^ (k + 2) := by
    have h := congrArg Neg.neg
      (heHuLemma59_neg_signedPower_eq (K := K) k)
    simpa only [neg_neg] using h.symm
  have hdet : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant (heHuOddFirst (K := K) k cn)) := by
    rw [diagonalUnitDeterminant_heHuOddFirst]
    rw [a.diagonalUnitDeterminant_prefixValueUnits]
    have hnormalized := heHuLemma59_normalized_sameSquareClass (K := K) c
    have heq :
        (-a.prefixProduct (2 * k + 5)) *
            (((-1 : Kˣ) ^ (k + 1)) * cn) = c * cn := by
      calc
        _ = (-((-1 : Kˣ) ^ (k + 1))) *
              (a.prefixProduct (2 * k + 5) * cn) := by
                rw [neg_mul, neg_mul]
                congr 1
                ac_rfl
        _ = ((-1 : Kˣ) ^ (k + 2)) *
              (a.prefixProduct (2 * k + 5) * cn) := by rw [hsign]
        _ = c * cn := by
          dsimp only [c, heHuLemma59C]
          rw [mul_assoc]
    rw [heq]
    simpa only [cn, c] using hnormalized
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heHuOddFirst (K := K) k cn) (heHuOddSecond (K := K) k cn)
      (heHu2022Definition34Proposition35Odd (K := K) k cn) target hdet
  rcases hExactlyOne with hOnlyFirst | hOnlySecond
  · exact hOnlyFirst.2 hSecond
  · exact hOnlySecond.1 hFirst

/-- Lemma 5.11, implication `(iii) -> (i)`.  Every index through `N`
descends to the rank-`N-1` prefix and Lemma 4.5.  The only remaining index
`N+1` contradicts `I3^O(N)` numerically. -/
theorem heHu2022Lemma511I3O_to_universal
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hOdd : a.HeHuI3O (2 * k + 3) (by omega) (by omega)) :
    HeHuAllLongRepresentationConditions.{u, v, w}
      (n := 2 * k + 2) a := by
  intro W _ _ r M b hBIntegral
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    beliUniversalAlphaLaws
  unfold LongRepresentationConditions
  intro i htrigger
  by_cases hiNonterminal : i.val ≤ 2 * k + 3
  · let wp := b.toBONG.prefixWitness (2 * k + 2) (by omega)
    let bp := wp.toGoodBONG b.good
    have hbpIntegral : Lattice.IsIntegral
        (r.restrict wp.carrier wp.nondegenerate) wp.lattice :=
      b.heHuLemma510_prefix_integral hBIntegral wp
    have hlong : a.LongRepresentationConditions bp :=
      a.heHu2022Lemma45Sufficiency sourceLaws targetLaws bp (by omega)
        hAIntegral hbpIntegral hI1 hI2 hI3
    let j : LongRepresentationIndex (m + 3) (2 * k + 2) := {
      val := i.val
      one_lt := i.one_lt
      succ_lt_large := i.succ_lt_large
      le_small_succ := by omega }
    have htargetOrder (t : Nat) (ht : t < 2 * k + 2) :
        bp.order ⟨t, ht⟩ = b.order ⟨t, by omega⟩ := by
      change wp.bong.order ⟨t, ht⟩ = b.toBONG.order ⟨t, by omega⟩
      have ho := wp.toSegmentWitness.order_eq ⟨t, ht⟩
      have hsource : wp.sourceIndex ⟨t, ht⟩ =
          (⟨t, by omega⟩ : Fin (2 * k + 3)) := by
        apply Fin.ext
        simp only [wp, BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]
      rw [hsource] at ho
      exact ho
    have htrigger' :
        ((if hj : j.val ≤ 2 * k + 2 then
            a.order ⟨j.val + 1, j.succ_lt_large⟩ ≤
              bp.order ⟨j.val - 1, by
                have := j.one_lt
                have := hj
                omega⟩
          else True) ∧
          bp.order ⟨j.val - 2, by
              have := j.one_lt
              have := j.le_small_succ
              omega⟩ + 2 * (ramificationIndex K : Int) <
            a.order ⟨j.val + 1, j.succ_lt_large⟩ ∧
          a.order ⟨j.val, by have := j.succ_lt_large; omega⟩ +
              2 * (ramificationIndex K : Int) ≤
            bp.order ⟨j.val - 2, by
              have := j.one_lt
              have := j.le_small_succ
              omega⟩ + 2 * (ramificationIndex K : Int)) := by
      have hfullFirst : a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
          b.order ⟨i.val - 1, by omega⟩ := by
        have hiFull : i.val ≤ 2 * k + 2 + 1 := by omega
        simpa only [dif_pos hiFull] using htrigger.1
      constructor
      · by_cases hj : j.val ≤ 2 * k + 2
        · rw [dif_pos hj]
          have ht : i.val - 1 < 2 * k + 2 := by
            have hj' : i.val ≤ 2 * k + 2 := by
              simpa only [j] using hj
            omega
          have heq := htargetOrder (i.val - 1) ht
          simpa only [j, heq] using hfullFirst
        · rw [dif_neg hj]
          trivial
      · constructor
        · simpa only [j, htargetOrder (i.val - 2) (by omega)] using
            htrigger.2.1
        · simpa only [j, htargetOrder (i.val - 2) (by omega)] using
            htrigger.2.2
    have hrep := hlong j htrigger'
    have htarget :
        bp.prefixValues (j.val - 1) (by
          have := j.le_small_succ
          omega) =
          b.prefixValues (i.val - 1) (by
            have := i.le_small_succ
            omega) := by
      funext t
      have htShort : t.val < 2 * k + 2 := by
        have := t.isLt
        simp only [j] at this
        omega
      change wp.bong.value ⟨t.val, htShort⟩ =
        b.toBONG.value ⟨t.val, by omega⟩
      have hv := wp.toSegmentWitness.value_eq ⟨t.val, htShort⟩
      have hsource : wp.sourceIndex ⟨t.val, htShort⟩ =
          (⟨t.val, by omega⟩ : Fin (2 * k + 3)) := by
        apply Fin.ext
        simp only [wp, BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]
      rw [hsource] at hv
      exact hv
    rw [htarget] at hrep
    simpa only [j] using hrep
  · have hiTerminal : i.val = 2 * k + 4 := by
      have := i.le_small_succ
      omega
    exfalso
    have hlow := htrigger.2.2
    have hhigh := htrigger.2.1
    have hbound := hOdd
    unfold HeHuI3O at hbound
    have hcurrentIndex :
        (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (m + 3)) =
          ⟨2 * k + 4, by omega⟩ := by
      apply Fin.ext
      exact hiTerminal
    have hnextIndex :
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 3)) =
          ⟨2 * k + 5, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = 2 * k + 5
      omega
    have htargetIndex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * k + 3)) =
          ⟨2 * k + 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 2 = 2 * k + 2
      omega
    rw [hcurrentIndex, htargetIndex] at hlow
    rw [htargetIndex, hnextIndex] at hhigh
    have hbound' :
        a.order ⟨2 * k + 5, by omega⟩ -
            a.order ⟨2 * k + 4, by omega⟩ ≤
          2 * (ramificationIndex K : Int) := by
      simpa only using hbound
    omega

/-- He--Hu, Lemma 5.11, complete equivalence of the universal form of
Theorem 2.8(iv), the two published maximal test lattices, and `I3^O(n)`.
As in the paper, the ambient `n`-universality premise is retained even though
the equivalence itself uses its integral and good-BONG consequences only. -/
theorem heHu2022Lemma511
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hI2O : a.HeHuI2O (2 * k + 3) (by omega) (by omega)) :
    Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) →
      ((HeHuAllLongRepresentationConditions.{u, v, u}
          (n := 2 * k + 2) a ↔
        a.HeHuLemma511TestConditions k hm) ∧
       (a.HeHuLemma511TestConditions k hm ↔
        a.HeHuI3O (2 * k + 3) (by omega) (by omega))) := by
  intro _hAmbient
  constructor
  · constructor
    · intro hAll
      exact @heHu2022Lemma511Universal_to_tests K _ _ _ _ _ V _ _ q L
        unitClassification m k a hm hAll
    · intro hTests
      have hI3O := a.heHu2022Lemma511Tests_to_i3O hm hAIntegral
        hI1 hI2 hI2O hTests
      intro X _ _ s N b hB
      exact (a.heHu2022Lemma511I3O_to_universal sourceLaws hm hAIntegral
        hI1 hI2 hI3 hI3O) b hB
  · constructor
    · exact a.heHu2022Lemma511Tests_to_i3O hm hAIntegral
        hI1 hI2 hI2O
    · intro hI3O
      have hAll : HeHuAllLongRepresentationConditions.{u, v, u}
          (n := 2 * k + 2) a := by
        intro X _ _ s N b hB
        exact (a.heHu2022Lemma511I3O_to_universal sourceLaws hm hAIntegral
          hI1 hI2 hI3 hI3O) b hB
      exact @heHu2022Lemma511Universal_to_tests K _ _ _ _ _ V _ _ q L
        unitClassification m k a hm hAll

end BONG.GoodBONG

end Bong
