/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankTwoFirst

/-!
# The nonexceptional corank-two order profile in He (2025), Lemma 6.8

For either ambient column, three actual maximal tests and the finite full
signed defect determine every order. No ambient classification conclusion
or converse to a necessary profile theorem is assumed.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Every nonexceptional parameter has its actual finite defect strictly below 2e. -/
theorem heADCSharpDefectData (c : Kˣ) (hs : HeHuSharpDomain c) :
    let d : Int := (quadraticDefect K c).toNat
    d < 2 * (ramificationIndex K : Int) ∧
      defectOrder (K := K) c = ((d : ℚ) : WithTop ℚ) := by
  let d : Int := (quadraticDefect K c).toNat
  let D := heHuSharpData c hs
  have hsource : D.sourceDefect = (d : ℚ) := by
    simp only [D, d, heHuSharpData, Int.cast_natCast]
  have hdlt : (d : ℚ) < 2 * (ramificationIndex K : ℚ) := by
    rw [← hsource]
    exact D.sourceDefect_lt_twoE
  have hdInt : d < 2 * (ramificationIndex K : Int) := by exact_mod_cast hdlt
  refine ⟨hdInt, ?_⟩
  rw [← hsource]
  exact D.source_defectOrder

/-- Three actual tests and a finite full defect force the generic maximal order profile. -/
theorem heADCEvenCorankTwo_orders_of_finite_full_defect
    (k : Nat) (a : GoodBONG q L (2 * k + 4)) (hIntegral : Lattice.IsIntegral q L)
    (hOne : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
      L (heADCN1Even k (1 : Kˣ)).lattice)
    (hDelta : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice)
    (hTwo : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) k))) L (heADCN2Even k
          (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) k)).lattice)
    (d : Int) (hd : d < 2 * (ramificationIndex K : Int))
    (hfull : defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) =
      ((d : ℚ) : WithTop ℚ)) :
    ∀ i, a.order i = heADCMaximalOrderProfile (K := K) (k + 1) ![0, 1 - d]
      ⟨i.val, by omega⟩ := by
  obtain ⟨_, hhead, hnext⟩ := a.heADC2025Lemma64ii k hIntegral hOne hDelta
  let current : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hfullLt : defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) <
      ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    rw [hfull]
    apply WithTop.coe_lt_coe.mpr
    exact_mod_cast hd
  have hgap := a.orderGap_ge_neg_two_mul_e current
  change -(2 * (ramificationIndex K : Int)) ≤
    a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ at hgap
  rw [hnext] at hgap
  have hnotEndpoint : a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int)) := by
    intro heq
    have H := a.heADCEvenEndpoint_signedPrefix_defect (k + 1) (by omega) hIntegral
      (by simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using heq)
    have H' : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) := by
      simpa only [Nat.add_assoc] using H
    exact (not_lt_of_ge H') hfullLt
  have hR : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩ := by
    by_contra hnot
    have hlastValue : a.order ⟨2 * k + 3, by omega⟩ =
        1 - 2 * (ramificationIndex K : Int) := by omega
    have hodd : Odd (a.orderGap current) := by
      change Odd (a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩)
      rw [hlastValue, hnext]
      exact ⟨-(ramificationIndex K : Int), by ring⟩
    have hpositive := a.heADC2025Corollary32i current hodd
    change 0 < a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ at hpositive
    have he := ramificationIndex_pos (K := K)
    omega
  have hcase : Even (a.order ⟨2 * k + 2, by omega⟩) := by rw [hnext]; exact Even.zero
  have H := a.heADC2025Lemma67i k hIntegral hhead hR (Or.inl hcase) hTwo
  have hlast : a.order ⟨2 * k + 3, by omega⟩ = 1 - d := by
    rcases H with hzero | ⟨_, hraw, hcap⟩
    · have hzeroGap := (a.heADC2025Proposition34 current).alphaZero.mp hzero
      change a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ = _ at hzeroGap
      rw [hnext] at hzeroGap
      omega
    · have hheadLast : a.order ⟨2 * k + 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
        have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
        simpa only [if_neg hodd] using hhead ⟨2 * k + 1, by omega⟩
      have hprefix := a.heADCEvenEndpoint_signedPrefix_defect k (by omega)
        hIntegral hheadLast
      have hrawEq := hraw.trans hcap
      have hpairLt : a.adjacentDefect current <
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        rw [hrawEq]
        apply WithTop.coe_lt_coe.mpr
        have hRQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
            (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by exact_mod_cast hR
        linarith
      have hfullEq : defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) =
          a.adjacentDefect current := by
        rw [show k + 2 = (k + 1) + 1 by omega,
          a.toBONG.signedEvenPrefixProduct_succ (k + 1) (by omega)]
        exact defectOrder_mul_eq_right_of_lt_left (hpairLt.trans_le hprefix)
      have heqQ := WithTop.coe_inj.mp (hfull.symm.trans (hfullEq.trans hrawEq))
      have heqInt : d = 1 - a.order ⟨2 * k + 3, by omega⟩ := by exact_mod_cast heqQ
      omega
  intro i
  by_cases hi : i.val < 2 * k + 2
  · simp only [heADCMaximalOrderProfile, dif_pos (show i.val < 2 * (k + 1) by omega)]
    exact hhead ⟨i.val, hi⟩
  · have hcases : i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 := by omega
    rcases hcases with hprevious | hterminal
    · have hiEq : i = ⟨2 * k + 2, by omega⟩ := Fin.ext hprevious
      rw [hiEq]
      simpa [heADCMaximalOrderProfile, show 2 * (k + 1) = 2 * k + 2 by omega] using hnext
    · have hiEq : i = ⟨2 * k + 3, by omega⟩ := Fin.ext hterminal
      rw [hiEq]
      simpa [heADCMaximalOrderProfile, show 2 * (k + 1) = 2 * k + 2 by omega,
        show ¬ 2 * k + 3 < 2 * k + 2 by omega,
        show 2 * k + 3 - (2 * k + 2) = 1 by omega] using hlast

end BONG.GoodBONG

end Bong
