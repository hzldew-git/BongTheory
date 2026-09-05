/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryCandidate
import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.BeliUniversalCentral

/-!
# Representation conditions for the exceptional quaternary lattice

This file begins the literal verification of conditions (i)--(iv) in He
(2025), Lemma 6.12(i).  The hypotheses on a binary target expose exactly the
published numerical data; subsequent files instantiate them for every member
of the maximal binary catalogue represented by `W_1^4(Delta)`.
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

/-- The order profile printed in He (2025), Lemmas 6.10--6.12. -/
def HeADCExceptionalQuaternaryOrders (a : GoodBONG q L 4) : Prop :=
  ∀ i, a.order i = (![0, -(2 * (ramificationIndex K : Int)), 0,
    2 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i

/-- The constructed exceptional candidate has the published profile. -/
theorem heADCExceptionalQuaternaryCandidate_hasOrders :
    HeADCExceptionalQuaternaryOrders
      (heADCExceptionalQuaternaryCandidate (K := K)) :=
  heADCExceptionalQuaternaryCandidate_orders

/-- Theorem 3.6(i) holds for every integral binary target. -/
theorem heADCExceptional_orderCondition (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hb : Lattice.IsIntegral r M) :
    a.RepresentationOrderCondition b (by omega) := by
  dsimp only [HeADCExceptionalQuaternaryOrders] at ha
  intro i
  left
  fin_cases i
  · have h := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
      (by decide) (by decide)).1
    simpa [ha] using h
  · have h := ((b.heHu2022Proposition27i hb).evenIndexed 1 1 le_rfl
      (by decide) (by decide)).1
    simpa [ha] using h

/-- Theorem 3.6(iv) is vacuous for every integral binary target. -/
theorem heADCExceptional_longConditions (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hb : Lattice.IsIntegral r M) :
    a.LongRepresentationConditions b := by
  dsimp only [HeADCExceptionalQuaternaryOrders] at ha
  intro i htrigger
  have hi : i.val = 2 := by have := i.one_lt; have := i.succ_lt_large; omega
  have hzero := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
    (by decide) (by decide)).1
  have h := htrigger.2.1
  simp only [hi, ha] at h
  change b.order 0 + 2 * (ramificationIndex K : Int) <
    2 - 2 * (ramificationIndex K : Int) at h
  have he := ramificationIndex_pos (K := K)
  omega

/-- The first inequality in Theorem 3.6(ii) follows from the half-gap term. -/
theorem heADCExceptional_firstDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hb : Lattice.IsIntegral r M) (i : RepresentationIndex 4 2)
    (hi : i.val = 1) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 1 1 := by
  dsimp only [HeADCExceptionalQuaternaryOrders] at ha
  have hzero := ((b.heHu2022Proposition27i hb).oddIndexed 0 0 le_rfl
    (by decide) (by decide)).1
  rw [coe_representationAlphaValue]
  apply (a.representationAlpha_le_halfGap b i).trans
  apply le_trans (b := (0 : WithTop ℚ))
  · unfold representationHalfGap
    simp only [hi, ha]
    change ((((-(2 * (ramificationIndex K : Int)) - b.order 0 : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤ 0
    apply WithTop.coe_le_coe.mpr
    push_cast
    have hzero' : (0 : ℚ) ≤ b.order 0 := by exact_mod_cast hzero
    linarith
  · exact a.truncatedPrefixDefect_nonneg b 1 1 1

/-- The middle alpha is exactly `2e`. -/
theorem heADCExceptional_middleAlpha (a : GoodBONG q L 4)
    (ha : HeADCExceptionalQuaternaryOrders a) :
    a.alphaValue 1 = 2 * (ramificationIndex K : ℚ) := by
  dsimp only [HeADCExceptionalQuaternaryOrders] at ha
  have hgap : a.orderGap 1 = 2 * (ramificationIndex K : Int) := by
    simp [orderGap, ha]
  exact ((a.heADC2025Proposition33 1).compareTwoE.2.1).mp hgap

/-- With the split head, the full binary comparison defect retains every
target defect of depth at most `2e`. -/
theorem heADCExceptional_secondComparisonDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) (d : Nat)
    (hd : d ≤ 2 * ramificationIndex K)
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ)) :
    a.truncatedPrefixDefect b 1 2 2 = (d : ℚ) := by
  have hdom : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) <
      defectOrder (K := K) ((-1 : Kˣ) * a.prefixProduct 2) := by
    rw [hb, defectOrder_eq_top_of_isSquare hsplit]
    exact WithTop.coe_lt_top _
  have hraw := defectOrder_mul_eq_right_of_lt_left hdom
  have hproduct : ((-1 : Kˣ) * a.prefixProduct 2) *
      ((-1 : Kˣ) * b.prefixProduct 2) = a.prefixProduct 2 * b.prefixProduct 2 := by
    simp only [neg_one_mul, neg_mul_neg]
  rw [hproduct, hb] at hraw
  rw [truncatedPrefixDefect, one_mul, hraw, b.prefixAlphaCap_last,
    min_top_right, a.prefixAlphaCap_of_internal (by omega) (by omega)]
  change min ((d : ℚ) : WithTop ℚ) (a.alphaValue 1) = (d : ℚ)
  rw [a.heADCExceptional_middleAlpha ha, min_eq_left]
  apply WithTop.coe_le_coe.mpr
  exact_mod_cast hd

/-- The mixed prefix preceding the terminal test is capped by `beta_1=1`. -/
theorem heADCExceptional_previousDefect_le_one (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (hbeta : b.alphaValue 0 = 1) :
    a.truncatedPrefixDefect b (-1) 3 1 ≤ 1 := by
  have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
  rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
  simpa [hbeta] using hcap

/-- A binary profile `[0,1-d]` with the corresponding finite defect has
`beta_1=1`; the allowed defect is zero or odd, as in the maximal catalogue. -/
theorem alphaValue_zero_eq_one_of_finiteProfile (b : GoodBONG r M 2)
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hparity : d = 0 ∨ Odd d) (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 1 - (d : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ)) :
    b.alphaValue 0 = 1 := by
  have hgap : b.orderGap 0 = 1 - (d : Int) := by
    simp [orderGap, hbzero, hbone]
  have hone : b.prefixProduct 1 = b.valueUnit 0 := by
    calc
      b.prefixProduct 1 = b.prefixProduct 0 * b.valueUnit (0 : Fin 2) :=
        b.toBONG.prefixProduct_succ 0 (by omega)
      _ = b.valueUnit 0 := by
        unfold GoodBONG.prefixProduct
        rw [BONG.prefixProduct_zero, one_mul]
  have htwo : b.prefixProduct 2 = b.valueUnit 0 * b.valueUnit 1 := by
    calc
      b.prefixProduct 2 = b.prefixProduct 1 * b.valueUnit (1 : Fin 2) :=
        b.toBONG.prefixProduct_succ 1 (by omega)
      _ = b.valueUnit 0 * b.valueUnit 1 := by rw [hone]
  have hcapped : b.heADCAdjacentCappedDefect 0 = (d : ℚ) := by
    change b.truncatedPrefixDefect b (-1) 0 2 = (d : ℚ)
    rw [b.rankTwo_adjacentDefect_eq_defectOrder_signedProduct, ← htwo]
    simpa only [neg_one_mul] using hb
  apply (b.heADC2025Proposition34 0).alphaOne.mpr
  rcases hparity with rfl | hodd
  · left
    right
    simpa using hgap
  · by_cases hend : d = 2 * ramificationIndex K - 1
    · left
      left
      rw [hgap, hend]
      have he := ramificationIndex_pos (K := K)
      omega
    · right
      rcases hodd with ⟨z, hz⟩
      refine ⟨⟨-(z : Int), ?_⟩, ?_, ?_, ?_⟩
      · rw [hgap]
        omega
      · rw [hgap]
        have he := ramificationIndex_pos (K := K)
        omega
      · rw [hgap]
        omega
      · rw [hcapped, hgap]
        norm_num

/-- The second inequality in Theorem 3.6(ii) for a finite-defect target. -/
theorem heADCExceptional_secondDefect_of_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) (d : Nat)
    (hd : d ≤ 2 * ramificationIndex K)
    (hbone : b.order 1 = 1 - (d : Int)) (hbeta : b.alphaValue 0 = 1)
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (i : RepresentationIndex 4 2) (hi : i.val = 2) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 2 2 := by
  rw [a.heADCExceptional_secondComparisonDefect b ha hsplit d hd hb,
    coe_representationAlphaValue]
  apply (a.representationAlpha_le_primary b i).trans
  unfold representationPrimaryDefect
  simp only [hi]
  change (((a.order 2 - b.order 1 : Int) : ℚ) : WithTop ℚ) +
      a.truncatedPrefixDefect b (-1) 3 1 ≤ (d : ℚ)
  calc
    _ ≤ (((a.order 2 - b.order 1 : Int) : ℚ) : WithTop ℚ) + 1 :=
      add_le_add_right (a.heADCExceptional_previousDefect_le_one b hbeta) _
    _ = (d : ℚ) := by
      have haTwo : a.order 2 = 0 := ha 2
      rw [haTwo, hbone]
      norm_num

/-- The terminal full mixed defect is the target defect below the endpoint. -/
theorem heADCExceptional_terminalMixedDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (d : Nat) (hd : d < 2 * ramificationIndex K)
    (ha : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ)) :
    a.truncatedPrefixDefect b (-1) 4 2 = (d : ℚ) := by
  have hdom : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) <
      defectOrder (K := K) (a.prefixProduct 4) := by
    rw [ha, hb]
    apply WithTop.coe_lt_coe.mpr
    exact_mod_cast hd
  have hraw := defectOrder_mul_eq_right_of_lt_left hdom
  rw [hb] at hraw
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last, b.prefixAlphaCap_last, min_self, min_top_right]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw

/-- The terminal condition-(iii) trigger is impossible for every finite-defect target. -/
theorem heADCExceptional_terminalTrigger_not_of_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hbone : b.order 1 = 1 - (d : Int)) (hbeta : b.alphaValue 0 = 1)
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (i : CentralRepresentationIndex 4 2) (hi : i.val = 3) :
    ¬ a.centralDefectTrigger b i := by
  intro htrigger
  have hprevious := a.heADCExceptional_previousDefect_le_one b hbeta
  have hcurrent := a.heADCExceptional_terminalMixedDefect b d hd hfull hb
  have hsum : a.centralPreviousDefect b i + a.centralCurrentDefect b i ≤
      (1 : WithTop ℚ) + (d : ℚ) := by
    simp only [centralPreviousDefect, centralCurrentDefect, hi, hcurrent]
    simpa using add_le_add_left hprevious ((d : ℚ) : WithTop ℚ)
  have h := htrigger.2.trans_le hsum
  have haThree : a.order 3 = 2 - 2 * (ramificationIndex K : Int) := ha 3
  simp only [hi] at h
  change (((2 * (ramificationIndex K : ℚ) + (b.order 1 : ℚ) -
    (a.order 3 : ℚ) : ℚ)) : WithTop ℚ) <
      (1 : WithTop ℚ) + (d : ℚ) at h
  rw [hbone, haThree] at h
  have h' : 2 * (ramificationIndex K : ℚ) +
      ((1 - (d : Int) : Int) : ℚ) -
      ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) < 1 + (d : ℚ) := by
    exact WithTop.coe_lt_coe.mp (by simpa using h)
  push_cast at h'
  have hd' : (d : ℚ) ≤ 2 * (ramificationIndex K : ℚ) - 1 := by
    have hNat : d + 1 ≤ 2 * ramificationIndex K := hd
    have hRat : (d : ℚ) + 1 ≤ 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hNat
    linarith
  linarith

/-- A split binary head represents every unary prefix. -/
theorem heADCExceptional_firstCentralRepresentation (a : GoodBONG q L 4)
    (b : GoodBONG r M 2)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) :
    DiagonalRepresents (b.prefixValues 1 (by omega))
      (a.prefixValues 2 (by omega)) := by
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  have hsquare : IsSquare (-(a.valueUnit 0 * a.valueUnit 1)) := by
    simpa only [hproduct, neg_one_mul] using hsplit
  have hisotropic := (diagonalBinary_isotropic_iff_isSquare_neg_product
    (a.valueUnit 0) (a.valueUnit 1)).mpr hsquare
  have hrep := diagonalBinary_represents_of_isotropic
    (a.valueUnit 0) (a.valueUnit 1) (b.valueUnit 0) hisotropic
  convert hrep using 1
  · funext j
    fin_cases j
    rfl
  · funext j
    fin_cases j <;> rfl

/-- All four published representation conditions hold for a finite-defect
binary target with its proved terminal alpha value. -/
theorem heADCExceptional_represents_finite (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2))
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hbzero : b.order 0 = 0) (hbone : b.order 1 = 1 - (d : Int))
    (hbeta : b.alphaValue 0 = 1)
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (ambient : q.Represents r) : Lattice.Represents q r L M := by
  have hintegral : Lattice.IsIntegral r M :=
    b.toBONG.beliUniversalLemma22.mpr (by change 0 ≤ b.order 0; rw [hbzero])
  apply (heADC2025Theorem36Published (by omega) ambient a b).mpr
  refine ⟨a.heADCExceptional_orderCondition b ha hintegral, ?_, ?_,
    a.heADCExceptional_longConditions b ha hintegral⟩
  · intro i
    have hi : i.val = 1 ∨ i.val = 2 := by have := i.pos; have := i.le_small; omega
    rcases hi with hi | hi
    · simpa only [hi] using a.heADCExceptional_firstDefect b ha hintegral i hi
    · simpa only [hi] using a.heADCExceptional_secondDefect_of_finite b ha hsplit d
        hd.le hbone hbeta hb i hi
  · intro i htrigger
    have hi : i.val = 2 ∨ i.val = 3 := by
      have := i.one_lt
      have := i.le_small_succ
      omega
    rcases hi with hi | hi
    · rcases i with ⟨j, hj1, hj2, hj3⟩
      change j = 2 at hi
      subst j
      exact a.heADCExceptional_firstCentralRepresentation b hsplit
    · exact (a.heADCExceptional_terminalTrigger_not_of_finite b ha d hd hbone hbeta
        hfull hb i hi htrigger).elim

end BONG.GoodBONG

end Bong
