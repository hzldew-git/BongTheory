/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryConditions
import Bong.Bong.He2023ADCEvenMixedTests

/-!
# He (2025), Lemma 6.9

The two maximal binary spaces with the kappa parameter cannot both occur as
terminal prefix representations when the fourth order lies above `2-2e`.
The literal capped-defect trigger in Theorem 3.6(iii) exposes the contradiction.
-/

namespace Bong

open Dyadic Module

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The first three orders in Lemma 6.9. -/
def HeADCLemma69HeadOrders (a : GoodBONG q L 4) : Prop :=
  a.order 0 = 0 ∧
    a.order 1 = -(2 * (ramificationIndex K : Int)) ∧
      a.order 2 = 0

/-- The terminal condition-(iii) index in the binary comparison. -/
def heADCLemma69CentralIndex : CentralRepresentationIndex 4 2 where
  val := 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- At the terminal trigger, the first capped comparison defect is one. -/
theorem heADCLemma69_previousDefect (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCLemma69HeadOrders a)
    (hterminal : 2 - 2 * (ramificationIndex K : Int) < a.order 3)
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 2 - 2 * (ramificationIndex K : Int)) :
    a.centralPreviousDefect b heADCLemma69CentralIndex = 1 := by
  have halphaNe : a.alphaValue (2 : Fin 3) ≠ 0 := by
    intro halpha
    have hgap := (a.heADC2025Proposition34 (2 : Fin 3)).alphaZero.mp halpha
    change a.order 3 - a.order 2 = -(2 * (ramificationIndex K : Int)) at hgap
    rw [ha.2.2] at hgap
    omega
  have halpha : (1 : ℚ) ≤ a.alphaValue (2 : Fin 3) :=
    a.heHuOne_le_alphaValue_of_ne_zero 2 halphaNe
  have hbeta : b.alphaValue (0 : Fin 1) = 1 := by
    apply b.alphaValue_eq_one_of_orderGap_eq_endpoint 0
    left
    change b.order 1 - b.order 0 = 2 - 2 * (ramificationIndex K : Int)
    rw [hbzero, hbone]
    omega
  have hrawEven : Even (ordUnit K
      ((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1)) := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [ordUnit_mul, ordUnit_mul, ordUnit_neg, hone,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega)]
    simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
      BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
      BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
      BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4),
      BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 2)]
    change Even (0 + (0 + a.order 0 + a.order 1 + a.order 2) + (0 + b.order 0))
    rw [ha.1, ha.2.1, ha.2.2, hbzero]
    exact ⟨-(ramificationIndex K : Int), by ring⟩
  have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1) :=
    defectOrder_one_le_of_even _ hrawEven
  have haCap : (1 : WithTop ℚ) ≤ a.prefixAlphaCap 3 := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    exact_mod_cast halpha
  have hbCap : b.prefixAlphaCap 1 = (1 : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    change (b.alphaValue (0 : Fin 1) : WithTop ℚ) = 1
    rw [hbeta]
    norm_num
  unfold centralPreviousDefect truncatedPrefixDefect
  simp only [heADCLemma69CentralIndex]
  rw [hbCap]
  change min (defectOrder (K := K)
    ((-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1))
      (min (a.prefixAlphaCap 3) 1) = 1
  apply le_antisymm
  · exact (min_le_right _ _).trans (min_le_right _ _)
  exact le_min hraw (le_min haCap le_rfl)

/-- The two finite defects make the published terminal trigger strict. -/
theorem heADCLemma69_terminalTrigger (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCLemma69HeadOrders a)
    (hterminal : 2 - 2 * (ramificationIndex K : Int) < a.order 3)
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 2 - 2 * (ramificationIndex K : Int))
    (hcurrent : a.centralCurrentDefect b heADCLemma69CentralIndex =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    a.centralDefectTrigger b heADCLemma69CentralIndex := by
  constructor
  · change b.order 1 < a.order 3
    rw [hbone]
    exact hterminal
  · rw [a.heADCLemma69_previousDefect b ha hterminal hbzero hbone, hcurrent]
    change (((2 * (ramificationIndex K : ℚ) + (b.order 1 : ℚ) -
      (a.order 3 : ℚ) : ℚ) : WithTop ℚ)) <
        (1 : WithTop ℚ) + ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)
    rw [hbone]
    apply WithTop.coe_lt_coe.mpr
    push_cast
    have hterminal' : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) < a.order 3 := by
      exact_mod_cast hterminal
    linarith

/-- A represented binary target with the kappa defect must occur in the
first three source coordinates when the fourth order is above the endpoint. -/
theorem heADCLemma69_fullTargetPrefix_representation (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCLemma69HeadOrders a)
    (hterminal : 2 - 2 * (ramificationIndex K : Int) < a.order 3)
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 2 - 2 * (ramificationIndex K : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ))
    (hrep : Lattice.Represents q r L M) :
    DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (a.prefixValues 3 (by omega)) := by
  have he := ramificationIndex_pos (K := K)
  have hd : 2 * ramificationIndex K - 1 < 2 * ramificationIndex K := by omega
  have hcurrentRaw := a.heADCExceptional_terminalMixedDefect b
    (2 * ramificationIndex K - 1) hd hfull hb
  have hcurrent : a.centralCurrentDefect b heADCLemma69CentralIndex =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
    unfold centralCurrentDefect
    change a.truncatedPrefixDefect b (-1) 4 2 = _
    rw [hcurrentRaw]
    norm_num [Nat.cast_sub (by omega : 1 ≤ 2 * ramificationIndex K)]
  have hconditions :=
    (heADC2025Theorem36Published (by omega : 1 ≤ 3) hrep.ambient a b).mp hrep
  have hprefix := hconditions.centralRepresentations heADCLemma69CentralIndex
    (a.heADCLemma69_terminalTrigger b ha hterminal hbzero hbone hcurrent)
  change DiagonalRepresents (b.prefixValues 2 (by omega))
    (a.prefixValues 3 (by omega)) at hprefix
  have hbfull : b.prefixValues 2 (by omega) =
      diagonalUnitCoefficients b.valueUnit := by
    funext i
    rfl
  rw [hbfull] at hprefix
  exact hprefix

/-- Replace the target BONG coefficients by the published diagonal model. -/
theorem heADCLemma69_displayedTargetPrefix_representation
    (a : GoodBONG q L 4) (w : Fin 2 → Kˣ)
    (hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (heADCMaximalGoodBONG w).valueUnit)
      (a.prefixValues 3 (by omega))) :
    DiagonalRepresents (diagonalUnitCoefficients w)
      (a.prefixValues 3 (by omega)) := by
  have hmodel : DiagonalRepresents (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients (heADCMaximalGoodBONG w).valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      w (heADCMaximalGoodBONG w).valueUnit).mp
    exact ⟨(heADCMaximalGoodBONG w).toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  exact hmodel.trans hprefix

/-- He (2025), Lemma 6.9.  The ambient quaternary space and both represented
binary lattices are the named models appearing in the published statement. -/
theorem heADC2025Lemma69 (a : GoodBONG q L 4) (κ : Kˣ)
    (hunit : IsValuationUnit K (κ : K))
    (hκ : quadraticDefect K κ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞))
    (ha : HeADCLemma69HeadOrders a)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even 1
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)))
    (hrepOne : Lattice.Represents q
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 κ)) L
      (heADCN1Even 0 κ).lattice)
    (hrepTwo : Lattice.Represents q
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 κ
        (Or.inr (heADCKappaSharpDomain κ hκ).notSquare))) L
      (heADCN2Even 0 κ (Or.inr (heADCKappaSharpDomain κ hκ).notSquare)).lattice) :
    a.order 3 = -(2 * (ramificationIndex K : Int)) ∨
      a.order 3 = 2 - 2 * (ramificationIndex K : Int) := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let hs := heADCKappaSharpDomain κ hκ
  let hdefined : HeHuEvenSecondDefined 0 κ := Or.inr hs.notSquare
  let wOne := heADCW1Even 0 κ
  let wTwo := heADCW2Even 0 κ hdefined
  let bOne := heADCMaximalGoodBONG wOne
  let bTwo := heADCMaximalGoodBONG wTwo
  have he := ramificationIndex_pos (K := K)
  have hδ : defectOrder (K := K) δ =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    unfold defectOrder δ
    rw [show quadraticDefect K δ = (2 * ramificationIndex K : Nat) from
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) = _
    norm_num
  have hfullRaw := a.heADC_signedFullDefectOrder_of_ambient
    (heADCW1Even 1 δ) rfl 2 rfl δ ambient
      (heADCEvenFirst_determinantClass 1 δ)
  have hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    rw [hδ] at hfullRaw
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hfullRaw
  have hκOrder : defectOrder (K := K) κ =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ) :=
    Beli2009FinalRemarksProof.defectOrder_eq_natCast_of_quadraticDefect_eq
      (K := K) κ (2 * ramificationIndex K - 1) hκ
  have hprofileOne := (heADC2025Lemma411iiiUnitFirstPublished κ hunit hs 0 bOne
    (heHuOMaximalLattice_isOMaximal wOne).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  have hprofileTwo := (heADC2025Lemma411iiiUnitSecondPublished κ hunit hs 0 bTwo
    (heHuOMaximalLattice_isOMaximal wTwo).isIntegral
    (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  have hbOneZero : bOne.order 0 = 0 := by
    simpa [heADCMaximalOrderProfile, bOne, wOne] using hprofileOne 0
  have hbTwoZero : bTwo.order 0 = 0 := by
    simpa [heADCMaximalOrderProfile, bTwo, wTwo] using hprofileTwo 0
  have hbOneLast : bOne.order 1 = 2 - 2 * (ramificationIndex K : Int) := by
    have hlast := (heADCKappaTest_lastOrders 0 κ hunit hκ).1
    change bOne.order 1 = 2 - 2 * (ramificationIndex K : Int) at hlast
    exact hlast
  have hbTwoLast : bTwo.order 1 = 2 - 2 * (ramificationIndex K : Int) := by
    have hlast := (heADCKappaTest_lastOrders 0 κ hunit hκ).2
    change bTwo.order 1 = 2 - 2 * (ramificationIndex K : Int) at hlast
    exact hlast
  have hbOneRaw := bOne.heADC_signedFullDefectOrder_of_ambient wOne rfl 1 rfl κ
    (QuadraticSpace.isIsometric_refl _) (heADCEvenFirst_determinantClass 0 κ)
  have hbOne : defectOrder (K := K) ((-1 : Kˣ) * bOne.prefixProduct 2) =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ) := by
    rw [hκOrder] at hbOneRaw
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hbOneRaw
  have hbTwoRaw := bTwo.heADC_signedFullDefectOrder_of_ambient wTwo rfl 1 rfl κ
    (QuadraticSpace.isIsometric_refl _)
    (heADCEvenSecond_determinantClass 0 κ hdefined)
  have hbTwo : defectOrder (K := K) ((-1 : Kˣ) * bTwo.prefixProduct 2) =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ) := by
    rw [hκOrder] at hbTwoRaw
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hbTwoRaw
  have hupper : a.order 3 ≤ 2 - 2 * (ramificationIndex K : Int) := by
    by_contra hnot
    have hterminal : 2 - 2 * (ramificationIndex K : Int) < a.order 3 := by omega
    have hprefixOneRaw := a.heADCLemma69_fullTargetPrefix_representation bOne ha
      hterminal hfull hbOneZero hbOneLast hbOne hrepOne
    have hprefixTwoRaw := a.heADCLemma69_fullTargetPrefix_representation bTwo ha
      hterminal hfull hbTwoZero hbTwoLast hbTwo hrepTwo
    have hprefixOne := a.heADCLemma69_displayedTargetPrefix_representation wOne
      hprefixOneRaw
    have hprefixTwo := a.heADCLemma69_displayedTargetPrefix_representation wTwo
      hprefixTwoRaw
    have hexact := heADC2025Lemma45iCodimensionOne wOne wTwo
      (heHu2022Definition34Proposition35Even 0 κ hdefined)
      (a.prefixValueUnits 3 (by omega))
    simp only [HeHuRepresentsExactlyOne,
      a.diagonalUnitCoefficients_prefixValueUnits] at hexact
    exact hexact.elim (fun h ↦ h.2 hprefixTwo) (fun h ↦ h.1 hprefixOne)
  have hlowerRaw := a.orderGap_ge_neg_two_mul_e (2 : Fin 3)
  have hlower : -(2 * (ramificationIndex K : Int)) ≤ a.order 3 := by
    unfold orderGap at hlowerRaw
    change -(2 * (ramificationIndex K : Int)) ≤ a.order 3 - a.order 2 at hlowerRaw
    rw [ha.2.2] at hlowerRaw
    omega
  have hnotMiddle : a.order 3 ≠ 1 - 2 * (ramificationIndex K : Int) := by
    intro hmiddle
    have hodd : Odd (a.orderGap (2 : Fin 3)) := by
      refine ⟨-(ramificationIndex K : Int), ?_⟩
      unfold orderGap
      change a.order 3 - a.order 2 = _
      rw [ha.2.2, hmiddle]
      ring
    have hpositive := a.heADC2025Corollary32i (2 : Fin 3) hodd
    unfold orderGap at hpositive
    change 0 < a.order 3 - a.order 2 at hpositive
    rw [ha.2.2, hmiddle] at hpositive
    omega
  omega

end BONG.GoodBONG

end Bong
