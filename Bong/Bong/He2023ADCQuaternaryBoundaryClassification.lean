/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenSecondEndpointOrders
import Bong.Bong.He2023ADCEvenCorankTwoTests
import Bong.Bong.He2023ADCLemma69
import Bong.Bong.He2023ADCQuaternaryBoundaryNonThree
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.He2023ADCTheorem62Stable

/-!
# The corrected second-discriminant quaternary classification

The binary endpoint omitted by He (2025), Lemma 6.8(iv), is classified here.
An arbitrary quaternary 2-ADC lattice in `W_2^4(Delta)` is either maximal or
isometric to the independently constructed boundary lattice.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A defined second-column even model embeds in the model obtained by adjoining
one hyperbolic plane. -/
theorem heADCEvenSecond_represents_previous (k : Nat) (c : Kˣ)
    (hsmall : HeHuEvenSecondDefined k c)
    (hlarge : HeHuEvenSecondDefined (k + 1) c) :
    DiagonalRepresents (diagonalUnitCoefficients (heADCW2Even k c hsmall))
      (diagonalUnitCoefficients (heADCW2Even (k + 1) c hlarge)) := by
  have hprefix := DiagonalRepresents.prefixOfLE
    (diagonalUnitCoefficients
      (Fin.append (heADCW2Even k c hsmall) (heHuHyperbolicPair (K := K))))
    (by omega : 2 * k + 2 ≤ (2 * k + 2) + 2)
  have hsource : DiagonalRepresents
      (diagonalUnitCoefficients (heADCW2Even k c hsmall))
      (diagonalUnitCoefficients
        (Fin.append (heADCW2Even k c hsmall) (heHuHyperbolicPair (K := K)))) := by
    convert hprefix using 1
    funext i
    change (heADCW2Even k c hsmall i : K) =
      (Fin.append (heADCW2Even k c hsmall) (heHuHyperbolicPair (K := K))
        ⟨i.val, by omega⟩ : Kˣ)
    have hi : (⟨i.val, by omega⟩ : Fin ((2 * k + 2) + 2)) = Fin.castAdd 2 i := Fin.ext rfl
    rw [hi, Fin.append_left]
  exact hsource.trans (heHuEvenSecond_hyperbolicLift k c hsmall hlarge)

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The same-parameter smaller second-column maximal test inside a second-column
corank-two ambient model. -/
theorem heADCEvenCorankTwoSecond_same (k : Nat) (c : Kˣ)
    (hsmall : HeHuEvenSecondDefined k c)
    (hlarge : HeHuEvenSecondDefined (k + 1) c)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c hlarge))) :
    Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k c hsmall))
      L (heADCN2Even k c hsmall).lattice :=
  heADCMaximal_represents_of_ambient_model hADC _ _ ambient
    (heADCEvenSecond_represents_previous k c hsmall hlarge)

end Lattice

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type v} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {r : QuadraticSpace K W} {M : Lattice K W}

/-- The first three orders of the omitted second-column quaternary branch. -/
def HeADCQuaternaryBoundaryHeadOrders (a : GoodBONG q L 4) : Prop :=
  a.order 0 = 0 ∧
    a.order 1 = -(2 * (ramificationIndex K : Int)) ∧
      a.order 2 = 1

/-- The mixed prefix preceding the terminal binary comparison has defect zero. -/
theorem heADCBoundaryHead_previousDefect_zero
    (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryHeadOrders a) (hbzero : b.order 0 = 0) :
    a.centralPreviousDefect b heADCLemma69CentralIndex = 0 := by
  unfold centralPreviousDefect
  change a.truncatedPrefixDefect b (-1) 3 1 = 0
  apply a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b (-1) 3 1
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hneg : ordUnit K (-1 : Kˣ) = 0 := by rw [ordUnit_neg, hone]
  rw [ordUnit_mul, ordUnit_mul, hneg,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum 1 (by omega)]
  simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4),
    BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 2)]
  change Odd (0 + (0 + a.order 0 + a.order 1 + a.order 2) + (0 + b.order 0))
  rw [ha.1, ha.2.1, ha.2.2, hbzero]
  exact ⟨-(ramificationIndex K : Int), by ring⟩

/-- Above the boundary endpoint, a finite-defect maximal binary target triggers
the terminal prefix representation in Theorem 3.6(iii). -/
theorem heADCBoundaryHead_terminalTrigger
    (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryHeadOrders a)
    (hterminal : 3 - 2 * (ramificationIndex K : Int) < a.order 3)
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 2 - 2 * (ramificationIndex K : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ)) :
    a.centralDefectTrigger b heADCLemma69CentralIndex := by
  have he := ramificationIndex_pos (K := K)
  have hd : 2 * ramificationIndex K - 1 < 2 * ramificationIndex K := by omega
  have hcurrentRaw := a.heADCBoundary_terminalMixedDefect b
    (2 * ramificationIndex K - 1) hd hfull hb
  have hcurrent : a.centralCurrentDefect b heADCLemma69CentralIndex =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
    unfold centralCurrentDefect
    change a.truncatedPrefixDefect b (-1) 4 2 = _
    rw [hcurrentRaw]
    norm_num [Nat.cast_sub (by omega : 1 ≤ 2 * ramificationIndex K)]
  constructor
  · change b.order 1 < a.order 3
    rw [hbone]
    omega
  · rw [a.heADCBoundaryHead_previousDefect_zero b ha hbzero, hcurrent]
    change (((2 * (ramificationIndex K : ℚ) + (b.order 1 : ℚ) -
      (a.order 3 : ℚ) : ℚ) : WithTop ℚ)) <
        (0 : WithTop ℚ) + ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)
    rw [hbone]
    apply WithTop.coe_lt_coe.mpr
    push_cast
    have hterminal' : (3 : ℚ) - 2 * (ramificationIndex K : ℚ) < a.order 3 := by
      exact_mod_cast hterminal
    linarith

/-- The terminal trigger forces the whole maximal binary target into the first
three source coordinates. -/
theorem heADCBoundaryHead_fullTargetPrefix_representation
    (a : GoodBONG q L 4) (b : GoodBONG r M 2)
    (ha : HeADCQuaternaryBoundaryHeadOrders a)
    (hterminal : 3 - 2 * (ramificationIndex K : Int) < a.order 3)
    (hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 2 - 2 * (ramificationIndex K : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * ramificationIndex K - 1 : Nat) : ℚ) : WithTop ℚ))
    (hrep : Lattice.Represents q r L M) :
    DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (a.prefixValues 3 (by omega)) := by
  have hconditions :=
    (heADC2025Theorem36Published (by omega : 1 ≤ 3) hrep.ambient a b).mp hrep
  have hprefix := hconditions.centralRepresentations heADCLemma69CentralIndex
    (a.heADCBoundaryHead_terminalTrigger b ha hterminal hfull hbzero hbone hb)
  change DiagonalRepresents (b.prefixValues 2 (by omega))
    (a.prefixValues 3 (by omega)) at hprefix
  have hbfull : b.prefixValues 2 (by omega) =
      diagonalUnitCoefficients b.valueUnit := by
    funext i
    rfl
  rwa [hbfull] at hprefix

/-- The two kappa tests bound the fourth order by the new endpoint `3-2e`.
This is the shifted analogue of the argument in Lemma 6.9. -/
theorem heADCBoundaryHead_last_le (a : GoodBONG q L 4) (κ : Kˣ)
    (hunit : IsValuationUnit K (κ : K))
    (hκ : quadraticDefect K κ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞))
    (ha : HeADCQuaternaryBoundaryHeadOrders a)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1))))
    (hrepOne : Lattice.Represents q
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 κ)) L
      (heADCN1Even 0 κ).lattice)
    (hrepTwo : Lattice.Represents q
      (BONG.coefficientDiagonalSpace (heADCW2Even 0 κ
        (Or.inr (heADCKappaSharpDomain κ hκ).notSquare))) L
      (heADCN2Even 0 κ (Or.inr (heADCKappaSharpDomain κ hκ).notSquare)).lattice) :
    a.order 3 ≤ 3 - 2 * (ramificationIndex K : Int) := by
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
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
    (heADCW2Even 1 δ (heHuLemma43_evenSecondDefined (K := K) 1)) rfl 2 rfl δ
      ambient (heADCEvenSecond_determinantClass 1 δ _)
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
  by_contra hnot
  have hterminal : 3 - 2 * (ramificationIndex K : Int) < a.order 3 := by omega
  have hprefixOneRaw := a.heADCBoundaryHead_fullTargetPrefix_representation bOne ha
    hterminal hfull hbOneZero hbOneLast hbOne hrepOne
  have hprefixTwoRaw := a.heADCBoundaryHead_fullTargetPrefix_representation bTwo ha
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

/-- Complete order, square-class, and determinant data for an arbitrary
quaternary 2-ADC lattice in the second discriminant ambient space. -/
structure HeADCQuaternarySecondDiscriminantData (a : GoodBONG q L 4) : Prop where
  head : HeADCQuaternaryBoundaryHeadOrders a
  last : a.order 3 = 1 - 2 * (ramificationIndex K : Int) ∨
    a.order 3 = 3 - 2 * (ramificationIndex K : Int)
  splitHead : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)
  fullDefect : defectOrder (K := K) (a.prefixProduct 4) =
    (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ)

/-- The actual 2-ADC hypothesis forces precisely the maximal endpoint or the
new boundary endpoint. -/
theorem heADCQuaternarySecondDiscriminant_data
    (a : GoodBONG q L 4) (hADC : Lattice.IsNADC.{u, u, u} q L 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1)))) :
    HeADCQuaternarySecondDiscriminantData a := by
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let hsmall : HeHuEvenSecondDefined 0 δ := heHuLemma43_evenSecondDefined (K := K) 0
  let hlarge : HeHuEvenSecondDefined 1 δ := heHuLemma43_evenSecondDefined (K := K) 1
  let w := heADCW2Even 1 δ hlarge
  have hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ 2 * δ)) := by
    simpa only [w] using heADCEvenSecond_determinantClass 1 δ hlarge
  have lift (source : Fin 2 → Kˣ) (d : Kˣ)
      (hsource : IsSquare
        (diagonalUnitDeterminant source * ((-1 : Kˣ) ^ (0 + 1) * d)))
      (hd : ¬ IsSquare (d * δ)) :
      Lattice.Represents q (BONG.coefficientDiagonalSpace source) L
        (heHuOMaximalLattice source) :=
    Lattice.heADCMaximal_represents_of_ambient_model hADC source w ambient
      (heADCEvenCodimensionTwo_represents_of_parameter_not_square 0 rfl
        source w d δ hsource hclass hd)
  have hδnot : ¬ IsSquare ((1 : Kˣ) * δ) := by
    simpa only [one_mul] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  have hOne := lift (heADCW1Even 0 (1 : Kˣ)) 1
    (heADCEvenFirst_determinantClass (K := K) 0 1) hδnot
  have hDeltaSecond := Lattice.heADCEvenCorankTwoSecond_same 0 δ hsmall hlarge
    hADC ambient
  have he := ramificationIndex_pos (K := K)
  obtain ⟨κ, hunit, hκ⟩ := exists_unit_quadraticDefect_eq_odd (K := K)
    (2 * ramificationIndex K - 1) (by omega)
    ⟨ramificationIndex K - 1, by omega⟩ (by omega)
  let hs := heADCKappaSharpDomain κ hκ
  let hdefined : HeHuEvenSecondDefined 0 κ := Or.inr hs.notSquare
  have hκnot : ¬ IsSquare (κ * δ) :=
    heADCSharp_mul_discriminant_not_square κ hs
  have hKappaOne := lift (heADCW1Even 0 κ) κ
    (heADCEvenFirst_determinantClass (K := K) 0 κ) hκnot
  have hKappaTwo := lift (heADCW2Even 0 κ hdefined) κ
    (heADCEvenSecond_determinantClass (K := K) 0 κ hdefined)
    hκnot
  obtain ⟨_, hhead, hheadDefect⟩ :=
    a.heADC2025Lemma64i 0 1 (Or.inl rfl) hADC.isIntegral hOne
  obtain ⟨_, hnext⟩ := a.heADC2025Lemma64iv 0 κ hunit hκ hADC.isIntegral
    (Or.inl hOne) (Or.inl hKappaOne)
  have hfullRaw := a.heADC_signedFullDefectOrder_of_ambient w rfl 2 rfl δ
    ambient hclass
  have hδDefect : defectOrder (K := K) δ =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    unfold defectOrder δ
    rw [show quadraticDefect K δ = (2 * ramificationIndex K : Nat) from
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) = _
    norm_num
  have hfull : defectOrder (K := K) (a.prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    rw [hδDefect] at hfullRaw
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hfullRaw
  have hthird : a.order 2 = 1 := by
    by_contra hnot
    have heven : Even (a.order 2) := by
      rcases hnext with hzero | hone | htwo
      · have hzero' : a.order 2 = 0 := by simpa using hzero
        rw [hzero']
        exact Even.zero
      · exact False.elim (hnot hone)
      · have htwo' : a.order 2 = 2 := by simpa using htwo
        rw [htwo']
        exact ⟨1, rfl⟩
    have hAlpha : 2 - 2 * (ramificationIndex K : Int) ≤ a.order 3 →
        a.HeADCEvenCentralAlphaAlternatives 0 := by
      intro hR
      exact a.heADC2025Lemma67_endpoint 0 hADC.isIntegral hhead hR δ hsmall
        (Or.inr rfl) (Or.inl heven) hDeltaSecond
    have hfullLower : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (0 + 2)) := by
      rw [hfullRaw, hδDefect]
    have hpair := a.heADCSecondEndpoint_terminal_pair 0 hADC.isIntegral δ
      (Or.inr rfl) hlarge ambient hhead hnext hfullLower hAlpha
    exact hnot hpair.1
  have hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2) := by
    apply (quadraticDefect_eq_top_iff_isSquare K _).mp
    have hthird' : a.order ⟨2 * 0 + 2, by omega⟩ = 1 := by simpa using hthird
    have H := hheadDefect (by omega) (by rw [hthird']; omega)
    simpa [show 0 + 1 = 1 by omega, show 2 * 0 + 2 = 2 by omega] using H
  have hheadBoundary : HeADCQuaternaryBoundaryHeadOrders a := by
    exact ⟨by simpa using hhead 0, by simpa using hhead 1, hthird⟩
  have hupper := a.heADCBoundaryHead_last_le κ hunit hκ hheadBoundary ambient
    hKappaOne hKappaTwo
  have hlowerRaw := a.orderGap_ge_neg_two_mul_e (2 : Fin 3)
  have hlower : 1 - 2 * (ramificationIndex K : Int) ≤ a.order 3 := by
    unfold orderGap at hlowerRaw
    change -(2 * (ramificationIndex K : Int)) ≤ a.order 3 - a.order 2 at hlowerRaw
    rw [hthird] at hlowerRaw
    omega
  have hnotMiddle : a.order 3 ≠ 2 - 2 * (ramificationIndex K : Int) := by
    intro hmiddle
    have hodd : Odd (a.orderGap (2 : Fin 3)) := by
      refine ⟨-(ramificationIndex K : Int), ?_⟩
      unfold orderGap
      change a.order 3 - a.order 2 = _
      rw [hthird, hmiddle]
      ring
    have hpositive := a.heADC2025Corollary32i (2 : Fin 3) hodd
    unfold orderGap at hpositive
    change 0 < a.order 3 - a.order 2 at hpositive
    rw [hthird, hmiddle] at hpositive
    omega
  refine ⟨hheadBoundary, ?_, hsplit, hfull⟩
  omega

/-- The boundary order sequence has alpha profile `(0, 2e+1/2, 1)`. -/
theorem heADCBoundary_alphaProfile (a : GoodBONG q L 4)
    (ha : HeADCQuaternaryBoundaryOrders a) (i : Fin 3) :
    a.alphaValue i =
      (![0, 2 * (ramificationIndex K : ℚ) + 1 / 2, 1] : Fin 3 → ℚ) i := by
  fin_cases i
  · apply (a.heADC2025Proposition34 0).alphaZero.mpr
    unfold orderGap
    change a.order 1 - a.order 0 = _
    rw [ha 0, ha 1]
    norm_num
  · simpa using a.heADCBoundary_middleAlpha ha
  · apply (a.heADC2025Proposition34 2).alphaOne.mpr
    left
    left
    unfold orderGap
    change a.order 3 - a.order 2 = _
    rw [ha 2, ha 3]
    simp
    ring

/-- A split binary prefix has square signed coefficient ratio. -/
theorem signedRatioSquare_of_splitHead (a : GoodBONG q L 4)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) :
    IsSquare (-(a.valueUnit 0 / a.valueUnit 1)) := by
  have hsquare : IsSquare (a.valueUnit 1 ^ 2) :=
    ⟨a.valueUnit 1, by rw [pow_two]⟩
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  have h := hsplit.div hsquare
  rw [hproduct] at h
  simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- Condition (iii) of Beli's classification theorem for the boundary model. -/
theorem heADCBoundary_prefixDefectBounds (a : GoodBONG q L 4)
    (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) :
    a.PrefixDefectBounds (heADCQuaternaryBoundaryCandidate (K := K)) := by
  let c := heADCQuaternaryBoundaryCandidate (K := K)
  intro i
  fin_cases i
  · change (a.alphaValue 0 : WithTop ℚ) ≤ comparisonPrefixDefect a c 1
    rw [a.heADCBoundary_alphaProfile ha 0]
    unfold comparisonPrefixDefect
    exact defectOrder_nonneg _
  · change (a.alphaValue 1 : WithTop ℚ) ≤ comparisonPrefixDefect a c 2
    have hcandidate := heADCQuaternaryBoundaryCandidate_splitHead (K := K)
    have hsquare : IsSquare (a.prefixProduct 2 * c.prefixProduct 2) := by
      have h := hsplit.mul hcandidate
      simpa [neg_one_mul] using h
    unfold comparisonPrefixDefect comparisonPrefixUnit
    rw [defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · change (a.alphaValue 2 : WithTop ℚ) ≤ comparisonPrefixDefect a c 3
    rw [a.heADCBoundary_alphaProfile ha 2]
    have haOdd : Odd (ordUnit K (a.prefixProduct 3)) := by
      rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega)]
      simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4)]
      change Odd (0 + a.order 0 + a.order 1 + a.order 2)
      rw [ha 0, ha 1, ha 2]
      simp
    have hcOdd : Odd (ordUnit K (c.prefixProduct 3)) := by
      rw [c.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega)]
      simp only [BeliOrderSequence.prefixSum_succ, BeliOrderSequence.prefixSum_zero,
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 0 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 1 < 4),
        BeliOrderSequence.entryOrZero_of_lt _ (by decide : 2 < 4)]
      change Odd (0 + c.order 0 + c.order 1 + c.order 2)
      rw [heADCQuaternaryBoundaryCandidate_orders,
        heADCQuaternaryBoundaryCandidate_orders,
        heADCQuaternaryBoundaryCandidate_orders]
      simp
    unfold comparisonPrefixDefect comparisonPrefixUnit
    apply defectOrder_one_le_of_even
    rw [ordUnit_mul]
    exact haOdd.add_odd hcOdd

/-- Condition (iv) of Beli's classification theorem for the boundary model. -/
theorem heADCBoundary_internalRepresentations (a : GoodBONG q L 4)
    (_ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2)) :
    a.InternalRepresentationConditions
      (heADCQuaternaryBoundaryCandidate (K := K)) := by
  let c := heADCQuaternaryBoundaryCandidate (K := K)
  intro i hi _htrigger
  fin_cases i
  · norm_num at hi
  · have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
      unfold GoodBONG.prefixProduct
      rw [a.toBONG.prefixProduct_succ 1 (by omega),
        a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
      rfl
    have hsquare : IsSquare (-(a.valueUnit 0 * a.valueUnit 1)) := by
      simpa only [hproduct, neg_one_mul] using hsplit
    have hisotropic := (diagonalBinary_isotropic_iff_isSquare_neg_product
      (a.valueUnit 0) (a.valueUnit 1)).mpr hsquare
    have hrep := diagonalBinary_represents_of_isotropic
      (a.valueUnit 0) (a.valueUnit 1) (c.valueUnit 0) hisotropic
    convert hrep using 1
    · funext j
      fin_cases j
      rfl
    · funext j
      fin_cases j <;> rfl
  · have hpair :=
      QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
        (c.valueUnit 0) (c.valueUnit 1) (a.valueUnit 0) (a.valueUnit 1)
        (c.signedRatioSquare_of_splitHead
          (heADCQuaternaryBoundaryCandidate_splitHead (K := K)))
        (a.signedRatioSquare_of_splitHead hsplit)
    have hprefix : DiagonalRepresents (c.prefixValues 2 (by omega))
        (a.prefixValues 2 (by omega)) := by
      convert hpair using 1 <;> funext j <;> fin_cases j <;> rfl
    exact hprefix.trans (a.prefixValues_represents_succ 2 (by omega))

/-- A boundary-profile lattice in the second discriminant space is the
constructed boundary lattice, not merely another lattice with the same orders. -/
theorem heADCBoundary_isometric (a : GoodBONG q L 4)
    (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1)))) :
    Lattice.IsIsometric q (heADCQuaternaryBoundaryForm (K := K)) L
      (heADCQuaternaryBoundaryLattice (K := K)) := by
  let c := heADCQuaternaryBoundaryCandidate (K := K)
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hfirst : 0 ≤ a.order 0 := by
    rw [ha 0]
    norm_num
  have hIntegral : Lattice.IsIntegral q L :=
    (a.toBONG.beliUniversalLemma22).2 hfirst
  have hcAmbient : (heADCQuaternaryBoundaryForm (K := K)).IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even 1 δ
        (heHuLemma43_evenSecondDefined (K := K) 1))) :=
    c.ambientIsometric_of_diagonalRepresents _ rfl
      (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hacAmbient : q.IsIsometric (heADCQuaternaryBoundaryForm (K := K)) :=
    ⟨(Classical.choice ambient).trans (Classical.choice hcAmbient).symm⟩
  apply (a.beli2009Theorem31_concrete hacAmbient c).mpr
  refine
    { sameOrders := ?_
      sameAlphas := ?_
      prefixDefectBounds := a.heADCBoundary_prefixDefectBounds ha hsplit
      internalRepresentations := a.heADCBoundary_internalRepresentations ha hsplit }
  · intro i
    rw [ha i, heADCQuaternaryBoundaryCandidate_orders]
  · intro i
    rw [a.heADCBoundary_alphaProfile ha i,
      c.heADCBoundary_alphaProfile
        (heADCQuaternaryBoundaryCandidate_hasOrders (K := K)) i]

/-- Corrected classification of the second-discriminant branch at `n=2`. -/
theorem heADCQuaternarySecondDiscriminant_classification
    (a : GoodBONG q L 4) (hADC : Lattice.IsNADC.{u, u, u} q L 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1)))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1))) L
        (heADCN2Even 1 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) 1)).lattice ∨
      Lattice.IsIsometric q (heADCQuaternaryBoundaryForm (K := K)) L
        (heADCQuaternaryBoundaryLattice (K := K)) := by
  have D := a.heADCQuaternarySecondDiscriminant_data hADC ambient
  rcases D.last with hmaximal | hboundary
  · left
    apply (heADC2025Lemma411iiDeltaPublished 1 a hADC.isIntegral ambient).mpr
    intro i
    fin_cases i <;>
      simp [heADCMaximalOrderProfile, D.head.1, D.head.2.1, D.head.2.2, hmaximal]
  · right
    apply a.heADCBoundary_isometric _ D.splitHead ambient
    intro i
    fin_cases i <;>
      simp [D.head.1, D.head.2.1, D.head.2.2, hboundary]

end BONG.GoodBONG

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Corrected second-discriminant quaternary classification, stated for an
arbitrary actual 2-ADC lattice. -/
theorem heADCQuaternarySecondDiscriminantClassification
    (hADC : IsNADC.{u, u, u} q L 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1)))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1))) L
        (heADCN2Even 1 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
          (heHuLemma43_evenSecondDefined (K := K) 1)).lattice ∨
      IsIsometric q (BONG.GoodBONG.heADCQuaternaryBoundaryForm (K := K)) L
        (BONG.GoodBONG.heADCQuaternaryBoundaryLattice (K := K)) := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 4)
  exact a.heADCQuaternarySecondDiscriminant_classification hADC ambient

/-- Corrected complete rank-four classification at the binary ADC boundary.
The two nonmaximal isometry classes are both realized and independently
proved 2-ADC elsewhere in this development. -/
theorem heADC2025Theorem62_binary_corrected
    (hADC : IsNADC.{u, u, u} q L 2) (hrank : finrank K V = 4) :
    IsOMaximal q L ∨
      IsIsometric q (BONG.GoodBONG.heADCExceptionalQuaternaryForm (K := K)) L
        (BONG.GoodBONG.heADCExceptionalQuaternaryLattice (K := K)) ∨
      IsIsometric q (BONG.GoodBONG.heADCQuaternaryBoundaryForm (K := K)) L
        (BONG.GoodBONG.heADCQuaternaryBoundaryLattice (K := K)) := by
  let a := (BONG.GoodBONG.ofLattice q L).castLength hrank
  rcases heADC2025Proposition42iiEven (K := K) 1 a.valueUnit with
    ⟨c, hfirst | ⟨hdefined, hsecond⟩⟩
  · have ambient : q.IsIsometric
        (BONG.coefficientDiagonalSpace (heADCW1Even 1 c)) :=
      a.ambientIsometric_of_diagonalRepresents _ rfl hfirst
    by_cases hsquare : IsSquare c
    · obtain ⟨s, hs⟩ := hsquare
      have hc : c = (1 : Kˣ) * s ^ 2 := by
        simpa only [one_mul, pow_two] using hs
      have ambientOne := heADCEvenFirst_ambient_of_parameter_mul_square
        1 c 1 s hc ambient
      have hiso := heADC2025Lemma68i 0 hADC ambientOne
      exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
        (Classical.choice hiso).symm)
    · let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      by_cases hdelta : IsSquare (c / δ)
      · obtain ⟨s, hs⟩ := hdelta
        have hc : c = δ * s ^ 2 := by
          calc
            c = (c / δ) * δ := (div_mul_cancel c δ).symm
            _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
        have ambientDelta := heADCEvenFirst_ambient_of_parameter_mul_square
          1 c δ s hc ambient
        rcases heADC2025Lemma611 hADC ambientDelta with hmaximal | hexceptional
        · exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hmaximal).symm)
        · exact Or.inr (Or.inl hexceptional)
      · have hs : HeHuSharpDomain c := ⟨hsquare, hdelta⟩
        have hiso := heADC2025Lemma68v 0 c hs hADC ambient
        exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
          (Classical.choice hiso).symm)
  · have ambient : q.IsIsometric
        (BONG.coefficientDiagonalSpace (heADCW2Even 1 c hdefined)) :=
      a.ambientIsometric_of_diagonalRepresents _ rfl hsecond
    by_cases hsquare : IsSquare c
    · obtain ⟨s, hs⟩ := hsquare
      have hc : c = (1 : Kˣ) * s ^ 2 := by
        simpa only [one_mul, pow_two] using hs
      have ambientOneRaw := heADCEvenSecond_ambient_of_parameter_mul_square
        1 c 1 s hdefined hc ambient
      have ambientOne : q.IsIsometric (BONG.coefficientDiagonalSpace
          (heADCW2Even 1 (1 : Kˣ) (Or.inl (by omega)))) := by
        simpa only [] using ambientOneRaw
      have hiso := heADC2025Lemma68iii 0 hADC ambientOne
      exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
        (Classical.choice hiso).symm)
    · let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      by_cases hdelta : IsSquare (c / δ)
      · obtain ⟨s, hs⟩ := hdelta
        have hc : c = δ * s ^ 2 := by
          calc
            c = (c / δ) * δ := (div_mul_cancel c δ).symm
            _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
        have ambientDeltaRaw := heADCEvenSecond_ambient_of_parameter_mul_square
          1 c δ s hdefined hc ambient
        have ambientDelta : q.IsIsometric (BONG.coefficientDiagonalSpace
            (heADCW2Even 1 δ (heHuLemma43_evenSecondDefined (K := K) 1))) := by
          simpa only [] using ambientDeltaRaw
        rcases heADCQuaternarySecondDiscriminantClassification hADC ambientDelta with
          hmaximal | hboundary
        · exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hmaximal).symm)
        · exact Or.inr (Or.inr hboundary)
      · have hs : HeHuSharpDomain c := ⟨hsquare, hdelta⟩
        have ambientSharp : q.IsIsometric (BONG.coefficientDiagonalSpace
            (heADCW2Even 1 c (Or.inr hs.notSquare))) := by
          simpa only [] using ambient
        have hiso := heADC2025Lemma68vi 0 c hs hADC ambientSharp
        exact Or.inl ((heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
          (Classical.choice hiso).symm)

end Lattice

end Bong
