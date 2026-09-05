/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma712
import Bong.Bong.He2023ADCLemma76
import Bong.Bong.He2023ADCEvenFirstDefects
import Bong.Bong.He2023ADCPublishedProfiles
import Bong.Bong.He2023ADCPublishedRepresentation
import Bong.Bong.HeHu2022Lemma59
import Bong.Bong.HeHu2022PublishedTestingSet

/-!
# He (2025), Lemma 7.13

The published proof assumes that one source prefix represents both displayed
targets and therefore establishes simultaneous nonrepresentation, rather than
separate nonrepresentation of each target.  This file exposes that corrected
quantifier structure.  The parity-cycle strengthening of He--Hu, Lemma 5.9(ii)
also supplies the second-column version without repeating the Hilbert-symbol
calculation.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- If the first entries of two determinant-class pairs are complementary
codimension-one tests, then their second entries are complementary as well. -/
theorem heADC_exactlyOne_second_of_first {n : Nat}
    (firstC secondC firstD secondD : Fin n → Kˣ)
    (target : Fin (n + 1) → Kˣ)
    (pairC : HeHuSpacePairProperties firstC secondC)
    (pairD : HeHuSpacePairProperties firstD secondD)
    (hfirst : HeHuRepresentsExactlyOne firstC firstD target) :
    HeHuRepresentsExactlyOne secondC secondD target := by
  have hC := heHu2022Lemma313CodimensionOne firstC secondC pairC target
  have hD := heHu2022Lemma313CodimensionOne firstD secondD pairD target
  unfold HeHuRepresentsExactlyOne at hfirst hC hD ⊢
  tauto

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The terminal central index `i=n+1` for `n=2*k+3` and source rank
`n+2`. -/
def heADC2025Lemma713CentralIndex (k : Nat) :
    CentralRepresentationIndex (2 * k + 5) (2 * k + 3) where
  val := 2 * k + 4
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- The last maximal-test order is strictly below the final source order.
This is the terminal-rank form of equation (5.2) and Remark 5.2; unlike
He--Hu, Lemma 5.9, it does not require a further source coefficient. -/
theorem heADC2025Lemma713_boundaryOrder_gt_gapParity
    (a : GoodBONG q L (2 * k + 5))
    (hIntegral : Lattice.IsIntegral q L)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    (if Even (a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
      a.order ⟨2 * k + 4, by omega⟩ := by
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
  have hcases :
      (a.order ⟨2 * k + 3, by omega⟩ = 1 ∧
          a.order ⟨2 * k + 4, by omega⟩ = 1) ∨
        1 < a.order ⟨2 * k + 4, by omega⟩ := by
    rcases hTrigger with hpenultimate | hlast
    · have hge := a.heHu2022Remark52_order_ge_one
        (n := 2 * k + 3) (by omega) hodd (by omega) hIntegral hpenultimate
      rcases lt_or_eq_of_le hge with hgt | heq
      · exact Or.inr hgt
      · exact Or.inl ⟨hpenultimate, heq.symm⟩
    · exact Or.inr hlast
  by_cases heven : Even (a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩)
  · rw [if_pos heven]
    rcases hcases with hboth | hlarge <;> omega
  · rw [if_neg heven]
    rcases hcases with hboth | hlarge
    · exfalso
      apply heven
      rw [hboth.1, hboth.2, sub_self]
      exact Even.zero
    · exact hlarge

/-- The two terminal inequalities which activate revised condition (iii').
The right-hand side is bounded below by `2e`, while the strict last-order
inequality makes the left-hand side strictly smaller than `2e`. -/
theorem heADC2025Lemma713_defectTrigger_of_terminal_bounds
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hlast : b.order ⟨2 * k + 2, by omega⟩ =
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1))
    (hboundary :
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1) <
        a.order ⟨2 * k + 4, by omega⟩)
    (hprevious :
      a.centralPreviousDefect b (heADC2025Lemma713CentralIndex k) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))
    (hcurrent :
      ((((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
            WithTop ℚ) ≤
        a.centralCurrentDefect b (heADC2025Lemma713CentralIndex k)) :
    a.centralDefectTrigger b (heADC2025Lemma713CentralIndex k) := by
  let s : Int := if Even (a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩) then 0 else 1
  have hs : s < a.order ⟨2 * k + 4, by omega⟩ := by
    simpa only [s] using hboundary
  have hsQ : (s : ℚ) < (a.order ⟨2 * k + 4, by omega⟩ : ℚ) := by
    exact_mod_cast hs
  have hleftLt :
      2 * (ramificationIndex K : ℚ) + (s : ℚ) -
          (a.order ⟨2 * k + 4, by omega⟩ : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
    linarith
  have hsum :
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) ≤
        a.centralPreviousDefect b (heADC2025Lemma713CentralIndex k) +
          a.centralCurrentDefect b (heADC2025Lemma713CentralIndex k) := by
    rw [hprevious]
    calc
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) =
          (((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ)) +
            (((((2 * (ramificationIndex K : Int) +
              a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
                WithTop ℚ)) := by
          rw [← WithTop.coe_add]
          congr 1
          push_cast
          ring
      _ ≤ _ := by
        simpa only [add_comm] using
          add_le_add_left hcurrent
            (((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ))
  unfold centralDefectTrigger
  have hsub : 2 * k + 4 - 2 = 2 * k + 2 := by omega
  simp only [heADC2025Lemma713CentralIndex, hsub]
  constructor
  · rw [hlast]
    exact hboundary
  · rw [hlast]
    have hcoeLt :
        ((2 * (ramificationIndex K : ℚ) + (s : ℚ) -
            (a.order ⟨2 * k + 4, by omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
          (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) :=
      WithTop.coe_lt_coe.mpr hleftLt
    exact hcoeLt.trans_le hsum

/-- The literal maximal first-column target used in Lemma 7.13 has the
published odd-dimensional ambient space after square-class normalization. -/
theorem heADC2025Lemma713_firstTarget_represents_oddFirst
    (x : Kˣ) (k : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma59Target (K := K) x k).valueUnit)
      (diagonalUnitCoefficients
        (heHuOddFirst k (heHuLemma59NormalizedParameter (K := K) x))) := by
  let c := heHuLemma59NormalizedParameter (K := K) x
  let raw := heHu2022Lemma310BONG
    (BONG.unaryModelGoodBONG c) (heHuLemma59UnaryIntegral x) (k + 1)
  have hraw := heADCUnaryTower_represents_oddFirst
    c (heHuLemma59UnaryIntegral x) k
  have hcast := heHuLemma43_diagonalRepresents_castLengths
    (by omega : 1 + 2 * (k + 1) = 2 * k + 3)
    (rfl : 2 * k + 3 = 2 * k + 3) hraw
  change DiagonalRepresents
    (diagonalUnitCoefficients
      (raw.castLength (by omega : 1 + 2 * (k + 1) = 2 * k + 3)).valueUnit)
    (diagonalUnitCoefficients (heHuOddFirst k c))
  convert hcast using 1 <;> funext i
  · simp only [diagonalUnitCoefficients,
      BONG.GoodBONG.valueUnit_castLength_heHu]
    congr 1
  · simp only [diagonalUnitCoefficients, heADCW1Odd]
    congr 1

/-- The literal first-column target is `O`-maximal. -/
theorem heADC2025Lemma713_firstTarget_isOMaximal (x : Kˣ) (k : Nat) :
    Lattice.IsOMaximal
      (Lattice.halfHyperbolicExtensionForm
        (QuadraticSpace.rescaleUnit
          (heHuLemma59NormalizedParameter (K := K) x)
          (QuadraticSpace.line K)) (k + 1))
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.unaryModelLattice (K := K)) (k + 1)) := by
  let tail := BONG.unaryModelGoodBONG
    (heHuLemma59NormalizedParameter (K := K) x)
  have htail : Lattice.IsOMaximal _ _ :=
    heHuRankOne_isOMaximal_of_order_le_one tail
      (heHuLemma59UnaryIntegral x) (by
        simpa only [tail, BONG.unaryModelGoodBONG_order,
          heHuLemma59NormalizedParameter_order] using
            heHuLemma59Parity_le_one (K := K) x)
  exact htail.halfHyperbolicExtension (k + 1)

/-- The canonical second-column maximal good BONG diagonalizes the
published second odd row with the normalized parameter. -/
theorem heADC2025Lemma713_secondTarget_represents_oddSecond
    (x : Kˣ) (k : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heADCMaximalGoodBONG
          (heADCW2Odd k
            (heHuLemma59NormalizedParameter (K := K) x))).valueUnit)
      (diagonalUnitCoefficients
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) x))) := by
  let b := heADCMaximalGoodBONG
    (heADCW2Odd (K := K) k (heHuLemma59NormalizedParameter (K := K) x))
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    b.valueUnit
      (heADCW2Odd (K := K) k
        (heHuLemma59NormalizedParameter (K := K) x))).mp
    ⟨b.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩

/-- At the terminal index the literal first-column target has no remaining
alpha cap, so its current defect is the raw determinant defect. -/
theorem heADC2025Lemma713_firstTarget_centralCurrentDefect_eq
    (a : GoodBONG q L (2 * k + 5)) (x : Kˣ) :
    a.centralCurrentDefect (heHuLemma59Target (K := K) x k)
        (heADC2025Lemma713CentralIndex k) =
      defectOrder (K := K) (heHuLemma59C a k * x) := by
  unfold centralCurrentDefect truncatedPrefixDefect
  change min
      (defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          (heHuLemma59Target (K := K) x k).prefixProduct (2 * k + 3)))
      (min (a.prefixAlphaCap (2 * k + 5))
        ((heHuLemma59Target (K := K) x k).prefixAlphaCap (2 * k + 3))) = _
  rw [a.prefixAlphaCap_last,
    (heHuLemma59Target (K := K) x k).prefixAlphaCap_last,
    min_top_right, min_top_right]
  exact heHuLemma59_currentMixed_defectOrder_eq a k x

/-- The first literal test at `c` has infinite terminal current defect. -/
theorem heADC2025Lemma713_firstTarget_centralCurrentDefect_C
    (a : GoodBONG q L (2 * k + 5)) :
    a.centralCurrentDefect
        (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
        (heADC2025Lemma713CentralIndex k) = ⊤ := by
  rw [a.heADC2025Lemma713_firstTarget_centralCurrentDefect_eq]
  apply defectOrder_eq_top_of_isSquare
  exact ⟨heHuLemma59C a k, rfl⟩

/-- The second literal test at `c*u` has terminal current defect `d(u)`. -/
theorem heADC2025Lemma713_firstTarget_centralCurrentDefect_C_mul
    (a : GoodBONG q L (2 * k + 5)) (u : Kˣ) :
    a.centralCurrentDefect
        (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
        (heADC2025Lemma713CentralIndex k) = defectOrder (K := K) u := by
  rw [a.heADC2025Lemma713_firstTarget_centralCurrentDefect_eq]
  calc
    defectOrder (K := K) (heHuLemma59C a k * (heHuLemma59C a k * u)) =
        defectOrder (K := K) (u * heHuLemma59C a k ^ 2) := by
      congr 1
      simp only [pow_two]
      ac_rfl
    _ = defectOrder (K := K) u := defectOrder_mul_square u (heHuLemma59C a k)

/-- The canonical maximal good BONG on the second published odd space is
paired with the literal first-column target. -/
theorem heADC2025Lemma713_secondTarget_pair (x : Kˣ) (k : Nat) :
    HeHuSpacePairProperties
      (heHuLemma59Target (K := K) x k).valueUnit
      (heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) x))).valueUnit := by
  let c := heHuLemma59NormalizedParameter (K := K) x
  let b := heADCMaximalGoodBONG (heADCW2Odd (K := K) k c)
  have hfirst := heADC2025Lemma713_firstTarget_represents_oddFirst
    (K := K) x k
  have hsecond : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW2Odd (K := K) k c)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      b.valueUnit (heADCW2Odd (K := K) k c)).mp
        ⟨b.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
  exact _root_.Bong.BONG.GoodBONG.HeHuSpacePairProperties.transport
    (heADC2025Proposition42iOdd (K := K) k c)
    (by simpa only [c] using hfirst) hsecond

/-- The final order of the canonical second-column maximal target is the
same normalized parity as the first-column target. -/
theorem heADC2025Lemma713_secondTarget_lastOrder (x : Kˣ) (k : Nat) :
    (heADCMaximalGoodBONG
      (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) x))).order
        ⟨2 * k + 2, by omega⟩ = heHuLemma59Parity (K := K) x := by
  let δ := normalizedUnitPart K x
  have hδ : IsValuationUnit K (δ : K) := by
    simpa only [δ] using normalizedUnitPart_isValuationUnit K x
  by_cases hx : Even (ordUnit K x)
  · have hparity : heHuLemma59Parity (K := K) x = 0 :=
      heHuLemma59Parity_eq_zero_of_even x hx
    have hnormalized : heHuLemma59NormalizedParameter (K := K) x = δ := by
      rw [heHuLemma59NormalizedParameter, hparity]
      simp only [uniformizerPowerUnit, zpow_zero, mul_one, δ]
    rw [hnormalized, hparity]
    let b := (heADCMaximalGoodBONG (heADCW2Odd (K := K) k δ)).castLength
      (by omega : 2 * k + 3 = 3 + 2 * k)
    have hprofile := (heADC2025Lemma412iiPublished δ hδ k b
      (heHuOMaximalLattice_isOMaximal _).isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp
        (Lattice.isIsometric_refl _ _)
    have h := hprofile ⟨2 * k + 2, by omega⟩
    have hlast : b.order ⟨2 * k + 2, by omega⟩ = 0 := by
      simpa [heADCMaximalOrderProfile] using h
    simpa only [b, order_castLength] using hlast
  · have hparity : heHuLemma59Parity (K := K) x = 1 :=
      heHuLemma59Parity_eq_one_of_not_even x hx
    have hnormalized : heHuLemma59NormalizedParameter (K := K) x =
        δ * uniformizerPowerUnit K 1 := by
      rw [heHuLemma59NormalizedParameter, hparity]
    rw [hnormalized, hparity]
    let b := (heADCMaximalGoodBONG
      (heADCW2Odd (K := K) k (δ * uniformizerPowerUnit K 1))).castLength
        (by omega : 2 * k + 3 = 3 + 2 * k)
    have hprofile := (heADC2025Lemma412iiiSecondPublished δ hδ k b
      (heHuOMaximalLattice_isOMaximal _).isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp
        (Lattice.isIsometric_refl _ _)
    have h := hprofile ⟨2 * k + 2, by omega⟩
    have hlast : b.order ⟨2 * k + 2, by omega⟩ = 1 := by
      simpa [heADCMaximalOrderProfile] using h
    simpa only [b, order_castLength] using hlast

/-- The signed full determinant `c` in Lemma 7.13 places the source
ambient space in exactly one of the two published odd rows with parameter
`c`. -/
theorem heADC2025Lemma713_sourceAmbient
    (a : GoodBONG q L (2 * k + 5)) :
    q.IsIsometric (BONG.coefficientDiagonalSpace
        (heADCW1Odd (k + 1) (heHuLemma59C a k))) ∨
      q.IsIsometric (BONG.coefficientDiagonalSpace
        (heADCW2Odd (k + 1) (heHuLemma59C a k))) := by
  let c : Kˣ := (-1 : Kˣ) ^ (k + 2) *
    diagonalUnitDeterminant a.valueUnit
  have hdet : diagonalUnitDeterminant a.valueUnit =
      a.prefixProduct (2 * k + 5) := by
    rw [← a.diagonalUnitDeterminant_prefixValueUnits (2 * k + 5) le_rfl]
    congr 1
  have hc : c = heHuLemma59C a k := by
    dsimp only [c]
    rw [hdet]
    rfl
  have hsquare : IsSquare
      (diagonalUnitDeterminant a.valueUnit *
        diagonalUnitDeterminant (heADCW1Odd (K := K) (k + 1) c)) := by
    refine ⟨c, ?_⟩
    rw [diagonalUnitDeterminant_heHuOddFirst]
    simp only [c]
    ac_rfl
  rcases (heADC2025Proposition42iOdd (K := K) (k + 1) c).exhaustive
      a.valueUnit hsquare with hfirst | hsecond
  · have hspace := a.ambientIsometric_of_diagonalRepresents
      (heADCW1Odd (K := K) (k + 1) c) rfl hfirst
    rw [hc] at hspace
    exact Or.inl hspace
  · have hspace := a.ambientIsometric_of_diagonalRepresents
      (heADCW2Odd (K := K) (k + 1) c) rfl hsecond
    rw [hc] at hspace
    exact Or.inr hspace

/-- The coefficient-level form of `heADC2025Lemma713_sourceAmbient`.
It is the convenient transitive bridge from either published large row to
the source good BONG. -/
theorem heADC2025Lemma713_sourceDiagonal
    (a : GoodBONG q L (2 * k + 5)) :
    DiagonalRepresents
        (diagonalUnitCoefficients
          (heHuFinFamilyCast
            (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW1Odd (K := K) (k + 1) (heHuLemma59C a k))))
        (diagonalUnitCoefficients a.valueUnit) ∨
      DiagonalRepresents
        (diagonalUnitCoefficients
          (heHuFinFamilyCast
            (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW2Odd (K := K) (k + 1) (heHuLemma59C a k))))
        (diagonalUnitCoefficients a.valueUnit) := by
  let c : Kˣ := (-1 : Kˣ) ^ (k + 2) *
    diagonalUnitDeterminant a.valueUnit
  have hdet : diagonalUnitDeterminant a.valueUnit =
      a.prefixProduct (2 * k + 5) := by
    rw [← a.diagonalUnitDeterminant_prefixValueUnits (2 * k + 5) le_rfl]
    congr 1
  have hc : c = heHuLemma59C a k := by
    dsimp only [c]
    rw [hdet]
    rfl
  have hsquare : IsSquare
      (diagonalUnitDeterminant a.valueUnit *
        diagonalUnitDeterminant (heADCW1Odd (K := K) (k + 1) c)) := by
    refine ⟨c, ?_⟩
    rw [diagonalUnitDeterminant_heHuOddFirst]
    simp only [c]
    ac_rfl
  rcases (heADC2025Proposition42iOdd (K := K) (k + 1) c).exhaustive
      a.valueUnit hsquare with hfirst | hsecond
  · rw [hc] at hfirst
    have hcast := diagonalRepresents_heHuFinFamilyCast_both (K := K)
      (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
      (rfl : 2 * k + 5 = 2 * k + 5) _ _ hfirst.symm_of_sameRank
    simpa only [heHuFinFamilyCast_self] using Or.inl hcast
  · rw [hc] at hsecond
    have hcast := diagonalRepresents_heHuFinFamilyCast_both (K := K)
      (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
      (rfl : 2 * k + 5 = 2 * k + 5) _ _ hsecond.symm_of_sameRank
    simpa only [heHuFinFamilyCast_self] using Or.inr hcast

/-- The parity normalization used in Lemma 7.13 can be written with the
un-normalized parameter on the left and an explicit square on the right. -/
theorem heADC2025Lemma713_exists_normalized_mul_square (x : Kˣ) :
    ∃ s : Kˣ, x = heHuLemma59NormalizedParameter (K := K) x * s ^ 2 := by
  let d := heHuLemma59NormalizedParameter (K := K) x
  rcases heHuLemma59_normalized_sameSquareClass (K := K) x with ⟨t, ht⟩
  refine ⟨t / d, ?_⟩
  have ht' : t ^ 2 = x * d := by
    simpa only [pow_two] using ht.symm
  rw [div_pow, ht']
  change x = d * (x * d / d ^ 2)
  calc
    x = x * ((d * d) * (d * d)⁻¹) := by simp
    _ = d * (x * d / d ^ 2) := by
      simp only [div_eq_mul_inv, pow_two]
      ac_rfl

/-- Rows whose parameters differ by a nonsquare cannot be isometric,
independently of which member of each two-space determinant class is used. -/
theorem heADC2025Lemma713_twisted_not_represents {n : Nat}
    (pairs : Nat) (c u : Kˣ) (hu : ¬ IsSquare u)
    (rowC rowCU : Fin n → Kˣ)
    (hC : IsSquare
      (diagonalUnitDeterminant rowC *
        diagonalUnitDeterminant (heADCW1Odd (K := K) pairs c)))
    (hCU : IsSquare
      (diagonalUnitDeterminant rowCU *
        diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)))) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients rowCU)
      (diagonalUnitCoefficients rowC) := by
  intro hrep
  have hrows := DiagonalIsometryInvariantLaws.determinant_square
    rowCU rowC hrep
  have hleft : IsSquare
      (diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)) *
        diagonalUnitDeterminant rowC) :=
    isSquare_mul_trans
      (diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)))
      (diagonalUnitDeterminant rowCU)
      (diagonalUnitDeterminant rowC)
      (by simpa only [mul_comm] using hCU) hrows
  have hbase : IsSquare
      (diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)) *
        diagonalUnitDeterminant (heADCW1Odd (K := K) pairs c)) :=
    isSquare_mul_trans
      (diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)))
      (diagonalUnitDeterminant rowC)
      (diagonalUnitDeterminant (heADCW1Odd (K := K) pairs c)) hleft hC
  let d := diagonalUnitDeterminant (heADCW1Odd (K := K) pairs (c * u)) *
    diagonalUnitDeterminant (heADCW1Odd (K := K) pairs c)
  have hcancel : IsSquare (u * d) := by
    refine ⟨(-1 : Kˣ) ^ (pairs + 1) * c * u, ?_⟩
    dsimp only [d]
    rw [diagonalUnitDeterminant_heHuOddFirst,
      diagonalUnitDeterminant_heHuOddFirst]
    ac_rfl
  have huSquare := isSquare_mul_trans u d 1 hcancel
    (by simpa only [d, mul_one] using hbase)
  apply hu
  simpa only [mul_one] using huSquare

/-- The first large odd row represents the two first-column small rows at
parameters `c` and `c*u` whenever `u` is nonsquare. -/
theorem heADC2025Lemma713_largeFirst_represents_smallFirst
    (k : Nat) (c u : Kˣ) (hu : ¬ IsSquare u) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heADCW1Odd (K := K) k c))
        (diagonalUnitCoefficients
          (heHuFinFamilyCast (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW1Odd (K := K) (k + 1) c))) ∧
      DiagonalRepresents
        (diagonalUnitCoefficients (heADCW1Odd (K := K) k (c * u)))
        (diagonalUnitCoefficients
          (heHuFinFamilyCast (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW1Odd (K := K) (k + 1) c))) := by
  let first := heADCW1Odd (K := K) k c
  let second := heADCW2Odd (K := K) k c
  let firstCU := heADCW1Odd (K := K) k (c * u)
  have pair := heADC2025Proposition42iOdd (K := K) k c
  have pairCU := heADC2025Proposition42iOdd (K := K) k (c * u)
  have exceptional := heADC2025Proposition42iiiOddSecond (K := K) k c
  have hnotSame : ¬ DiagonalRepresents
      (diagonalUnitCoefficients first)
      (diagonalUnitCoefficients second) := by
    intro h
    exact pair.nonisometric h.symm_of_sameRank
  have hnotTwisted : ¬ DiagonalRepresents
      (diagonalUnitCoefficients firstCU)
      (diagonalUnitCoefficients second) := by
    apply heADC2025Lemma713_twisted_not_represents k c u hu second firstCU
    · exact pair.determinantSquare
    · exact ⟨diagonalUnitDeterminant firstCU, rfl⟩
  constructor
  · simpa only [first, second, heADCW1Odd, heADCW2Odd] using
      exceptional.exactness.represents_other first hnotSame
  · simpa only [firstCU, second, heADCW1Odd, heADCW2Odd] using
      exceptional.exactness.represents_other firstCU hnotTwisted

/-- The second large odd row represents the two second-column small rows
at parameters `c` and `c*u` whenever `u` is nonsquare. -/
theorem heADC2025Lemma713_largeSecond_represents_smallSecond
    (k : Nat) (c u : Kˣ) (hu : ¬ IsSquare u) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heADCW2Odd (K := K) k c))
        (diagonalUnitCoefficients
          (heHuFinFamilyCast (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW2Odd (K := K) (k + 1) c))) ∧
      DiagonalRepresents
        (diagonalUnitCoefficients (heADCW2Odd (K := K) k (c * u)))
        (diagonalUnitCoefficients
          (heHuFinFamilyCast (by omega : 2 * (k + 1) + 3 = 2 * k + 5)
            (heADCW2Odd (K := K) (k + 1) c))) := by
  let first := heADCW1Odd (K := K) k c
  let second := heADCW2Odd (K := K) k c
  let secondCU := heADCW2Odd (K := K) k (c * u)
  have pair := heADC2025Proposition42iOdd (K := K) k c
  have pairCU := heADC2025Proposition42iOdd (K := K) k (c * u)
  have exceptional := heADC2025Proposition42iiiOddFirst (K := K) k c
  have hnotSame : ¬ DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients first) :=
    pair.nonisometric
  have hnotTwisted : ¬ DiagonalRepresents
      (diagonalUnitCoefficients secondCU)
      (diagonalUnitCoefficients first) := by
    apply heADC2025Lemma713_twisted_not_represents k c u hu first secondCU
    · exact ⟨diagonalUnitDeterminant first, rfl⟩
    · exact pairCU.determinantSquare
  constructor
  · simpa only [first, second, heADCW1Odd, heADCW2Odd] using
      exceptional.exactness.represents_other second hnotSame
  · simpa only [first, secondCU, heADCW1Odd, heADCW2Odd] using
      exceptional.exactness.represents_other secondCU hnotTwisted

/-- The source diagonal form represents both corrected Lemma 7.13 targets
in the column selected by its published odd ambient row. -/
theorem heADC2025Lemma713_source_represents_selected_targets
    (a : GoodBONG q L (2 * k + 5))
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k)) :
    let c := heHuLemma59C a k
    let u := heHuSharp (heHuLemma59CTilde a k) hc
    let firstC := heHuLemma59Target (K := K) c k
    let firstCU := heHuLemma59Target (K := K) (c * u) k
    let secondC := heADCMaximalGoodBONG
      (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
    let secondCU := heADCMaximalGoodBONG
      (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
    (DiagonalRepresents (diagonalUnitCoefficients firstC.valueUnit)
          (diagonalUnitCoefficients a.valueUnit) ∧
        DiagonalRepresents (diagonalUnitCoefficients firstCU.valueUnit)
          (diagonalUnitCoefficients a.valueUnit)) ∨
      (DiagonalRepresents (diagonalUnitCoefficients secondC.valueUnit)
          (diagonalUnitCoefficients a.valueUnit) ∧
        DiagonalRepresents (diagonalUnitCoefficients secondCU.valueUnit)
          (diagonalUnitCoefficients a.valueUnit)) := by
  dsimp only
  let c := heHuLemma59C a k
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  have hu : ¬ IsSquare u := by
    intro huSquare
    have hone := hilbertSymbol_eq_one_of_isSquare_left
      (b := heHuLemma59CTilde a k) K huSquare
    have hneg := (heHu2022Proposition32 (heHuLemma59CTilde a k) hc).2.2
    change hilbertSymbol K u (heHuLemma59CTilde a k) = -1 at hneg
    rw [hneg] at hone
    norm_num at hone
  obtain ⟨sC, hsC⟩ := heADC2025Lemma713_exists_normalized_mul_square
    (K := K) c
  obtain ⟨sCU, hsCU⟩ := heADC2025Lemma713_exists_normalized_mul_square
    (K := K) (c * u)
  have hfirstCNorm :=
    Lattice.QuadraticLatticeModel.heHuOddFirst_represents_of_mul_square
    (K := K) k c (heHuLemma59NormalizedParameter (K := K) c) sC hsC
  have hfirstCUNorm :=
    Lattice.QuadraticLatticeModel.heHuOddFirst_represents_of_mul_square
    (K := K) k (c * u)
      (heHuLemma59NormalizedParameter (K := K) (c * u)) sCU hsCU
  have hsecondCNorm :=
    Lattice.QuadraticLatticeModel.heHuOddSecond_represents_of_mul_square
    (K := K) k c (heHuLemma59NormalizedParameter (K := K) c) sC hsC
  have hsecondCUNorm :=
    Lattice.QuadraticLatticeModel.heHuOddSecond_represents_of_mul_square
    (K := K) k (c * u)
      (heHuLemma59NormalizedParameter (K := K) (c * u)) sCU hsCU
  rcases a.heADC2025Lemma713_sourceDiagonal with hsource | hsource
  · obtain ⟨hlargeC, hlargeCU⟩ :=
      heADC2025Lemma713_largeFirst_represents_smallFirst
        (K := K) k c u hu
    left
    constructor
    · exact (heADC2025Lemma713_firstTarget_represents_oddFirst
          (K := K) c k).trans hfirstCNorm.symm_of_sameRank |>.trans
        hlargeC |>.trans hsource
    · exact (heADC2025Lemma713_firstTarget_represents_oddFirst
          (K := K) (c * u) k).trans hfirstCUNorm.symm_of_sameRank |>.trans
        hlargeCU |>.trans hsource
  · obtain ⟨hlargeC, hlargeCU⟩ :=
      heADC2025Lemma713_largeSecond_represents_smallSecond
        (K := K) k c u hu
    right
    constructor
    · exact (heADC2025Lemma713_secondTarget_represents_oddSecond
          (K := K) c k).trans hsecondCNorm.symm_of_sameRank |>.trans
        hlargeC |>.trans hsource
    · exact (heADC2025Lemma713_secondTarget_represents_oddSecond
          (K := K) (c * u) k).trans hsecondCUNorm.symm_of_sameRank |>.trans
        hlargeCU |>.trans hsource

/-- Replacing the first-column target by its paired second-column target
does not change the square class of the full mixed determinant. -/
theorem heADC2025Lemma713_currentMixed_sameSquareClass_of_pair
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3)) (x : Kˣ)
    (pair : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) x k).valueUnit b.valueUnit) :
    IsSquare
      (((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          b.prefixProduct (2 * k + 3)) *
        (heHuLemma59C a k * x)) := by
  let first := heHuLemma59Target (K := K) x k
  have hbDet : diagonalUnitDeterminant b.valueUnit =
      b.prefixProduct (2 * k + 3) := by
    rw [← b.diagonalUnitDeterminant_prefixValueUnits (2 * k + 3) le_rfl]
    congr 1
  have hfirstDet : diagonalUnitDeterminant first.valueUnit =
      first.prefixProduct (2 * k + 3) := by
    rw [← first.diagonalUnitDeterminant_prefixValueUnits (2 * k + 3) le_rfl]
    congr 1
  have hpair : IsSquare
      (b.prefixProduct (2 * k + 3) * first.prefixProduct (2 * k + 3)) := by
    simpa only [first, hbDet, hfirstDet] using pair.determinantSquare
  have hfirst := heHuLemma59_currentMixed_sameSquareClass
    (K := K) a k x
  have hmiddle : IsSquare
      (first.prefixProduct (2 * k + 3) *
        (((-1 : Kˣ) * a.prefixProduct (2 * k + 5)) *
          (heHuLemma59C a k * x))) := by
    simpa only [first, mul_assoc, mul_comm, mul_left_comm] using hfirst
  have hreplace := isSquare_mul_trans
    (b.prefixProduct (2 * k + 3))
    (first.prefixProduct (2 * k + 3))
    (((-1 : Kˣ) * a.prefixProduct (2 * k + 5)) *
      (heHuLemma59C a k * x)) hpair hmiddle
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hreplace

/-- At the terminal central index both alpha caps are infinite, so the
second bracketed defect is exactly the defect of the parameter product. -/
theorem heADC2025Lemma713_centralCurrentDefect_eq_of_pair
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3)) (x : Kˣ)
    (pair : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) x k).valueUnit b.valueUnit) :
    a.centralCurrentDefect b (heADC2025Lemma713CentralIndex k) =
      defectOrder (K := K) (heHuLemma59C a k * x) := by
  have hclass := a.heADC2025Lemma713_currentMixed_sameSquareClass_of_pair
    b x pair
  have hdefect := heADCQuadraticDefect_eq_of_squareProduct
    ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
      b.prefixProduct (2 * k + 3))
    (heHuLemma59C a k * x) hclass
  unfold centralCurrentDefect truncatedPrefixDefect
  change min
      (defectOrder (K := K)
        ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
          b.prefixProduct (2 * k + 3)))
      (min (a.prefixAlphaCap (2 * k + 5))
        (b.prefixAlphaCap (2 * k + 3))) = _
  rw [a.prefixAlphaCap_last, b.prefixAlphaCap_last, min_top_right,
    min_top_right]
  exact congrArg (WithTop.map fun m : Nat ↦ (m : ℚ)) hdefect

/-- A second-column target paired with the first test at `c` also has
infinite terminal current defect. -/
theorem heADC2025Lemma713_centralCurrentDefect_C_of_pair
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (pair : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k).valueUnit
      b.valueUnit) :
    a.centralCurrentDefect b (heADC2025Lemma713CentralIndex k) = ⊤ := by
  rw [a.heADC2025Lemma713_centralCurrentDefect_eq_of_pair b
    (heHuLemma59C a k) pair]
  apply defectOrder_eq_top_of_isSquare
  exact ⟨heHuLemma59C a k, rfl⟩

/-- A second-column target paired with the first test at `c*u` has
terminal current defect `d(u)`. -/
theorem heADC2025Lemma713_centralCurrentDefect_C_mul_of_pair
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3)) (u : Kˣ)
    (pair : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k).valueUnit
      b.valueUnit) :
    a.centralCurrentDefect b (heADC2025Lemma713CentralIndex k) =
      defectOrder (K := K) u := by
  rw [a.heADC2025Lemma713_centralCurrentDefect_eq_of_pair b
    (heHuLemma59C a k * u) pair]
  calc
    defectOrder (K := K)
        (heHuLemma59C a k * (heHuLemma59C a k * u)) =
      defectOrder (K := K) (u * heHuLemma59C a k ^ 2) := by
        congr 1
        simp only [pow_two]
        ac_rfl
    _ = defectOrder (K := K) u := defectOrder_mul_square u (heHuLemma59C a k)

/-- Lemma 7.6(v) supplies the first terminal defect for every maximal
odd-rank target.  This wrapper aligns the integer and rational casts used
in Lemma 7.13. -/
theorem heADC2025Lemma713_centralPreviousDefect_eq
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG r M (2 * k + 3))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hAdjacent : a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
      ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
        WithTop ℚ))
    (hM : Lattice.IsOMaximal r M) :
    a.centralPreviousDefect b (heADC2025Lemma713CentralIndex k) =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
  have h := a.heADC2025Lemma76v k b hInitial hAlpha hAdjacent hM
  have h' :
      a.centralPreviousDefect b (heADC2025Lemma713CentralIndex k) =
        ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
          WithTop ℚ) := by
    simpa only [centralPreviousDefect, heADC2025Lemma713CentralIndex,
      show 2 * k + 4 - 2 = 2 * k + 2 by omega] using h
  exact h'.trans (by
    congr 1
    push_cast
    ring)

/-- Lemma 7.13(i) for the first-column maximal tests.  Both terminal
condition-(iii') triggers are active. -/
theorem heADC2025Lemma713iFirst (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let c := heHuLemma59C a k
      let u := heHuSharp cTilde hc
      a.centralDefectTrigger (heHuLemma59Target (K := K) c k)
          (heADC2025Lemma713CentralIndex k) ∧
        a.centralDefectTrigger (heHuLemma59Target (K := K) (c * u) k)
          (heADC2025Lemma713CentralIndex k) := by
  dsimp only
  have h710 := a.heADC2025Lemma710 k hADC
  have hAdjacent :
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
        ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
          WithTop ℚ) := by
    rcases h710.alphaAlternative with hzero | hone
    · have hfalse : (1 : ℚ) = 0 := hAlpha.symm.trans hzero
      norm_num at hfalse
    · exact hone.2
  have h712Raw := a.heADC2025Lemma712 k hADC hAlpha hTrigger
  have h712 :
      ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
        defectOrder (K := K) (heHuLemma59CTilde a k) =
            ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) ∧
          IsValuationUnit K (heHuSharp (heHuLemma59CTilde a k) hc : K) ∧
          defectOrder (K := K) (heHuSharp (heHuLemma59CTilde a k) hc) =
            (((2 * (ramificationIndex K : Int) +
                a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
              WithTop ℚ) := by
    simpa only [heHuLemma59CTilde_eq_lemma58Prefix] using h712Raw
  rcases h712 with ⟨hc, _hraw, hunit, hsharp⟩
  refine ⟨hc, ?_⟩
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hboundary := a.heADC2025Lemma713_boundaryOrder_gt_gapParity
    hADC.isIntegral hTrigger
  have hcDiff : Even (ordUnit K c - gap) := by
    simpa only [c, gap] using
      a.heHuLemma59_c_order_sub_gap_even k (by omega) h710.initial
  have hcuDiff : Even (ordUnit K (c * u) - gap) := by
    apply heHuLemma59_mul_unit_order_sub_gap_even c u gap hcDiff
    simpa only [u, cTilde] using hunit
  have hcParity : heHuLemma59Parity (K := K) c =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity c gap hcDiff
  have hcuParity : heHuLemma59Parity (K := K) (c * u) =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity (c * u) gap hcuDiff
  have hlastC : (heHuLemma59Target (K := K) c k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) c k).trans hcParity
  have hlastCU : (heHuLemma59Target (K := K) (c * u) k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) (c * u) k).trans hcuParity
  have hpreviousC :
      a.centralPreviousDefect (heHuLemma59Target (K := K) c k)
          (heADC2025Lemma713CentralIndex k) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) := by
    have h := a.heADC2025Lemma76v k
      (heHuLemma59Target (K := K) c k) h710.initial hAlpha hAdjacent
      (heADC2025Lemma713_firstTarget_isOMaximal c k)
    have h' :
        a.centralPreviousDefect (heHuLemma59Target (K := K) c k)
            (heADC2025Lemma713CentralIndex k) =
          ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
            WithTop ℚ) := by
      simpa only [centralPreviousDefect, heADC2025Lemma713CentralIndex,
        show 2 * k + 4 - 2 = 2 * k + 2 by omega] using h
    exact h'.trans (by
      congr 1
      push_cast
      ring)
  have hpreviousCU :
      a.centralPreviousDefect (heHuLemma59Target (K := K) (c * u) k)
          (heADC2025Lemma713CentralIndex k) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) := by
    have h := a.heADC2025Lemma76v k
      (heHuLemma59Target (K := K) (c * u) k) h710.initial hAlpha hAdjacent
      (heADC2025Lemma713_firstTarget_isOMaximal (c * u) k)
    have h' :
        a.centralPreviousDefect (heHuLemma59Target (K := K) (c * u) k)
            (heADC2025Lemma713CentralIndex k) =
          ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
            WithTop ℚ) := by
      simpa only [centralPreviousDefect, heADC2025Lemma713CentralIndex,
        show 2 * k + 4 - 2 = 2 * k + 2 by omega] using h
    exact h'.trans (by
      congr 1
      push_cast
      ring)
  have hcurrentC :
      ((((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
            WithTop ℚ) ≤
        a.centralCurrentDefect (heHuLemma59Target (K := K) c k)
          (heADC2025Lemma713CentralIndex k) := by
    rw [show c = heHuLemma59C a k by rfl,
      a.heADC2025Lemma713_firstTarget_centralCurrentDefect_C]
    exact le_top
  have hcurrentCU :
      ((((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
            WithTop ℚ) ≤
        a.centralCurrentDefect (heHuLemma59Target (K := K) (c * u) k)
          (heADC2025Lemma713CentralIndex k) := by
    rw [show c = heHuLemma59C a k by rfl,
      a.heADC2025Lemma713_firstTarget_centralCurrentDefect_C_mul]
    simpa only [u, cTilde] using hsharp.symm.le
  constructor
  · apply a.heADC2025Lemma713_defectTrigger_of_terminal_bounds
      (heHuLemma59Target (K := K) c k)
    · simpa only [gap] using hlastC
    · simpa only [gap] using hboundary
    · exact hpreviousC
    · exact hcurrentC
  · apply a.heADC2025Lemma713_defectTrigger_of_terminal_bounds
      (heHuLemma59Target (K := K) (c * u) k)
    · simpa only [gap] using hlastCU
    · simpa only [gap] using hboundary
    · exact hpreviousCU
    · exact hcurrentCU

/-- Lemma 7.13(i) for any pair of second-column maximal targets paired
with the two literal first-column tests. -/
theorem heADC2025Lemma713iSecond_of_pairs (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩)
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k))
    (hsharp : defectOrder (K := K)
      (heHuSharp (heHuLemma59CTilde a k) hc) =
        (((2 * (ramificationIndex K : Int) +
            a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
          WithTop ℚ))
    {W₁ W₂ : Type u} [AddCommGroup W₁] [Module K W₁]
    [AddCommGroup W₂] [Module K W₂]
    {r₁ : QuadraticSpace K W₁} {r₂ : QuadraticSpace K W₂}
    {M₁ : Lattice K W₁} {M₂ : Lattice K W₂}
    (bC : GoodBONG r₁ M₁ (2 * k + 3))
    (bCU : GoodBONG r₂ M₂ (2 * k + 3))
    (hMC : Lattice.IsOMaximal r₁ M₁)
    (hMCU : Lattice.IsOMaximal r₂ M₂)
    (pairC : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k).valueUnit
      bC.valueUnit)
    (pairCU : HeHuSpacePairProperties
      (heHuLemma59Target (K := K)
        (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k).valueUnit
      bCU.valueUnit)
    (hlastC : bC.order ⟨2 * k + 2, by omega⟩ =
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1))
    (hlastCU : bCU.order ⟨2 * k + 2, by omega⟩ =
      (if Even (a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩) then 0 else 1)) :
    a.centralDefectTrigger bC (heADC2025Lemma713CentralIndex k) ∧
      a.centralDefectTrigger bCU (heADC2025Lemma713CentralIndex k) := by
  have h710 := a.heADC2025Lemma710 k hADC
  have hAdjacent :
      a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
        ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
          WithTop ℚ) := by
    rcases h710.alphaAlternative with hzero | hone
    · have hfalse : (1 : ℚ) = 0 := hAlpha.symm.trans hzero
      norm_num at hfalse
    · exact hone.2
  have hboundary := a.heADC2025Lemma713_boundaryOrder_gt_gapParity
    hADC.isIntegral hTrigger
  have hpreviousC := a.heADC2025Lemma713_centralPreviousDefect_eq
    bC h710.initial hAlpha hAdjacent hMC
  have hpreviousCU := a.heADC2025Lemma713_centralPreviousDefect_eq
    bCU h710.initial hAlpha hAdjacent hMCU
  have hcurrentC :
      ((((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
            WithTop ℚ) ≤
        a.centralCurrentDefect bC (heADC2025Lemma713CentralIndex k) := by
    rw [a.heADC2025Lemma713_centralCurrentDefect_C_of_pair bC pairC]
    exact le_top
  have hcurrentCU :
      ((((2 * (ramificationIndex K : Int) +
          a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ)) :
            WithTop ℚ) ≤
        a.centralCurrentDefect bCU (heADC2025Lemma713CentralIndex k) := by
    rw [a.heADC2025Lemma713_centralCurrentDefect_C_mul_of_pair bCU
      (heHuSharp (heHuLemma59CTilde a k) hc) pairCU]
    exact hsharp.symm.le
  constructor
  · exact a.heADC2025Lemma713_defectTrigger_of_terminal_bounds bC
      hlastC hboundary hpreviousC hcurrentC
  · exact a.heADC2025Lemma713_defectTrigger_of_terminal_bounds bCU
      hlastCU hboundary hpreviousCU hcurrentCU

/-- Lemma 7.13(i) for the canonical second-column maximal targets. -/
theorem heADC2025Lemma713iSecond (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let c := heHuLemma59C a k
      let u := heHuSharp cTilde hc
      let bC := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
      let bCU := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
      a.centralDefectTrigger bC (heADC2025Lemma713CentralIndex k) ∧
        a.centralDefectTrigger bCU (heADC2025Lemma713CentralIndex k) := by
  dsimp only
  have h712Raw := a.heADC2025Lemma712 k hADC hAlpha hTrigger
  have h712 :
      ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
        defectOrder (K := K) (heHuLemma59CTilde a k) =
            ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) ∧
          IsValuationUnit K (heHuSharp (heHuLemma59CTilde a k) hc : K) ∧
          defectOrder (K := K) (heHuSharp (heHuLemma59CTilde a k) hc) =
            (((2 * (ramificationIndex K : Int) +
                a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
              WithTop ℚ) := by
    simpa only [heHuLemma59CTilde_eq_lemma58Prefix] using h712Raw
  rcases h712 with ⟨hc, _hraw, hunit, hsharp⟩
  refine ⟨hc, ?_⟩
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  let bC := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
  let bCU := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
  have hcDiff : Even (ordUnit K c - gap) := by
    simpa only [c, gap] using a.heHuLemma59_c_order_sub_gap_even k
      (by omega) (a.heADC2025Lemma710 k hADC).initial
  have hcuDiff : Even (ordUnit K (c * u) - gap) := by
    apply heHuLemma59_mul_unit_order_sub_gap_even c u gap hcDiff
    simpa only [u, cTilde] using hunit
  have hcParity := heHuLemma59Parity_eq_gapParity c gap hcDiff
  have hcuParity := heHuLemma59Parity_eq_gapParity (c * u) gap hcuDiff
  have hlastC : bC.order ⟨2 * k + 2, by omega⟩ =
      if Even gap then 0 else 1 := by
    exact (heADC2025Lemma713_secondTarget_lastOrder (K := K) c k).trans hcParity
  have hlastCU : bCU.order ⟨2 * k + 2, by omega⟩ =
      if Even gap then 0 else 1 := by
    exact (heADC2025Lemma713_secondTarget_lastOrder (K := K) (c * u) k).trans
      hcuParity
  apply a.heADC2025Lemma713iSecond_of_pairs k hADC hAlpha hTrigger hc
    (by simpa only [u, cTilde] using hsharp) bC bCU
    (heHuOMaximalLattice_isOMaximal _)
    (heHuOMaximalLattice_isOMaximal _)
    (by simpa only [bC, c] using
      heADC2025Lemma713_secondTarget_pair (K := K) c k)
    (by simpa only [bCU, c, u] using
      heADC2025Lemma713_secondTarget_pair (K := K) (c * u) k)
    (by simpa only [gap] using hlastC)
    (by simpa only [gap] using hlastCU)

/-- Corrected Lemma 7.13(ii), abstract second-column form.  Any two
second-column targets paired with the literal first-column maximal targets
cannot both be represented by the source prefix. -/
theorem heADC2025Lemma713iiSecond_of_pairs
    {m : Nat} (a : GoodBONG q L (m + 3)) (k : Nat)
    (hm : 2 * k + 2 ≤ m)
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k))
    (secondC secondD : Fin (2 * k + 3) → Kˣ)
    (pairC : HeHuSpacePairProperties
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k).valueUnit secondC)
    (pairD : HeHuSpacePairProperties
      (heHuLemma59Target (K := K)
        (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k).valueUnit
      secondD) :
    ¬(DiagonalRepresents
        (diagonalUnitCoefficients secondC)
        (diagonalUnitCoefficients
          (a.prefixValueUnits (2 * k + 4) (by omega))) ∧
      DiagonalRepresents
        (diagonalUnitCoefficients secondD)
        (diagonalUnitCoefficients
          (a.prefixValueUnits (2 * k + 4) (by omega)))) := by
  let firstC :=
    (heHuLemma59Target (K := K) (heHuLemma59C a k) k).valueUnit
  let firstD :=
    (heHuLemma59Target (K := K)
      (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k).valueUnit
  let source := a.prefixValueUnits (2 * k + 4) (by omega)
  have hfirstRaw := a.heHu2022Lemma59iiExactlyOne k hm hc
  have hCfull :
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixValues
          (2 * k + 3) le_rfl =
        diagonalUnitCoefficients firstC := by
    funext i
    rfl
  have hDfull :
      (heHuLemma59Target (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k).prefixValues
          (2 * k + 3) le_rfl =
        diagonalUnitCoefficients firstD := by
    funext i
    rfl
  rw [hCfull, hDfull] at hfirstRaw
  have hfirst : HeHuRepresentsExactlyOne firstC firstD source := by
    simpa only [HeHuRepresentsExactlyOne, firstC, firstD, source,
      diagonalUnitCoefficients_prefixValueUnits] using hfirstRaw
  have hsecond := heADC_exactlyOne_second_of_first
    firstC secondC firstD secondD source pairC pairD hfirst
  intro hboth
  rcases hsecond with hleft | hright
  · exact hleft.2 hboth.2
  · exact hright.1 hboth.1

/-- Corrected Lemma 7.13(ii) for both columns of the published odd table.
For each fixed column, the two displayed source-prefix representations
cannot hold simultaneously. -/
theorem heADC2025Lemma713ii (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let c := heHuLemma59C a k
      let u := heHuSharp cTilde hc
      let bC := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
      let bCU := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
      ¬(DiagonalRepresents
          ((heHuLemma59Target (K := K) c k).prefixValues
            (2 * k + 3) le_rfl)
          (a.prefixValues (2 * k + 4) (by omega)) ∧
        DiagonalRepresents
          ((heHuLemma59Target (K := K) (c * u) k).prefixValues
            (2 * k + 3) le_rfl)
          (a.prefixValues (2 * k + 4) (by omega))) ∧
      ¬(DiagonalRepresents
          (diagonalUnitCoefficients bC.valueUnit)
          (diagonalUnitCoefficients
            (a.prefixValueUnits (2 * k + 4) (by omega))) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients bCU.valueUnit)
          (diagonalUnitCoefficients
            (a.prefixValueUnits (2 * k + 4) (by omega)))) := by
  dsimp only
  have h712Raw := a.heADC2025Lemma712 k hADC hAlpha hTrigger
  have h712 : ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k), True := by
    rcases h712Raw with ⟨hc, _⟩
    rw [← heHuLemma59CTilde_eq_lemma58Prefix a k] at hc
    exact ⟨hc, trivial⟩
  rcases h712 with ⟨hc, _⟩
  refine ⟨hc, ?_, ?_⟩
  · exact a.heHu2022Lemma59ii k (by omega) hc
  · apply a.heADC2025Lemma713iiSecond_of_pairs k (by omega) hc
      (heADCMaximalGoodBONG
        (heADCW2Odd k
          (heHuLemma59NormalizedParameter (K := K) (heHuLemma59C a k)))).valueUnit
      (heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K)
          (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc)))).valueUnit
    · exact heADC2025Lemma713_secondTarget_pair (K := K)
        (heHuLemma59C a k) k
    · exact heADC2025Lemma713_secondTarget_pair (K := K)
        (heHuLemma59C a k * heHuSharp (heHuLemma59CTilde a k) hc) k

/-- He (2025), Lemma 7.13 with the quantifiers proved by the published
argument.  In each fixed column, both tests activate condition (iii'), but
the central representation condition fails for at least one of them. -/
theorem heADC2025Lemma713 (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let c := heHuLemma59C a k
      let u := heHuSharp cTilde hc
      let firstC := heHuLemma59Target (K := K) c k
      let firstCU := heHuLemma59Target (K := K) (c * u) k
      let secondC := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
      let secondCU := heADCMaximalGoodBONG
        (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
      a.centralDefectTrigger firstC (heADC2025Lemma713CentralIndex k) ∧
        a.centralDefectTrigger firstCU (heADC2025Lemma713CentralIndex k) ∧
        (¬a.CentralRepresentationConditionsPrime firstC ∨
          ¬a.CentralRepresentationConditionsPrime firstCU) ∧
        a.centralDefectTrigger secondC (heADC2025Lemma713CentralIndex k) ∧
        a.centralDefectTrigger secondCU (heADC2025Lemma713CentralIndex k) ∧
        (¬a.CentralRepresentationConditionsPrime secondC ∨
          ¬a.CentralRepresentationConditionsPrime secondCU) := by
  dsimp only
  rcases a.heADC2025Lemma713iFirst k hADC hAlpha hTrigger with
    ⟨hc, hfirstC, hfirstCU⟩
  rcases a.heADC2025Lemma713iSecond k hADC hAlpha hTrigger with
    ⟨hcSecond, hsecondC, hsecondCU⟩
  have hproofSecond : hcSecond = hc := Subsingleton.elim _ _
  subst hcSecond
  rcases a.heADC2025Lemma713ii k hADC hAlpha hTrigger with
    ⟨hcNot, hnotFirst, hnotSecond⟩
  have hproofNot : hcNot = hc := Subsingleton.elim _ _
  subst hcNot
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  let firstC := heHuLemma59Target (K := K) c k
  let firstCU := heHuLemma59Target (K := K) (c * u) k
  let secondC := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
  let secondCU := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
  have hfailFirst : ¬a.CentralRepresentationConditionsPrime firstC ∨
      ¬a.CentralRepresentationConditionsPrime firstCU := by
    by_cases hprimeC : a.CentralRepresentationConditionsPrime firstC
    · right
      intro hprimeCU
      apply hnotFirst
      constructor
      · apply a.centralRepresentationConditionsPrime_represents_castLengths
          firstC hprimeC (heADC2025Lemma713CentralIndex k) hfirstC
        · simp only [heADC2025Lemma713CentralIndex]
          omega
        · rfl
      · apply a.centralRepresentationConditionsPrime_represents_castLengths
          firstCU hprimeCU (heADC2025Lemma713CentralIndex k) hfirstCU
        · simp only [heADC2025Lemma713CentralIndex]
          omega
        · rfl
    · exact Or.inl hprimeC
  have hfailSecond : ¬a.CentralRepresentationConditionsPrime secondC ∨
      ¬a.CentralRepresentationConditionsPrime secondCU := by
    by_cases hprimeC : a.CentralRepresentationConditionsPrime secondC
    · right
      intro hprimeCU
      apply hnotSecond
      constructor
      · have hrep := a.centralRepresentationConditionsPrime_represents_castLengths
          (s := 2 * k + 3) (t := 2 * k + 4) secondC hprimeC
          (heADC2025Lemma713CentralIndex k) hsecondC
          (by simp only [heADC2025Lemma713CentralIndex]; omega) rfl
        have hfull : secondC.prefixValues (2 * k + 3) le_rfl =
            diagonalUnitCoefficients secondC.valueUnit := by
          funext i
          rfl
        rw [hfull] at hrep
        simpa only [diagonalUnitCoefficients_prefixValueUnits] using hrep
      · have hrep := a.centralRepresentationConditionsPrime_represents_castLengths
          (s := 2 * k + 3) (t := 2 * k + 4) secondCU hprimeCU
          (heADC2025Lemma713CentralIndex k) hsecondCU
          (by simp only [heADC2025Lemma713CentralIndex]; omega) rfl
        have hfull : secondCU.prefixValues (2 * k + 3) le_rfl =
            diagonalUnitCoefficients secondCU.valueUnit := by
          funext i
          rfl
        rw [hfull] at hrep
        simpa only [diagonalUnitCoefficients_prefixValueUnits] using hrep
    · exact Or.inl hprimeC
  exact ⟨hc, hfirstC, hfirstCU, hfailFirst, hsecondC, hsecondCU, hfailSecond⟩

/-- The corrected Lemma 7.13 is still strong enough for the necessity
argument in Lemma 7.5: under `n`-ADC, its terminal trigger is impossible. -/
theorem heADC2025Lemma713_trigger_impossible (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1) :
    ¬(a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) := by
  intro hTrigger
  rcases a.heADC2025Lemma713 k hADC hAlpha hTrigger with
    ⟨hc, hfirstC, hfirstCU, hfailFirst,
      hsecondC, hsecondCU, hfailSecond⟩
  let c := heHuLemma59C a k
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  let firstC := heHuLemma59Target (K := K) c k
  let firstCU := heHuLemma59Target (K := K) (c * u) k
  let secondC := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) c))
  let secondCU := heADCMaximalGoodBONG
    (heADCW2Odd k (heHuLemma59NormalizedParameter (K := K) (c * u)))
  have lift {W : Type u} [AddCommGroup W] [Module K W]
      {r : QuadraticSpace K W} {M : Lattice K W}
      (b : GoodBONG r M (2 * k + 3)) (hM : Lattice.IsIntegral r M)
      (hdiag : DiagonalRepresents
        (diagonalUnitCoefficients b.valueUnit)
        (diagonalUnitCoefficients a.valueUnit)) :
      Lattice.Represents q r L M := by
    apply hADC.represents r M b.toBONG.length_eq_finrank.symm hM
    have hSource : q.Represents
        (BONG.coefficientDiagonalSpace a.valueUnit) :=
      ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
    have hDiagonal :
        (BONG.coefficientDiagonalSpace a.valueUnit).Represents
          (BONG.coefficientDiagonalSpace b.valueUnit) :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        b.valueUnit a.valueUnit).2 hdiag
    exact (hSource.trans hDiagonal).trans
      ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  rcases a.heADC2025Lemma713_source_represents_selected_targets hc with
    hrepresented | hrepresented
  · have hrepC := lift firstC
      (heADC2025Lemma713_firstTarget_isOMaximal
        (K := K) c k).isIntegral hrepresented.1
    have hrepCU := lift firstCU
      (heADC2025Lemma713_firstTarget_isOMaximal
        (K := K) (c * u) k).isIntegral hrepresented.2
    have hcentralC :=
      ((heADC2025Theorem36Published (by omega) hrepC.ambient a firstC).mp
        hrepC).centralRepresentations
    have hcentralCU :=
      ((heADC2025Theorem36Published (by omega) hrepCU.ambient a firstCU).mp
        hrepCU).centralRepresentations
    exact hfailFirst.elim (fun hfail ↦ hfail hcentralC)
      (fun hfail ↦ hfail hcentralCU)
  · have hrepC :=
      lift secondC (heHuOMaximalLattice_isOMaximal _).isIntegral
        hrepresented.1
    have hrepCU :=
      lift secondCU (heHuOMaximalLattice_isOMaximal _).isIntegral
        hrepresented.2
    have hcentralC :=
      ((heADC2025Theorem36Published (by omega) hrepC.ambient a secondC).mp
        hrepC).centralRepresentations
    have hcentralCU :=
      ((heADC2025Theorem36Published (by omega) hrepCU.ambient a secondCU).mp
        hrepCU).centralRepresentations
    exact hfailSecond.elim (fun hfail ↦ hfail hcentralC)
      (fun hfail ↦ hfail hcentralCU)

end BONG.GoodBONG

end Bong
