/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma77
import Bong.Bong.He2023ADCLemma78
import Bong.Bong.He2023ADCOddMaximalStructure
import Bong.Bong.He2023ADCSignedDeterminant

/-!
# He (2025), sufficiency in Lemma 7.5

The four displayed invariant clauses are packaged without changing their
quantifiers.  The small terminal-gap branch is the direct assembly of
Lemmas 7.7 and 7.8 with Theorem 3.6 and the maximal-target reduction.
The large-gap branch is separated below so that its use of Lemma 4.12(iii)
remains independently auditable.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem even_ordUnit_of_square_for_lemma75 (x : Kˣ)
    (hx : IsSquare x) : Even (ordUnit K x) := by
  rcases hx with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

/-- The four numerical conditions displayed in He (2025), Lemma 7.5,
with odd paper rank `n=2*k+3`. -/
structure HeADCLemma75Conditions (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2)) : Prop where
  initial : a.HeHuI1E (2 * k + 2) (by omega)
  boundary : a.HeHuI2E (2 * k + 2) (by omega)
  largeGap :
    2 * (ramificationIndex K : Int) <
        a.order ⟨2 * k + 4, by omega⟩ - a.order ⟨2 * k + 3, by omega⟩ →
      a.order ⟨2 * k + 3, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) ∧
        a.order ⟨2 * k + 4, by omega⟩ = 1
  alphaOneTail :
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 →
      Even (a.order ⟨2 * k + 3, by omega⟩) ∧
        2 - 2 * (ramificationIndex K : Int) ≤
          a.order ⟨2 * k + 3, by omega⟩ ∧
        a.order ⟨2 * k + 3, by omega⟩ ≤ 0 ∧
        (a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
          a.order ⟨2 * k + 4, by omega⟩ = 1)

/-- The small-gap half of the sufficiency proof in Lemma 7.5. -/
theorem heADC2025Lemma75Sufficiency_of_terminalGap_le (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hA : Lattice.IsIntegral q L)
    (C : a.HeADCLemma75Conditions k)
    (hTerminalGap :
      a.order ⟨2 * k + 4, by omega⟩ - a.order ⟨2 * k + 3, by omega⟩ ≤
        2 * (ramificationIndex K : Int)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) := by
  apply (Lattice.isNADC_iff_representsAllRelevantOMaximal
    q L (2 * k + 3)).mpr
  refine ⟨hA, ?_⟩
  intro W _ _ r M hRank hMaximal ambient
  letI : BONGStructuralLaws.{u, u} K := bongStructuralLawsProved K
  let b : GoodBONG r M (2 * k + 3) :=
    (GoodBONG.ofLattice r M).castLength hRank
  have hBoundary :
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
        (a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
          a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
            ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
              WithTop ℚ)) := by
    simpa only [HeHuI2E, heADCAdjacentCappedDefect] using C.boundary
  have hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := by
    rcases hBoundary with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr hone.1
  have hAlternative :
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
        (a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
          a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
            ((((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ)) : ℚ) :
              WithTop ℚ) ∧
          Even (a.order ⟨2 * k + 3, by omega⟩) ∧
          2 - 2 * (ramificationIndex K : Int) ≤
            a.order ⟨2 * k + 3, by omega⟩ ∧
          a.order ⟨2 * k + 3, by omega⟩ ≤ 0 ∧
          (a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
            a.order ⟨2 * k + 4, by omega⟩ = 1)) := by
    rcases hBoundary with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr ⟨hone.1, hone.2, C.alphaOneTail hone.1⟩
  have hConditions : RepresentationConditions a b (by omega) :=
    { orderCondition := a.heADC2025Lemma77i k b C.initial hMaximal.isIntegral
      defectCondition :=
        a.heADC2025Lemma77ii k b hA C.initial C.boundary hMaximal.isIntegral
      centralRepresentations :=
        a.heADC2025Lemma78 k b hA C.initial hTerminalGap hAlternative hMaximal
      longRepresentations :=
        a.heADC2025Lemma77iii k b C.initial hAlpha hTerminalGap }
  exact (a.heADC2025Theorem36 (by omega) ambient b).mpr hConditions

/-- The full maximal profile forced by clauses (i) and (iii) in the
large-gap branch of Lemma 7.5. -/
theorem heADC2025Lemma75_largeGap_orderProfile (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hNext : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hLast : a.order ⟨2 * k + 4, by omega⟩ = 1) :
    ∀ i, a.order i =
      heADCMaximalOrderProfile (K := K) (k + 1)
        ![0, -(2 * (ramificationIndex K : Int)), 1] ⟨i.val, by omega⟩ := by
  intro i
  by_cases hi : i.val < 2 * (k + 1)
  · by_cases heven : Even i.val
    · have horder : a.order i = 0 := by
        have h := hInitial.oddOrder ⟨i.val, by omega⟩ heven.add_one
        simpa only using h
      simp [heADCMaximalOrderProfile, hi, heven, horder]
    · have hodd : Odd i.val := Nat.not_even_iff_odd.mp heven
      have horder : a.order i = -(2 * (ramificationIndex K : Int)) := by
        have h := hInitial.evenOrder ⟨i.val, by omega⟩ hodd.add_one
        simpa only using h
      simp [heADCMaximalOrderProfile, hi, heven, horder]
  · have hcases : i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 ∨
        i.val = 2 * k + 4 := by
      have := i.isLt
      omega
    rcases hcases with hfirst | hsecond | hthird
    · have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
      have horder : a.order i = 0 := by
        have h := hInitial.oddOrder ⟨2 * k + 2, by omega⟩ heven.add_one
        have hiEq : i = (⟨2 * k + 2, by omega⟩ :
            Fin (((2 * k + 2) + 1) + 2)) := Fin.ext hfirst
        rw [hiEq]
        exact h
      rw [horder]
      simp [heADCMaximalOrderProfile, hfirst,
        show ¬ 2 * k + 2 < 2 * (k + 1) by omega,
        show 2 * k + 2 - 2 * (k + 1) = 0 by omega]
    · have hiEq : i = (⟨2 * k + 3, by omega⟩ :
          Fin (((2 * k + 2) + 1) + 2)) := Fin.ext hsecond
      rw [hiEq, hNext]
      simp [heADCMaximalOrderProfile,
        show ¬ 2 * k + 3 < 2 * (k + 1) by omega,
        show 2 * k + 3 - 2 * (k + 1) = 1 by omega]
    · have hiEq : i = (⟨2 * k + 4, by omega⟩ :
          Fin (((2 * k + 2) + 1) + 2)) := Fin.ext hthird
      rw [hiEq, hLast]
      simp [heADCMaximalOrderProfile,
        show ¬ 2 * k + 4 < 2 * (k + 1) by omega,
        show 2 * k + 4 - 2 * (k + 1) = 2 by omega]

/-- In the large-gap branch, the displayed profile has odd determinant
order.  This excludes the two valuation-zero ambient rows. -/
theorem heADC2025Lemma75_largeGap_fullOrder_not_even (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hNext : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hLast : a.order ⟨2 * k + 4, by omega⟩ = 1) :
    ¬ Even (ordUnit K (a.prefixProduct (2 * k + 5))) := by
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hDiff : Even (ordUnit K (heHuLemma59C a k) - gap) := by
    simpa only [gap] using
      a.heHuLemma59_c_order_sub_gap_even k (by omega) hInitial
  have hGapOdd : Odd gap := by
    rw [show gap = 1 + 2 * (ramificationIndex K : Int) by
      dsimp only [gap]
      rw [hNext, hLast]
      ring]
    exact odd_one.add_even ⟨ramificationIndex K, by ring⟩
  have hCNotEven : ¬ Even (ordUnit K (heHuLemma59C a k)) := by
    intro hEven
    have hGapEven :=
      (heHuLemma59_even_iff_of_sub_even hDiff).mp hEven
    exact Int.not_even_iff_odd.mpr hGapOdd hGapEven
  have hOrder : ordUnit K (heHuLemma59C a k) =
      ordUnit K (a.prefixProduct (2 * k + 5)) := by
    unfold heHuLemma59C
    rw [ordUnit_mul, ordUnit_pow, ordUnit_neg_one_eq_zero (K := K)]
    simp only [mul_zero, zero_add]
  rwa [hOrder] at hCNotEven

/-- Lemma 4.12(iii), applied after the odd determinant has removed the
valuation-zero rows, recognizes the source lattice as `O`-maximal. -/
theorem heADC2025Lemma75_largeGap_isOMaximal (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hA : Lattice.IsIntegral q L)
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hNext : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hLast : a.order ⟨2 * k + 4, by omega⟩ = 1) :
    Lattice.IsOMaximal q L := by
  have hProfile := a.heADC2025Lemma75_largeGap_orderProfile k
    hInitial hNext hLast
  have hFullNotEven := a.heADC2025Lemma75_largeGap_fullOrder_not_even k
    hInitial hNext hLast
  obtain ⟨δ, hδ, hfirst | hsecond | hfirstPi | hsecondPi⟩ :=
    a.exists_heADCOddNormalizedAmbient (k + 1)
  · have hdetOrder : ordUnit K
        (diagonalUnitDeterminant (heADCW1Odd (K := K) (k + 1) δ)) = 0 := by
      rw [diagonalUnitDeterminant_heHuOddFirst, ordUnit_mul, ordUnit_pow,
        ordUnit_neg_one_eq_zero (K := K),
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
      simp
    have hEven := even_ordUnit_of_square_for_lemma75
      (a.prefixProduct (2 * k + 5) *
        diagonalUnitDeterminant (heADCW1Odd (K := K) (k + 1) δ))
      (a.heADC_prefixProduct_det_square_of_ambient _ hfirst)
    rw [ordUnit_mul, hdetOrder, add_zero] at hEven
    exact (hFullNotEven hEven).elim
  · let first := heADCW1Odd (K := K) (k + 1) δ
    let second := heADCW2Odd (K := K) (k + 1) δ
    have hFirstOrder : ordUnit K (diagonalUnitDeterminant first) = 0 := by
      dsimp only [first, heADCW1Odd]
      rw [diagonalUnitDeterminant_heHuOddFirst, ordUnit_mul, ordUnit_pow,
        ordUnit_neg_one_eq_zero (K := K),
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
      simp
    have hSecondEven : Even (ordUnit K (diagonalUnitDeterminant second)) := by
      have hPair := (heADC2025Proposition42iOdd (K := K) (k + 1) δ).determinantSquare
      have hBothEven := even_ordUnit_of_square_for_lemma75
        (diagonalUnitDeterminant second * diagonalUnitDeterminant first) hPair
      rw [ordUnit_mul, hFirstOrder, add_zero] at hBothEven
      exact hBothEven
    have hProductEven := even_ordUnit_of_square_for_lemma75
      (a.prefixProduct (2 * k + 5) * diagonalUnitDeterminant second)
      (a.heADC_prefixProduct_det_square_of_ambient _ hsecond)
    rw [ordUnit_mul] at hProductEven
    have hSourceEven := hProductEven.sub hSecondEven
    have : Even (ordUnit K (a.prefixProduct (2 * k + 5))) := by
      simpa using hSourceEven
    exact (hFullNotEven this).elim
  · let ac := a.castLength (by omega :
        ((2 * k + 2) + 1) + 2 = 1 + 2 * ((k + 1) + 1))
    have hPublishedProfile : ∀ i,
        ac.order i = heADCMaximalOrderProfile (K := K) ((k + 1) + 1) ![1] i := by
      intro i
      have h := hProfile ⟨i.val, by omega⟩
      have hConvert := heADCMaximalOrderProfile_unary_eq_ternary
        (K := K) (k + 1) 1 ⟨i.val, by omega⟩
      rw [order_castLength]
      exact h.trans hConvert.symm
    have hiso := (heADC2025Lemma412iiiFirstPublished δ hδ (k + 1)
      ac hA hfirstPi).mpr hPublishedProfile
    exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
      (Classical.choice hiso).symm
  · let ac := a.castLength (by omega :
        ((2 * k + 2) + 1) + 2 = 3 + 2 * (k + 1))
    have hPublishedProfile : ∀ i,
        ac.order i = heADCMaximalOrderProfile (K := K) (k + 1)
          ![0, -(2 * (ramificationIndex K : Int)), 1] i := by
      intro i
      rw [order_castLength]
      exact hProfile ⟨i.val, by omega⟩
    have hiso := (heADC2025Lemma412iiiSecondPublished δ hδ (k + 1)
      ac hA hsecondPi).mpr hPublishedProfile
    exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
      (Classical.choice hiso).symm

/-- The large-gap half of the sufficiency proof in Lemma 7.5. -/
theorem heADC2025Lemma75Sufficiency_of_terminalGap_gt (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hA : Lattice.IsIntegral q L)
    (C : a.HeADCLemma75Conditions k)
    (hTerminalGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ - a.order ⟨2 * k + 3, by omega⟩) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) := by
  rcases C.largeGap hTerminalGap with ⟨hNext, hLast⟩
  exact (a.heADC2025Lemma75_largeGap_isOMaximal k hA C.initial
    hNext hLast).isNADC (2 * k + 3)

/-- Sufficiency in He (2025), Lemma 7.5, with the two terminal-gap
branches recombined. -/
theorem heADC2025Lemma75Sufficiency (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (hA : Lattice.IsIntegral q L)
    (C : a.HeADCLemma75Conditions k) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) := by
  by_cases hGap :
      a.order ⟨2 * k + 4, by omega⟩ - a.order ⟨2 * k + 3, by omega⟩ ≤
        2 * (ramificationIndex K : Int)
  · exact a.heADC2025Lemma75Sufficiency_of_terminalGap_le k hA C hGap
  · exact a.heADC2025Lemma75Sufficiency_of_terminalGap_gt k hA C
      (lt_of_not_ge hGap)

end BONG.GoodBONG

end Bong
