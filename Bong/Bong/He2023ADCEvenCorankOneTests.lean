/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenPenultimateObstruction

/-!
# The concrete maximal tests in the proof of He (2025), Theorem 6.1

The corank-one ambient alternative is proved for the actual named target
pair before applying the definition of n-ADC. No testing-table premise is
left to a caller.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- For an n-ADC lattice, an actual maximal diagonal target is represented
exactly when its displayed ambient coefficients are represented. -/
theorem heADCMaximal_represents_iff_diagonalRepresents {m n : Nat}
    (a : GoodBONG q L m) (hADC : Lattice.IsNADC.{u, u, u} q L n) (w : Fin n → Kˣ) :
    Lattice.Represents q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w) ↔
      DiagonalRepresents (diagonalUnitCoefficients w) (diagonalUnitCoefficients a.valueUnit) := by
  constructor
  · intro hrep
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents w a.valueUnit).mp
    exact (show (BONG.coefficientDiagonalSpace a.valueUnit).Represents q from
      ⟨a.toBONG.exactDiagonalizationIsometry.toRepresentation⟩).trans hrep.ambient
  · intro hrep
    apply hADC.represents _ _ (finrank_fin_fun K) (heHuOMaximalLattice_isOMaximal w).isIntegral
    exact (show q.Represents (BONG.coefficientDiagonalSpace a.valueUnit) from
      ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩).trans
        ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents w a.valueUnit).2 hrep)

/-- The corank-one part of He (2025), Lemma 4.6(i), on the actual even
N1/N2 pair. The exactly-one ambient alternative is discharged here. -/
theorem heADC2025Lemma46iEvenCorankOne (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2)) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined k c) :
    (Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
        L (heADCN1Even k c).lattice ∧
      ¬ Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k c hdefined))
        L (heADCN2Even k c hdefined).lattice) ∨
    (¬ Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
        L (heADCN1Even k c).lattice ∧
      Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k c hdefined))
        L (heADCN2Even k c hdefined).lattice) := by
  have H := heADC2025Lemma45iCodimensionOne (heADCW1Even k c) (heADCW2Even k c hdefined)
    (heADC2025Proposition42iEven k c hdefined) a.valueUnit
  change (_ ∧ ¬ _) ∨ (¬ _ ∧ _) at H
  have hOne := a.heADCMaximal_represents_iff_diagonalRepresents hADC (heADCW1Even k c)
  have hTwo := a.heADCMaximal_represents_iff_diagonalRepresents hADC (heADCW2Even k c hdefined)
  rcases H with ⟨hfirst, hnotsecond⟩ | ⟨hnotfirst, hsecond⟩
  · exact Or.inl ⟨hOne.mpr hfirst, fun h ↦ hnotsecond (hTwo.mp h)⟩
  · exact Or.inr ⟨fun h ↦ hnotfirst (hOne.mp h), hTwo.mpr hsecond⟩

/-- An n-ADC lattice of corank one represents an actual unit-uniformizer
maximal target whose good-BONG orders are derived, not assumed. -/
theorem heADCCorankOne_uniformizerTest (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (ε : Kˣ) (hε : IsValuationUnit K (ε : K)) :
    ∃ w : Fin (2 * k + 2) → Kˣ,
      Lattice.Represents q (BONG.coefficientDiagonalSpace w) L (heHuOMaximalLattice w) ∧
      ∀ i, (heADCMaximalGoodBONG w).order i =
        heADCMaximalOrderProfile (K := K) k ![0, 1] ⟨i.val, by omega⟩ := by
  let c := ε * uniformizerPowerUnit K 1
  have hd : HeHuEvenSecondDefined k c := Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare
  rcases a.heADC2025Lemma46iEvenCorankOne k hADC c hd with ⟨hrep, _⟩ | ⟨_, hrep⟩
  · refine ⟨heADCW1Even k c, hrep, ?_⟩
    exact heADCUniformizerTest_orders k ε hε _ (heHuOMaximalLattice_isOMaximal _).isIntegral
      (Or.inl (Lattice.isIsometric_refl _ _))
  · refine ⟨heADCW2Even k c hd, hrep, ?_⟩
    exact heADCUniformizerTest_orders k ε hε _ (heHuOMaximalLattice_isOMaximal _).isIntegral
      (Or.inr (Lattice.isIsometric_refl _ _))

/-- The necessary order profile established in the first paragraph of
the proof of He (2025), Theorem 6.1. This is not yet the maximality converse. -/
theorem heADCEvenCorankOne_orders (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2)) :
    (∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
    a.order ⟨2 * k, by omega⟩ = 0 ∧
    (a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
      a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int)) ∧
    (a.order ⟨2 * k + 2, by omega⟩ = 0 ∨ a.order ⟨2 * k + 2, by omega⟩ = 1) := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hcases :
      (∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
        if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
      ((a.order ⟨2 * k, by omega⟩ = 0 ∧
        (a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
          a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))) ∨
        (a.order ⟨2 * k, by omega⟩ = 1 ∧
          a.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int))) := by
    rcases a.heADC2025Lemma46iEvenCorankOne k hADC δ (heHuLemma43_evenSecondDefined k) with
      ⟨hrep, _⟩ | ⟨_, hrep⟩
    · obtain ⟨_, horders, _⟩ := a.heADC2025Lemma64i k δ (Or.inr rfl) hADC.isIntegral hrep
      refine ⟨fun i ↦ horders ⟨i.val, by omega⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
      · simpa only [if_pos (show Even (2 * k) from ⟨k, by omega⟩)] using
          horders ⟨2 * k, by omega⟩
      · have hodd : ¬ Even (2 * k + 1) := by rintro ⟨s, hs⟩; omega
        simpa only [if_neg hodd] using horders ⟨2 * k + 1, by omega⟩
    · obtain ⟨_, hhead, hlast⟩ := a.heADC2025Lemma64iii k δ (heHuLemma43_evenSecondDefined k)
        (Or.inr rfl) hADC.isIntegral hrep
      exact ⟨hhead, hlast⟩
  have hOne : IsValuationUnit K ((1 : Kˣ) : K) := by simp [IsValuationUnit]
  obtain ⟨w, hrep, hTarget⟩ := a.heADCCorankOne_uniformizerTest k hADC 1 hOne
  let b := heADCMaximalGoodBONG w
  have C := (a.heADC2025Theorem36 (by omega) hrep.ambient b).mp hrep
  obtain ⟨hhead, hcases⟩ := hcases
  rcases hcases with ⟨hprevious, hlast⟩ | ⟨hprevious, hlast⟩
  · refine ⟨hhead, hprevious, hlast, ?_⟩
    have hnext : a.order ⟨2 * k + 2, by omega⟩ < 2 := by
      by_contra hnot
      have hfail := heADC2025Lemma65i_of_orders k a b hhead hprevious hlast
        (by omega) hTarget
      exact hfail (C.defectCondition ⟨2 * k + 2, by omega, by omega, le_rfl⟩)
    have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
    have hnonneg := ((a.heHu2022Proposition27i hADC.isIntegral).oddIndexed
      ⟨2 * k + 2, by omega⟩ ⟨2 * k + 2, by omega⟩ le_rfl heven heven).1
    omega
  · have hfail := heADC2025Lemma65ii_of_orders k a b hhead hprevious hlast hTarget
    exact False.elim (hfail (C.defectCondition ⟨2 * k + 1, by omega, by omega, by omega⟩))

end BONG.GoodBONG

end Bong
