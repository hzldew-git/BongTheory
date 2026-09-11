/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankTwoGenericTests

/-!
# Nonexceptional columns in He (2025), Lemma 6.8(v)--(vi)

The parameter domain excludes the square and discriminant square classes.
Parameters are normalized internally, so the conclusion does not depend
on the chosen scalar representative of a nonexceptional square class.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Internal selector for the two actual nonexceptional even space columns. -/
noncomputable def heADCEvenSharpSpace (second : Bool) (k : Nat) (c : Kˣ)
    (hs : HeHuSharpDomain c) : Fin (2 * k + 2) → Kˣ :=
  if second then heADCW2Even k c (Or.inr hs.notSquare) else heADCW1Even k c

/-- Both selected columns have the same published signed determinant class. -/
theorem heADCEvenSharpSpace_determinantClass (second : Bool) (k : Nat)
    (c : Kˣ) (hs : HeHuSharpDomain c) :
    IsSquare (diagonalUnitDeterminant (heADCEvenSharpSpace second k c hs) *
      ((-1 : Kˣ) ^ (k + 1) * c)) := by
  cases second with
  | false => exact heADCEvenFirst_determinantClass k c
  | true => exact heADCEvenSecond_determinantClass k c (Or.inr hs.notSquare)

/-- Removing a coordinate square preserves both nonexceptional class exclusions. -/
theorem heADCSharpDomain_of_mul_square (c d s : Kˣ) (hs : HeHuSharpDomain c)
    (h : c = d * s ^ 2) : HeHuSharpDomain d := by
  constructor
  · intro hd
    apply hs.notSquare
    rw [h]
    exact hd.mul ⟨s, pow_two s⟩
  · intro hd
    apply hs.notDiscriminantSquare
    rw [h]
    have H := hd.mul (show IsSquare (s ^ 2) from ⟨s, pow_two s⟩)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using H

/-- Each actual nonexceptional column is invariant under a square change of parameter. -/
theorem heADCEvenSharpSpace_represents_of_mul_square (second : Bool) (k : Nat)
    (c d s : Kˣ) (hc : HeHuSharpDomain c) (hd : HeHuSharpDomain d)
    (h : c = d * s ^ 2) :
    DiagonalRepresents (diagonalUnitCoefficients (heADCEvenSharpSpace second k c hc))
      (diagonalUnitCoefficients (heADCEvenSharpSpace second k d hd)) := by
  cases second with
  | false =>
      exact Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square k c d s h
  | true =>
      exact Lattice.QuadraticLatticeModel.heHuEvenSecond_represents_of_mul_square
        k c d s (Or.inr hc.notSquare) h

namespace Lattice

/-- A normalized nonexceptional ambient parameter gives an actual maximal source lattice. -/
theorem heADCEvenCorankTwoSharp_normalized (second : Bool) (k : Nat)
    (c : Kˣ) (hs : HeHuSharpDomain c) (hnorm : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second (k + 1) c hs))) :
    IsOMaximal q L := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 2 * k + 4)
  let b := a.castLength (by omega : 2 * k + 4 = 2 + 2 * (k + 1))
  have horders := a.heADCEvenCorankTwo_sharp_orders k c hs _ (by omega) hADC ambient
    (by simpa only [Nat.add_assoc] using heADCEvenSharpSpace_determinantClass second (k + 1) c hs)
  have horders' : ∀ i, b.order i = heADCMaximalOrderProfile (K := K) (k + 1)
      ![0, 1 - ((quadraticDefect K c).toNat : Int)] i := by
    intro i
    simpa only [b, order_castLength] using horders ⟨i.val, by omega⟩
  have hiso : IsIsometric q
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second (k + 1) c hs))
      L (heHuOMaximalLattice (heADCEvenSharpSpace second (k + 1) c hs)) := by
    rcases hnorm with hzero | hone
    · have hunit := (isValuationUnit_iff_ordUnit_eq_zero K c).mpr hzero
      cases second with
      | false =>
          exact (heADC2025Lemma411iiiUnitFirstPublished c hunit hs (k + 1) b
            hADC.isIntegral ambient).mpr horders'
      | true =>
          exact (heADC2025Lemma411iiiUnitSecondPublished c hunit hs (k + 1) b
            hADC.isIntegral ambient).mpr horders'
    · obtain ⟨δ, hδ, hc⟩ : ∃ δ : Kˣ, IsValuationUnit K (δ : K) ∧
          c = δ * uniformizerPowerUnit K 1 := by
        refine ⟨normalizedUnitPart K c, normalizedUnitPart_isValuationUnit K c, ?_⟩
        simpa only [hone, mul_comm] using (uniformizerPower_mul_normalizedUnitPart K c).symm
      subst c
      have hdefect : quadraticDefect K (δ * uniformizerPowerUnit K 1) = 0 :=
        quadraticDefect_eq_zero_of_odd_ordUnit _ (by rw [hone]; exact odd_one)
      have hordersπ : ∀ i, b.order i =
          heADCMaximalOrderProfile (K := K) (k + 1) ![0, 1] i := by
        simpa only [hdefect, ENat.toNat_zero, Nat.cast_zero, sub_zero] using horders'
      cases second with
      | false =>
          exact (heADC2025Lemma411iiiUniformizerFirstPublished δ hδ (k + 1) b
            hADC.isIntegral ambient).mpr hordersπ
      | true =>
          exact (heADC2025Lemma411iiiUniformizerSecondPublished δ hδ (k + 1) b
            hADC.isIntegral ambient).mpr hordersπ
  exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry (Classical.choice hiso).symm

/-- Internal square normalization removes any valuation restriction on the parameter. -/
theorem heADCEvenCorankTwoSharp_isOMaximal (second : Bool) (k : Nat)
    (c : Kˣ) (hs : HeHuSharpDomain c) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second (k + 1) c hs))) :
    IsOMaximal q L := by
  obtain ⟨d, s, hdOrder, hc⟩ := exists_order_zero_or_one_mul_square_any (K := K) c
  have hd := heADCSharpDomain_of_mul_square c d s hs hc
  have hrep := heADCEvenSharpSpace_represents_of_mul_square second (k + 1) c d s hs hd hc
  have hiso := QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
    _ _ hrep
  exact heADCEvenCorankTwoSharp_normalized second k d hd hdOrder hADC
    ⟨(Classical.choice ambient).trans (Classical.choice hiso)⟩

/-- Lemma 6.8(v) on the nonexceptional square-class domain, independent of representatives. -/
theorem heADC2025Lemma68v (k : Nat) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c))
      L (heADCN1Even (k + 1) c).lattice :=
  oMaximal_isIsometric_of_isometric
    (heADCEvenCorankTwoSharp_isOMaximal false k c hs hADC ambient)
    (heHuOMaximalLattice_isOMaximal _) ambient

/-- Lemma 6.8(vi) on the nonexceptional square-class domain, independent of representatives. -/
theorem heADC2025Lemma68vi (k : Nat) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c (Or.inr hs.notSquare)))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c (Or.inr hs.notSquare)))
      L (heADCN2Even (k + 1) c (Or.inr hs.notSquare)).lattice :=
  oMaximal_isIsometric_of_isometric
    (heADCEvenCorankTwoSharp_isOMaximal true k c hs hADC ambient)
    (heHuOMaximalLattice_isOMaximal _) ambient

end Lattice

end Bong
