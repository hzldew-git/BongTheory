/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma715
import Bong.Bong.He2023ADCOddMaximalStructure

/-!
# He (2025), Definition 7.16 and Remark 7.17

This file represents `M_{nu,r}^{n+2}(c)` by the property that defines its
isometry class.  The two ambient columns are an explicit finite type.  The
index bound, normalized parameter order, ADC property, ambient space, and
penultimate BONG order all remain visible in the definition.
-/

namespace Bong

open Dyadic Module

universe u

/-- The two ambient-space columns `nu in {1,2}` in Definition 7.16. -/
inductive HeADC716Column
  | one
  | two
  deriving DecidableEq, Fintype

namespace HeADC716Column

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The odd-dimensional diagonal space in the selected column. -/
noncomputable def coefficients (nu : HeADC716Column) (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  match nu with
  | one => heADCW1Odd pairs c
  | two => heADCW2Odd pairs c

end HeADC716Column

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Definition 7.16.  This is the defining property of the
isometry class denoted by `M_{nu,r}^{n+2}(c)` in the paper. -/
structure HeADC2025Definition716 (k rIndex : Nat) (nu : HeADC716Column)
    (c : Kˣ) (a : GoodBONG q L (2 * k + 5)) : Prop where
  indexBound : rIndex ≤ ramificationIndex K
  parameterOrder : ordUnit K c = 0 ∨ ordUnit K c = 1
  nADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)
  ambient : q.IsIsometric
    (BONG.coefficientDiagonalSpace (nu.coefficients (k + 1) c))
  penultimate : a.order ⟨2 * k + 3, by omega⟩ = -(2 * (rIndex : Int))

/-- The even interval in Theorem 7.4 has the unique source shape `-2r`
with `0 <= r <= e`. -/
private theorem heADC2025Remark717_existsIndex (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k) :
    ∃ rIndex : Nat, rIndex ≤ ramificationIndex K ∧
      a.order ⟨2 * k + 3, by omega⟩ = -(2 * (rIndex : Int)) := by
  rcases C.penultimate.1 with ⟨z, hz⟩
  have hzNonpositive : z ≤ 0 := by
    have hupper := C.penultimate.2.2
    omega
  let rIndex := Int.toNat (-z)
  have hrCast : (rIndex : Int) = -z := by
    dsimp only [rIndex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨rIndex, ?_, ?_⟩
  · have hlower := C.penultimate.2.1
    have hrCastBound : (rIndex : Int) ≤ (ramificationIndex K : Int) := by
      rw [hrCast]
      omega
    exact_mod_cast hrCastBound
  · rw [hrCast]
    omega

/-- He (2025), Remark 7.17: two realizations of the same displayed symbol
are integrally isometric. -/
theorem heADC2025Remark717_unique (k rIndex : Nat)
    (nu : HeADC716Column) (c : Kˣ)
    (a : GoodBONG q L (2 * k + 5))
    (b : GoodBONG s M (2 * k + 5))
    (A : HeADC2025Definition716 k rIndex nu c a)
    (B : HeADC2025Definition716 k rIndex nu c b) :
    Lattice.IsIsometric q s L M := by
  apply (a.heADC2025Lemma715 k b A.nADC B.nADC).2
  constructor
  · exact ⟨(Classical.choice A.ambient).trans
      (Classical.choice B.ambient).symm⟩
  · exact A.penultimate.trans B.penultimate.symm

/-- He (2025), Remark 7.17: every odd-corank-two `n`-ADC lattice belongs to
one of the classes introduced in Definition 7.16. -/
theorem heADC2025Remark717_exhaustion (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) :
    ∃ nu rIndex c, HeADC2025Definition716 k rIndex nu c a := by
  have C := a.heADC2025Theorem74Necessity k hADC
  obtain ⟨rIndex, hrBound, hrOrder⟩ :=
    a.heADC2025Remark717_existsIndex k C
  obtain ⟨delta, hdeltaUnit, hambient⟩ :=
    a.exists_heADCOddNormalizedAmbient (k + 1)
  have hdeltaOrder : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdeltaUnit
  have hdeltaPiOrder :
      ordUnit K (delta * uniformizerPowerUnit K 1) = 1 := by
    rw [ordUnit_mul, ordUnit_uniformizerPowerUnit, hdeltaOrder]
    omega
  rcases hambient with hfirst | hsecond | hfirstPi | hsecondPi
  · refine ⟨HeADC716Column.one, rIndex, delta, ?_⟩
    exact
      { indexBound := hrBound
        parameterOrder := Or.inl hdeltaOrder
        nADC := hADC
        ambient := by
          simpa only [HeADC716Column.coefficients] using hfirst
        penultimate := hrOrder }
  · refine ⟨HeADC716Column.two, rIndex, delta, ?_⟩
    exact
      { indexBound := hrBound
        parameterOrder := Or.inl hdeltaOrder
        nADC := hADC
        ambient := by
          simpa only [HeADC716Column.coefficients] using hsecond
        penultimate := hrOrder }
  · refine ⟨HeADC716Column.one, rIndex,
      delta * uniformizerPowerUnit K 1, ?_⟩
    exact
      { indexBound := hrBound
        parameterOrder := Or.inr hdeltaPiOrder
        nADC := hADC
        ambient := by
          simpa only [HeADC716Column.coefficients] using hfirstPi
        penultimate := hrOrder }
  · refine ⟨HeADC716Column.two, rIndex,
      delta * uniformizerPowerUnit K 1, ?_⟩
    exact
      { indexBound := hrBound
        parameterOrder := Or.inr hdeltaPiOrder
        nADC := hADC
        ambient := by
          simpa only [HeADC716Column.coefficients] using hsecondPi
        penultimate := hrOrder }

end BONG.GoodBONG

end Bong
