/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaOddBinaryWeightCoordinates
import Bong.Lattice.Omeara9318EvenParity

/-!
# O'Meara 93:10 in both weight branches

For every binary unimodular lattice and every prescribed norm-generator
vector, O'Meara 93:10 gives integral coordinates `A(a, beta)` with
`beta` in the weight ideal.  The nonterminal branch is the exact odd-weight
calculation, while the terminal branch is the already proved `beta = 2 zeta`
calculation.  This file only joins those two unconditional constructions.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The branch-independent coordinate output of O'Meara 93:10. -/
structure Omeara9310GeneralWeightCoordinatesData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) where
  beta : K
  beta_mem_weight : beta ∈ weightIdeal q L
  nondegenerate : q.quadratic x * beta ≠ 1
  isometry : Isometry q
    (QuadraticSpace.omearaGeneralPlane
      (q.quadratic x) beta nondegenerate)
    L (hyperbolicPlaneLattice (K := K))

/-- O'Meara 93:10 for an arbitrary binary unimodular lattice.  No parity
or strict-weight hypothesis remains in the statement. -/
noncomputable def omeara9310GeneralWeightCoordinatesData
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 2)
    (x : V) (hx : IsNormGenerator q L x)
    (hxne : q.quadratic x ≠ 0) :
    Omeara9310GeneralWeightCoordinatesData q L x := by
  let a : Kˣ := Units.mk0 (q.quadratic x) hxne
  have ha : IsNormGeneratorValue q L a :=
    hx.isNormGeneratorValue hxne
  by_cases hterminal : weightIdeal q L = twoScaleIdeal q L
  · let D := omeara9310BinaryWeightData
      q L x hmodular hrank hx hterminal
    have hpos : 0 < finrank K V := by omega
    have hbeta : (2 : K) * D.zeta ∈ weightIdeal q L := by
      rw [hterminal,
        twoScaleIdeal_eq_principalIdeal_two_of_unimodular hmodular hpos]
      simpa only [mul_comm] using
        (mul_mem_principalIdeal_of_mem_integerRing
          (K := K) (2 : K) D.zeta D.zeta_integral)
    exact
      { beta := (2 : K) * D.zeta
        beta_mem_weight := hbeta
        nondegenerate := D.nondegenerate
        isometry := D.isometry }
  · have hodd : Odd (ordUnit K a + weightIdealOrder q L) := by
      have hconditions := (beli2009Lemma210 a ha
        (Beli2009WeightIdealData.weight q L)
        (twoScaleIdeal_le_weightIdeal q L)).mp rfl
      exact hconditions.2.resolve_left hterminal
    have hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L := by
      have hle : weightIdealOrder q L ≤ canonicalTwoScaleOrder q L := by
        rw [weightIdealOrder_eq_canonicalWeightOrder a ha]
        exact canonicalWeightOrder_le_twoScaleOrder ha
      apply lt_of_le_of_ne hle
      intro heq
      apply hterminal
      calc
        weightIdeal q L =
            powerIdeal (K := K) (weightIdealOrder q L) :=
          weightIdeal_eq_powerIdeal q L
        _ = powerIdeal (K := K) (canonicalTwoScaleOrder q L) := by
          rw [heq]
        _ = twoScaleIdeal q L :=
          (twoScaleIdeal_eq_powerIdeal_canonicalTwoScaleOrder ha).symm
    let D := omeara9310OddWeightCoordinatesData
      hmodular hrank x hx hxne hodd hlt
    exact
      { beta := D.beta
        beta_mem_weight := D.beta_mem_weight
        nondegenerate := D.nondegenerate
        isometry := D.isometry }

end Lattice

end Bong
