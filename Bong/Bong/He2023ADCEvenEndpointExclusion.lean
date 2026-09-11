/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.AlternatingEndpointEvenOrders
import Bong.Bong.He2023ADCEvenCorankTwoFirst

/-!
# Endpoint-tower exclusions for He (2025), Lemma 6.8(iii)--(iv)

An endpoint tower with even leading orders belongs to the first ambient
column. This also covers a final leading order of two: its normalization
is an ambient square change, not an integral change of the original BONG.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- An all-even-scale endpoint tower cannot belong to either exceptional second column. -/
theorem heADCSecondEndpoint_not_evenTower (k : Nat) (a : GoodBONG q L (2 * k + 2))
    (c : Kˣ) (hc : c = 1 ∨
      c = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hd : HeHuEvenSecondDefined k c)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even k c hd)))
    (hgaps : ∀ t : Fin (k + 1),
      a.order ⟨2 * t.val + 1, by omega⟩ - a.order ⟨2 * t.val, by omega⟩ =
        -(2 * (ramificationIndex K : Int)))
    (heven : ∀ t : Fin (k + 1), Even (a.order ⟨2 * t.val, by omega⟩)) : False := by
  have hclasses : AlternatingEndpointPairClasses (pairs := k + 1) a.valueUnit := by
    intro t
    let i : Fin (2 * k + 2) := ⟨2 * t.val, by omega⟩
    have hnext : i.val + 1 < 2 * k + 2 := by dsimp only [i]; omega
    have hgap : a.order ⟨i.val + 1, hnext⟩ - a.order i =
        -(2 * (ramificationIndex K : Int)) := hgaps t
    have H := a.toBONG.adjacentUnitSquareClass_endpoint_cases i hnext hgap
    exact a.toBONG.adjacentSignedProduct_endpoint_cases i hnext H
  have heven' : ∀ t : Fin (k + 1),
      Even (ordUnit K (a.valueUnit ⟨2 * t.val, by omega⟩)) := by
    intro t
    change Even (ordUnit K (a.toBONG.valueUnit ⟨2 * t.val, by omega⟩))
    rw [← a.toBONG.order_eq_ordUnit]
    exact heven t
  have hfirstEven : ∀ t : Fin (k + 1),
      Even (ordUnit K ((heADCW1Even k c) ⟨2 * t.val, by omega⟩)) := by
    intro t
    rw [heHuLemma45_evenFirst_leadingOrders k c t]
    have H := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at H
    exact ⟨0, by omega⟩
  have hpair := heADC2025Proposition42iEven k c hd
  have hdet := isSquare_mul_trans _ (diagonalUnitDeterminant (heADCW2Even k c hd)) _
    (a.heADC_prefixProduct_det_square_of_ambient _ ambient) hpair.determinantSquare
  have hdet' : IsSquare (diagonalUnitDeterminant a.valueUnit *
      diagonalUnitDeterminant (heADCW1Even k c)) := by
    simpa [diagonalUnitDeterminant, GoodBONG.prefixProduct, BONG.prefixProduct,
      GoodBONG.valueUnit] using hdet
  have hrep := AlternatingEndpointTower.equalDeterminantRepresentation_of_even_leadingOrders
    (pairs := k + 1) a.valueUnit (heADCW1Even k c)
      hclasses (heHuLemma45_evenFirst_pairClasses k c hc)
      heven' hfirstEven hdet'
  have hfirst := a.ambientIsometric_of_diagonalRepresents _ rfl hrep.symm_of_sameRank
  apply hpair.nonisometric
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).mp
  exact ⟨((Classical.choice ambient).symm.trans (Classical.choice hfirst)).toRepresentation⟩

/-- A terminal order `-2e` would make the entire integral lattice an even-scale endpoint tower. -/
theorem heADCSecondEndpoint_last_ne_neg_twoE (k : Nat) (a : GoodBONG q L (2 * k + 2))
    (hIntegral : Lattice.IsIntegral q L) (c : Kˣ)
    (hc : c = 1 ∨ c = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hd : HeHuEvenSecondDefined k c)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even k c hd))) :
    a.order ⟨2 * k + 1, by omega⟩ ≠ -(2 * (ramificationIndex K : Int)) := by
  intro hlast
  have C := a.heHu2022Proposition27iiiiv hIntegral ⟨2 * k + 1, by omega⟩
    (show Odd (2 * k + 1) from ⟨k, rfl⟩) hlast
  have horders (t : Fin (k + 1)) := C.pairOrdersAndDefects ⟨2 * t.val + 1, by omega⟩
    (by apply Fin.mk_le_mk.mpr; omega) (show Odd (2 * t.val + 1) from ⟨t.val, rfl⟩)
  apply a.heADCSecondEndpoint_not_evenTower k c hc hd ambient
  · intro t
    have H := horders t
    have hz : a.order ⟨2 * t.val, by omega⟩ = 0 := by
      simpa only [Nat.add_sub_cancel] using H.1
    rw [hz, H.2.1, sub_zero]
  · intro t
    have H := horders t
    have hz : a.order ⟨2 * t.val, by omega⟩ = 0 := by
      simpa only [Nat.add_sub_cancel] using H.1
    rw [hz]
    exact Even.zero

end BONG.GoodBONG

end Bong
