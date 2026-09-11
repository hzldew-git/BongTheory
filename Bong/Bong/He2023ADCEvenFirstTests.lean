/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenRepresentationBounds
import Bong.Bong.He2023ADCPublishedProfiles

/-!
# The two first-column maximal tests in He (2025), Lemma 6.4

The good BONGs used below are constructed on the actual maximal lattices
from Definition 4.1. Their order and determinant data are proved rather
than supplied as hypotheses by a caller.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A good BONG on the chosen maximal lattice in a displayed diagonal space. -/
noncomputable def heADCMaximalGoodBONG {n : Nat} (w : Fin n → Kˣ) :
    BONG.GoodBONG (BONG.coefficientDiagonalSpace w) (heHuOMaximalLattice w) n :=
  (BONG.GoodBONG.ofLattice (BONG.coefficientDiagonalSpace w)
    (heHuOMaximalLattice w)).castLength (finrank_fin_fun K)

/-- The full value product of a BONG has the determinant class of the
displayed ambient diagonal space. -/
theorem heADCMaximalGoodBONG_prefixProduct_det_square {n : Nat} (w : Fin n → Kˣ) :
    IsSquare ((heADCMaximalGoodBONG w).prefixProduct n * diagonalUnitDeterminant w) := by
  let b := heADCMaximalGoodBONG w
  have hrep : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients w) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents b.valueUnit w).mp
      ⟨b.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
  have h := DiagonalIsometryInvariantLaws.determinant_square b.valueUnit w hrep
  simpa [b, BONG.GoodBONG.prefixProduct, BONG.prefixProduct,
    BONG.GoodBONG.valueUnit, diagonalUnitDeterminant] using h

/-- The binary endpoint profile is alternating throughout the whole tower. -/
theorem heADCMaximalOrderProfile_endpoint (k : Nat) (i : Fin (2 + 2 * k)) :
    heADCMaximalOrderProfile (K := K) k ![0, -(2 * (ramificationIndex K : Int))] i =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
  by_cases hi : i.val < 2 * k
  · simp [heADCMaximalOrderProfile, hi]
  · have hcases : i.val = 2 * k ∨ i.val = 2 * k + 1 := by omega
    rcases hcases with hzero | hone
    · simp [heADCMaximalOrderProfile, hzero, show Even (2 * k) from ⟨k, by omega⟩]
    · have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
      simp [heADCMaximalOrderProfile, hone, hodd,
        show ¬ 2 * k + 1 < 2 * k by omega, show 2 * k + 1 - 2 * k = 1 by omega]

/-- The actual `N_1^n(1)` and `N_1^n(Delta)` good BONGs have the
alternating endpoint orders, without a profile assumption. -/
theorem heADCEvenFirstTest_orders (k : Nat) (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (i : Fin (2 * k + 2)) :
    (heADCMaximalGoodBONG (heADCW1Even k c)).order i =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
  let b := (heADCMaximalGoodBONG (heADCW1Even k c)).castLength
    (by omega : 2 * k + 2 = 2 + 2 * k)
  have hM := heHuOMaximalLattice_isOMaximal (heADCW1Even k c)
  have hprofile : ∀ j, b.order j = heADCMaximalOrderProfile (K := K) k
      ![0, -(2 * (ramificationIndex K : Int))] j := by
    rcases hc with hc | hc
    · subst c
      exact (heADC2025Lemma411iOnePublished k b hM.isIntegral
        (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
    · subst c
      exact (heADC2025Lemma411iDeltaPublished k b hM.isIntegral
        (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
  have h := hprofile ⟨i.val, by omega⟩
  rw [heADCMaximalOrderProfile_endpoint] at h
  simpa only [b, order_castLength] using h

/-- The determinant classes of the two displayed first-column spaces differ. -/
theorem heADCEvenFirstTests_det_not_square (k : Nat) :
    ¬ IsSquare (diagonalUnitDeterminant (heADCW1Even (K := K) k 1) *
      diagonalUnitDeterminant (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)) := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let s : Kˣ := (-1 : Kˣ) ^ (k + 1)
  intro hdet
  rw [diagonalUnitDeterminant_heHuEvenFirst, diagonalUnitDeterminant_heHuEvenFirst,
    mul_one] at hdet
  have hδ : IsSquare δ := by
    have hs : IsSquare (s ^ 2) := ⟨s, by simp only [pow_two]⟩
    have hquot := hdet.div hs
    have hcancel : (s * (s * δ)) / s ^ 2 = δ := by
      simp [pow_two, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    change IsSquare ((s * (s * δ)) / s ^ 2) at hquot
    rwa [hcancel] at hquot
  have htop := quadraticDefect_eq_top_of_isSquare (K := K) hδ
  rw [(Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

/-- The actual good BONGs of the two first-column tests have distinct
determinant square classes, independently of the choice of those BONGs. -/
theorem heADCEvenFirstTests_prefixProduct_not_square (k : Nat) :
    ¬ IsSquare
      ((heADCMaximalGoodBONG (heADCW1Even (K := K) k 1)).prefixProduct (2 * k + 2) *
        (heADCMaximalGoodBONG (heADCW1Even k
          (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)).prefixProduct
            (2 * k + 2)) := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let a := heADCMaximalGoodBONG (heADCW1Even (K := K) k 1)
  let b := heADCMaximalGoodBONG (heADCW1Even k δ)
  intro h
  have hA := heADCMaximalGoodBONG_prefixProduct_det_square (heADCW1Even (K := K) k 1)
  have hB := heADCMaximalGoodBONG_prefixProduct_det_square (heADCW1Even k δ)
  have hdet : IsSquare (diagonalUnitDeterminant (heADCW1Even (K := K) k 1) *
      diagonalUnitDeterminant (heADCW1Even k δ)) :=
    isSquare_mul_trans _ (a.prefixProduct (2 * k + 2)) _
      (by simpa only [mul_comm] using hA)
      (isSquare_mul_trans _ (b.prefixProduct (2 * k + 2)) _ h hB)
  exact heADCEvenFirstTests_det_not_square k hdet

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Representing both nonisometric tests forces a strictly larger ambient
rank. Thus the next-order index in Lemma 6.4(ii) genuinely exists. -/
theorem heADCEvenFirstTests_rank_gt {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hOne : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
      L (heADCN1Even k (1 : Kˣ)).lattice)
    (hDelta : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice) :
    2 * k < m := by
  letI : Module.Finite K V := L.moduleFinite
  obtain ⟨fOne⟩ := hOne
  obtain ⟨fDelta⟩ := hDelta
  have hle := fOne.toLinearMap.finrank_le_finrank_of_injective fOne.injective
  have haRank := a.toBONG.length_eq_finrank
  rw [finrank_fin_fun, ← haRank] at hle
  by_contra hnot
  have hsame : finrank K (Fin (2 * k + 2) → K) = finrank K V := by
    rw [finrank_fin_fun, ← haRank]
    omega
  let g := (fOne.toQuadraticSpaceIsometryOfFinrankEq hsame).trans
    (fDelta.toQuadraticSpaceIsometryOfFinrankEq hsame).symm
  have hrep := (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (heADCW1Even k (1 : Kˣ)) (heADCW1Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)).mp
        ⟨g.toRepresentation⟩
  exact heADCEvenFirstTests_det_not_square k
    (DiagonalIsometryInvariantLaws.determinant_square _ _ hrep)

/-- He (2025), Lemma 6.4(ii), for every even target rank at least two.
The strict rank inequality is derived, not imposed as an extra hypothesis. -/
theorem heADC2025Lemma64ii {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat)
    (hL : Lattice.IsIntegral q L)
    (hOne : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k (1 : Kˣ)))
      L (heADCN1Even k (1 : Kˣ)).lattice)
    (hDelta : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      L (heADCN1Even k
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice) :
    ∃ hrank : 2 * k < m,
      (∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
        if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
      a.order ⟨2 * k + 2, by omega⟩ = 0 := by
  have hrank := a.heADCEvenFirstTests_rank_gt k hOne hDelta
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let bOne := heADCMaximalGoodBONG (heADCW1Even (K := K) k 1)
  let bDelta := heADCMaximalGoodBONG (heADCW1Even k δ)
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  have honePrev : bOne.order ⟨2 * k, by omega⟩ = 0 := by
    simpa [bOne, heven] using heADCEvenFirstTest_orders (K := K) k 1 (Or.inl rfl)
      ⟨2 * k, by omega⟩
  have honeLast : bOne.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    simpa [bOne, Nat.not_even_iff_odd.mpr hodd] using
      heADCEvenFirstTest_orders (K := K) k 1 (Or.inl rfl)
      ⟨2 * k + 1, by omega⟩
  have hdeltaLast : bDelta.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    simpa [bDelta, Nat.not_even_iff_odd.mpr hodd] using
      heADCEvenFirstTest_orders (K := K) k δ (Or.inr rfl)
      ⟨2 * k + 1, by omega⟩
  have C := a.heADCAlternatingPrefix_of_represented_endpoint bOne hrank.le hL hOne
    ⟨2 * k + 1, by omega⟩ hodd (by simpa using honePrev) honeLast
  refine ⟨hrank, ?_, ?_⟩
  · intro i
    rcases Nat.even_or_odd i.val with hi | hi
    · have hnext : i.val + 1 ≤ 2 * k + 1 := by obtain ⟨z, hz⟩ := hi; omega
      have h := C.pairOrdersAndDefects ⟨i.val + 1, by omega⟩ (by simpa using hnext)
        (Even.add_one hi)
      simpa only [Nat.add_sub_cancel, if_pos hi] using h.1
    · have h := C.pairOrdersAndDefects ⟨i.val, by omega⟩ (by simp; omega) hi
      simpa only [if_neg (Nat.not_even_iff_odd.mpr hi)] using h.2.1
  · exact a.heADCBoundaryOrder_zero_of_two_represented_classes bOne bDelta hrank
      ⟨k + 1, by omega⟩ hL hOne hDelta honeLast hdeltaLast
      (heADCEvenFirstTests_prefixProduct_not_square k)

end BONG.GoodBONG

end Bong
