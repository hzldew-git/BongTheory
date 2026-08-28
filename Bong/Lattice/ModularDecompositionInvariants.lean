/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.OrthogonalDecompositionRankSum

/-!
# Invariants of unordered modular decompositions

The intrinsic scale truncations of a lattice recover the total rank carried
at each modular scale.  Unlike the corresponding strict-Jordan result, the
statements here allow repeated scales and arbitrary component order.  This is
the invariant needed to compare the independently chosen almost-Jordan data
in Beli's Lemma 5.1, including its possible selected/common scale collision.
-/

open scoped BigOperators

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.ModularDecomposition

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The weighted positive scale difference for an unordered modular
decomposition. -/
noncomputable def scalePositiveRankSum {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) : Int :=
  ∑ i, (finrank K (D.component i).carrier : Int) *
    max 0 (r - ordUnit K (D.scaleGenerator i))

/-- The total rank of all modular components having scale order `r`. -/
noncomputable def scaleRankMultiplicity {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) : Int :=
  ∑ i, (finrank K (D.component i).carrier : Int) *
    if ordUnit K (D.scaleGenerator i) = r then 1 else 0

/-- The intrinsic scale truncation computes the positive-rank sum for an
arbitrary modular decomposition; no ordering or distinctness of scales is
needed. -/
theorem volumeOrder_scaleTruncation {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) :
    volumeOrder q (scaleTruncation q L r) =
      volumeOrder q L + 2 * D.scalePositiveRankSum r := by
  classical
  letI (i : Fin t) : Fintype (D.component i).lattice.BasisIndex :=
    Fintype.ofFinite _
  rw [D.toOrthogonalDecomposition.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      D.scaleGenerator D.modular r,
    OrthogonalDecomposition.componentwiseRescaleLattice,
    OrthogonalDecomposition.componentwiseRescaleBasis,
    volumeOrder_basisLattice_unitsSMul,
    D.toOrthogonalDecomposition.basisLattice_componentAmbientBasis]
  unfold scalePositiveRankSum
  congr 2
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [OrthogonalDecomposition.ordUnit_modularScaleTruncationFactor,
    Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [← Module.finrank_eq_card_basis
    (D.component i).lattice.ambientBasis]

/-- The positive-rank sum is intrinsic to the lattice. -/
theorem scalePositiveRankSum_eq {s t : Nat}
    (D : ModularDecomposition q L t) (E : ModularDecomposition q L s)
    (r : Int) :
    D.scalePositiveRankSum r = E.scalePositiveRankSum r := by
  have hD := D.volumeOrder_scaleTruncation r
  have hE := E.volumeOrder_scaleTruncation r
  omega

/-- Total rank carried strictly below the supplied scale order. -/
noncomputable def scaleRankBelow {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) : Int :=
  ∑ i, (finrank K (D.component i).carrier : Int) *
    if ordUnit K (D.scaleGenerator i) < r then 1 else 0

private theorem positivePart_firstDifference (r a : Int) :
    max 0 (r - a) - max 0 (r - 1 - a) =
      if a < r then 1 else 0 := by
  by_cases hlt : a < r
  · have h0 : 0 ≤ r - a := by omega
    have hm : 0 ≤ r - 1 - a := by omega
    rw [if_pos hlt, max_eq_right h0, max_eq_right hm]
    omega
  · have h0 : r - a ≤ 0 := by omega
    have hm : r - 1 - a ≤ 0 := by omega
    rw [if_neg hlt, max_eq_left h0, max_eq_left hm]
    omega

/-- The rank below `r` is the first difference of the intrinsic positive
rank sum. -/
theorem scaleRankBelow_eq_firstDifference {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) :
    D.scaleRankBelow r =
      D.scalePositiveRankSum r - D.scalePositiveRankSum (r - 1) := by
  classical
  unfold scaleRankBelow scalePositiveRankSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (finrank K (D.component i).carrier : Int) *
          (if ordUnit K (D.scaleGenerator i) < r then 1 else 0) =
        (finrank K (D.component i).carrier : Int) *
          (max 0 (r - ordUnit K (D.scaleGenerator i)) -
            max 0 (r - 1 - ordUnit K (D.scaleGenerator i))) := by
      rw [positivePart_firstDifference]
    _ = (finrank K (D.component i).carrier : Int) *
            max 0 (r - ordUnit K (D.scaleGenerator i)) -
          (finrank K (D.component i).carrier : Int) *
            max 0 (r - 1 - ordUnit K (D.scaleGenerator i)) := by
      ring

/-- The total rank below any scale is independent of the modular
decomposition. -/
theorem scaleRankBelow_eq {s t : Nat}
    (D : ModularDecomposition q L t) (E : ModularDecomposition q L s)
    (r : Int) :
    D.scaleRankBelow r = E.scaleRankBelow r := by
  rw [D.scaleRankBelow_eq_firstDifference,
    E.scaleRankBelow_eq_firstDifference,
    D.scalePositiveRankSum_eq E r,
    D.scalePositiveRankSum_eq E (r - 1)]

private theorem positivePart_secondDifference (r a : Int) :
    max 0 (r + 1 - a) - 2 * max 0 (r - a) +
        max 0 (r - 1 - a) =
      if a = r then 1 else 0 := by
  by_cases heq : a = r
  · subst a
    simp
  · by_cases hlt : a < r
    · have hm : 0 ≤ r - 1 - a := by omega
      have h0 : 0 ≤ r - a := by omega
      have hp : 0 ≤ r + 1 - a := by omega
      rw [if_neg heq, max_eq_right hp, max_eq_right h0,
        max_eq_right hm]
      omega
    · have hgt : r < a := by omega
      have hp : r + 1 - a ≤ 0 := by omega
      have h0 : r - a ≤ 0 := by omega
      have hm : r - 1 - a ≤ 0 := by omega
      rw [if_neg heq, max_eq_left hp, max_eq_left h0,
        max_eq_left hm]
      omega

/-- Scale multiplicity is the discrete second difference of the intrinsic
positive-rank sum. -/
theorem scaleRankMultiplicity_eq_secondDifference {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) :
    D.scaleRankMultiplicity r =
      D.scalePositiveRankSum (r + 1) -
        2 * D.scalePositiveRankSum r +
          D.scalePositiveRankSum (r - 1) := by
  classical
  unfold scaleRankMultiplicity scalePositiveRankSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (finrank K (D.component i).carrier : Int) *
          (if ordUnit K (D.scaleGenerator i) = r then 1 else 0) =
        (finrank K (D.component i).carrier : Int) *
          (max 0 (r + 1 - ordUnit K (D.scaleGenerator i)) -
            2 * max 0 (r - ordUnit K (D.scaleGenerator i)) +
              max 0 (r - 1 - ordUnit K (D.scaleGenerator i))) := by
      rw [positivePart_secondDifference]
    _ = (finrank K (D.component i).carrier : Int) *
            max 0 (r + 1 - ordUnit K (D.scaleGenerator i)) -
          2 * ((finrank K (D.component i).carrier : Int) *
            max 0 (r - ordUnit K (D.scaleGenerator i))) +
          (finrank K (D.component i).carrier : Int) *
            max 0 (r - 1 - ordUnit K (D.scaleGenerator i)) := by
      ring

/-- Total rank at every scale is independent of the chosen unordered
modular decomposition. -/
theorem scaleRankMultiplicity_eq {s t : Nat}
    (D : ModularDecomposition q L t) (E : ModularDecomposition q L s)
    (r : Int) :
    D.scaleRankMultiplicity r = E.scaleRankMultiplicity r := by
  rw [D.scaleRankMultiplicity_eq_secondDifference,
    E.scaleRankMultiplicity_eq_secondDifference,
    D.scalePositiveRankSum_eq E (r + 1),
    D.scalePositiveRankSum_eq E r,
    D.scalePositiveRankSum_eq E (r - 1)]

/-! ## Reverse duality -/

/-- Reverse the component order after taking componentwise integral duals. -/
noncomputable def reverseDual {t : Nat}
    (D : ModularDecomposition q L t) :
    ModularDecomposition q (Lattice.dualLattice q L) t where
  toOrthogonalDecomposition := D.toOrthogonalDecomposition.reverseDual
  scaleGenerator := fun i ↦ (D.scaleGenerator (Fin.rev i))⁻¹
  modular := by
    intro i
    exact (D.modular (Fin.rev i)).dual
  component_finrank_pos := by
    intro i
    exact D.component_finrank_pos (Fin.rev i)

@[simp]
theorem reverseDual_component {t : Nat}
    (D : ModularDecomposition q L t) (i : Fin t) :
    D.reverseDual.component i = (D.component (Fin.rev i)).dual :=
  rfl

@[simp]
theorem reverseDual_scaleGenerator {t : Nat}
    (D : ModularDecomposition q L t) (i : Fin t) :
    D.reverseDual.scaleGenerator i =
      (D.scaleGenerator (Fin.rev i))⁻¹ :=
  rfl

@[simp]
theorem reverseDual_componentRank {t : Nat}
    (D : ModularDecomposition q L t) (i : Fin t) :
    finrank K (D.reverseDual.component i).carrier =
      finrank K (D.component (Fin.rev i)).carrier :=
  rfl

/-- Reverse duality negates scale orders and preserves their total ranks. -/
theorem reverseDual_scaleRankMultiplicity {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) :
    D.reverseDual.scaleRankMultiplicity r =
      D.scaleRankMultiplicity (-r) := by
  classical
  unfold scaleRankMultiplicity
  simp only [reverseDual_componentRank, reverseDual_scaleGenerator,
    ordUnit_inv]
  calc
    (∑ i, (finrank K (D.component (Fin.rev i)).carrier : Int) *
        if -ordUnit K (D.scaleGenerator (Fin.rev i)) = r then 1 else 0) =
        ∑ i, (finrank K (D.component i).carrier : Int) *
          if -ordUnit K (D.scaleGenerator i) = r then 1 else 0 := by
      exact Fin.rev_bijective.sum_comp (fun i ↦
        (finrank K (D.component i).carrier : Int) *
          if -ordUnit K (D.scaleGenerator i) = r then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      by_cases h : ordUnit K (D.scaleGenerator i) = -r
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

/-- The rank below the negative dual scale is the complementary original
rank strictly above that scale. -/
theorem reverseDual_scaleRankBelow {t : Nat}
    (D : ModularDecomposition q L t) (r : Int) :
    D.reverseDual.scaleRankBelow (-r) =
      (finrank K V : Int) - D.scaleRankBelow (r + 1) := by
  classical
  unfold scaleRankBelow
  simp only [reverseDual_componentRank, reverseDual_scaleGenerator,
    ordUnit_inv]
  rw [show (∑ i, (finrank K (D.component (Fin.rev i)).carrier : Int) *
      if -ordUnit K (D.scaleGenerator (Fin.rev i)) < -r then 1 else 0) =
      ∑ i, (finrank K (D.component i).carrier : Int) *
        if -ordUnit K (D.scaleGenerator i) < -r then 1 else 0 by
    exact Fin.rev_bijective.sum_comp (fun i ↦
      (finrank K (D.component i).carrier : Int) *
        if -ordUnit K (D.scaleGenerator i) < -r then 1 else 0)]
  have htotal := D.toOrthogonalDecomposition.finrank_eq_sum_components
  have htotalInt : (finrank K V : Int) =
      ∑ i, (finrank K (D.component i).carrier : Int) := by
    exact_mod_cast htotal
  rw [htotalInt]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : ordUnit K (D.scaleGenerator i) < r + 1
  · have hnot : ¬ -ordUnit K (D.scaleGenerator i) < -r := by omega
    simp [h, hnot]
  · have hdual : -ordUnit K (D.scaleGenerator i) < -r := by omega
    simp [h, hdual]

end Lattice.ModularDecomposition

end Bong
