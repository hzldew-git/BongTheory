/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIConstruction
import Bong.Bong.Beli2019Lemma912TypeIIIIndexP

/-!
# Beli (2019), Lemma 9.12: type-III construction in every rank

The coefficient construction itself is meaningful in every rank `3 + T`.
The original wrapper assumed `2 ≤ T` only so that its fourth- and fifth-order
hypotheses could be written without endpoint conventions.  Here those two
hypotheses are requested only when the corresponding coefficient exists.
This gives the literal rank-three and rank-four constructions while retaining
the same proof for all higher ranks.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- The two-step order inequalities for the type-III values, with fourth and
fifth bounds required only when those coordinates exist. -/
theorem typeIIIValues_weak_allRanks
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (hzero : a.order (⟨0, by omega⟩ : Fin (3 + T)) ≤
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)
    (hone : ∀ hT : 0 < T,
      a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 ≤
        a.order (⟨3, by omega⟩ : Fin (3 + T)))
    (htwo : ∀ hT : 1 < T,
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 ≤
        a.order (⟨4, by omega⟩ : Fin (3 + T))) :
    ∀ (i : Fin (3 + T)) (hi : i.val + 2 < 3 + T),
      ordUnit K (typeIIIValues a D i) ≤
        ordUnit K (typeIIIValues a D ⟨i.val + 2, hi⟩) := by
  intro i hi
  by_cases hi0 : i.val = 0
  · have hcurrent : i = (⟨0, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi0
    have hnext : (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
        (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi0]
    rw [hnext, hcurrent, typeIIIValues_zero,
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit,
      ordUnit_typeIIIValues_two]
    exact hzero
  by_cases hi1 : i.val = 1
  · have hT : 0 < T := by omega
    have hcurrent : i = (⟨1, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi1
    have hnext : (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
        (⟨3, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi1]
    rw [hnext, hcurrent, ordUnit_typeIIIValues_one,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit]
    exact hone hT
  by_cases hi2 : i.val = 2
  · have hT : 1 < T := by omega
    have hcurrent : i = (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi2
    have hnext : (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
        (⟨4, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi2]
    rw [hnext, hcurrent, ordUnit_typeIIIValues_two,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit]
    exact htwo hT
  · have hi3 : 3 ≤ i.val := by omega
    have hiNext3 : 3 ≤ i.val + 2 := by omega
    rw [typeIIIValues_of_three_le a D i hi3,
      typeIIIValues_of_three_le a D ⟨i.val + 2, hi⟩ hiNext3]
    unfold GoodBONG.valueUnit
    rw [← a.toBONG.order_eq_ordUnit, ← a.toBONG.order_eq_ordUnit]
    exact a.good i hi

/-- Adjacent admissibility for the type-III values in every rank.  The right
junction exists precisely when `0 < T`. -/
theorem typeIIIValues_adjacent_allRanks
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (hleft : 0 ≤ a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 -
      a.order (⟨0, by omega⟩ : Fin (3 + T)))
    (hright : ∀ hT : 0 < T,
      0 ≤ a.order (⟨3, by omega⟩ : Fin (3 + T)) -
        (a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)) :
    ∀ (i : Fin (3 + T)) (hi : i.val + 1 < 3 + T),
      IsBinaryParameterAdmissible
        (typeIIIValues a D ⟨i.val + 1, hi⟩ / typeIIIValues a D i) := by
  intro i hi
  by_cases hi0 : i.val = 0
  · have hcurrent : i = (⟨0, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi0
    have hnext : (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
        (⟨1, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi0]
    rw [hnext, hcurrent]
    apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_typeIIIValues_one, typeIIIValues_zero,
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit]
    exact hleft
  by_cases hi1 : i.val = 1
  · have hcurrent : i = (⟨1, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi1
    have hnext : (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
        (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi1]
    rw [hnext, hcurrent, typeIIIValues_two, typeIIIValues_one]
    exact D.bong.adjacentParameter_isBinaryParameterAdmissible 0 (by norm_num)
  by_cases hi2 : i.val = 2
  · have hT : 0 < T := by omega
    have hcurrent : i = (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi2
    have hnext : (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
        (⟨3, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi2]
    rw [hnext, hcurrent]
    apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit,
      ordUnit_typeIIIValues_two]
    exact hright hT
  · have hi3 : 3 ≤ i.val := by omega
    have hiNext3 : 3 ≤ i.val + 1 := by omega
    rw [typeIIIValues_of_three_le a D i hi3,
      typeIIIValues_of_three_le a D ⟨i.val + 1, hi⟩ hiNext3]
    exact a.toBONG.adjacentParameter_isBinaryParameterAdmissible i hi

/-- The Lemma 9.11 replacement realizes a good BONG in every rank `3 + T`.
Endpoint order hypotheses are supplied only when their indices exist. -/
theorem exists_beli2019Lemma912TypeIIIRealization_allRanks
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (hboundary :
      (((a.order (⟨2, by omega⟩ : Fin (3 + T)) -
        a.order (⟨1, by omega⟩ : Fin (3 + T)) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (-(a.valueUnit (⟨1, by omega⟩ : Fin (3 + T)) *
          a.valueUnit (⟨2, by omega⟩ : Fin (3 + T)))) = 1)
    (hzero : a.order (⟨0, by omega⟩ : Fin (3 + T)) ≤
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)
    (hone : ∀ hT : 0 < T,
      a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 ≤
        a.order (⟨3, by omega⟩ : Fin (3 + T)))
    (htwo : ∀ hT : 1 < T,
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 ≤
        a.order (⟨4, by omega⟩ : Fin (3 + T)))
    (hleft : 0 ≤ a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 -
      a.order (⟨0, by omega⟩ : Fin (3 + T)))
    (hright : ∀ hT : 0 < T,
      0 ≤ a.order (⟨3, by omega⟩ : Fin (3 + T)) -
        (a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)) :
    ∃ D : Beli2019Lemma911Data a.typeIIIPair,
      Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + T)
        (typeIIIValues a D)) := by
  rcases a.typeIIIPair.beli2019Lemma911 (a.typeIIIPair_boundary hboundary) with
    ⟨D⟩
  refine ⟨D, ?_⟩
  apply BONG.exists_prescribedValuesGoodBONGData a (typeIIIValues a D)
  · exact typeIIIValues_diagonalRepresents a D
  · exact typeIIIValues_weak_allRanks a D hzero hone htwo
  · exact typeIIIValues_adjacent_allRanks a D hleft hright

end BONG.GoodBONG

end Bong
