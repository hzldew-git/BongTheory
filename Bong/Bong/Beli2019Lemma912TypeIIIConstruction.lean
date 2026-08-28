/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIINormalization
import Bong.Bong.Beli2019Lemma911
import Bong.Bong.GoodBONGPrescribedValues
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 9.12: construction of the type-III BONG

After normalization of the second adjacent pair, Lemma 9.11 replaces that
binary block by its non-generator sublattice. This file inserts the resulting
pair between the unchanged first coefficient and the unchanged tail, checks
the numerical good-BONG criteria, and realizes the prescribed values inside
the original quadratic space.

The rank is written as 3 + T so the coefficient list is literally a three-term
head followed by the common tail.
-/

open Bong Dyadic
open Module

universe u v w

namespace Bong.BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {T N : Nat}

noncomputable def typeIIIPairSegment
    (a : GoodBONG q L (3 + T)) :
    BONG.SegmentWitness a.toBONG 1 2 (by omega) :=
  a.toBONG.segmentWitness 1 2 (by omega)

noncomputable def typeIIIPair
    (a : GoodBONG q L (3 + T)) : GoodBONG
      (q.restrict a.typeIIIPairSegment.carrier
        a.typeIIIPairSegment.nondegenerate)
      a.typeIIIPairSegment.lattice 2 :=
  a.typeIIIPairSegment.toGoodBONG a.good

theorem typeIIIPair_boundary
    (a : GoodBONG q L (3 + T))
    (hboundary :
      (((a.order (⟨2, by omega⟩ : Fin (3 + T)) -
        a.order (⟨1, by omega⟩ : Fin (3 + T)) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (-(a.valueUnit (⟨1, by omega⟩ : Fin (3 + T)) *
          a.valueUnit (⟨2, by omega⟩ : Fin (3 + T)))) = 1) :
    (((a.typeIIIPair.orderGap 0 : Int) : ℚ) : WithTop ℚ) +
        a.typeIIIPair.adjacentDefect 0 = 1 := by
  unfold typeIIIPair orderGap adjacentDefect adjacentProduct
  unfold GoodBONG.order GoodBONG.valueUnit BONG.SegmentWitness.toGoodBONG
  rw [a.typeIIIPairSegment.order_eq, a.typeIIIPairSegment.order_eq,
    a.typeIIIPairSegment.valueUnit_eq, a.typeIIIPairSegment.valueUnit_eq]
  unfold GoodBONG.order GoodBONG.valueUnit at hboundary
  simpa [BONG.SegmentWitness.sourceIndex] using hboundary

variable [BeliCorollary44Laws.{u, v} K]

noncomputable def typeIIIValues
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (i : Fin (3 + T)) : Kˣ :=
  if i.val = 1 then D.bong.valueUnit 0
  else if i.val = 2 then D.bong.valueUnit 1
  else a.valueUnit i

@[simp] theorem typeIIIValues_zero
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    typeIIIValues a D (⟨0, by omega⟩ : Fin (3 + T)) =
      a.valueUnit ⟨0, by omega⟩ := by
  simp [typeIIIValues]

@[simp] theorem typeIIIValues_one
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    typeIIIValues a D (⟨1, by omega⟩ : Fin (3 + T)) =
      D.bong.valueUnit 0 := by
  simp [typeIIIValues]

@[simp] theorem typeIIIValues_two
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    typeIIIValues a D (⟨2, by omega⟩ : Fin (3 + T)) =
      D.bong.valueUnit 1 := by
  simp [typeIIIValues]

@[simp] theorem typeIIIValues_of_three_le
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (i : Fin (3 + T)) (hi : 3 ≤ i.val) :
    typeIIIValues a D i = a.valueUnit i := by
  simp [typeIIIValues, show i.val ≠ 1 by omega, show i.val ≠ 2 by omega]

theorem ordUnit_typeIIIValues_one
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    ordUnit K (typeIIIValues a D (⟨1, by omega⟩ : Fin (3 + T))) =
      a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 := by
  rw [typeIIIValues_one, ← D.bong.order_eq_ordUnit, D.firstOrder]
  congr 1
  unfold typeIIIPair GoodBONG.order BONG.SegmentWitness.toGoodBONG
  rw [a.typeIIIPairSegment.order_eq]
  congr 2

theorem ordUnit_typeIIIValues_two
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    ordUnit K (typeIIIValues a D (⟨2, by omega⟩ : Fin (3 + T))) =
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 := by
  rw [typeIIIValues_two, ← D.bong.order_eq_ordUnit, D.secondOrder]
  congr 1
  unfold typeIIIPair GoodBONG.order BONG.SegmentWitness.toGoodBONG
  rw [a.typeIIIPairSegment.order_eq]
  congr 2

theorem typeIIIValues_diagonalRepresents
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) :
    DiagonalRepresents
      (diagonalUnitCoefficients (typeIIIValues a D)) a.toBONG.value := by
  let tailUnits : Fin T → Kˣ := fun j => a.valueUnit (Fin.natAdd 3 j)
  let tail : Fin T → K := fun j => (tailUnits j : K)
  have hpair : DiagonalRepresents D.bong.value a.typeIIIPair.toBONG.value :=
    D.bong.diagonalRepresents_values a.typeIIIPair.toBONG
  have hhead := diagonalRepresents_cons hpair (a.value 0)
  have hfull := diagonalRepresents_append hhead tail
  have hsource : diagonalUnitCoefficients (typeIIIValues a D) =
      Fin.append (Fin.cons (a.value 0) D.bong.value) tail := by
    funext i
    refine Fin.addCases (m := 3) (n := T) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, diagonalUnitCoefficients]
      fin_cases j
      · simp [typeIIIValues, GoodBONG.coe_valueUnit, GoodBONG.value]
        apply congrArg a.toBONG.value
        apply Fin.ext
        rfl
      · simp [typeIIIValues, GoodBONG.value]
      · simp [typeIIIValues, GoodBONG.value]
        rw [show (2 : Fin 3) = (1 : Fin 2).succ by
          apply Fin.ext
          rfl]
        symm
        exact Fin.cons_succ (α := fun _ : Fin 3 => K)
          (a.toBONG.value 0) D.bong.value (1 : Fin 2)
    · simp only [Fin.append_right, diagonalUnitCoefficients]
      rw [typeIIIValues_of_three_le a D _ (by
        simp only [Fin.val_natAdd]
        omega)]
  have htarget : Fin.append
        (Fin.cons (a.value 0) a.typeIIIPair.toBONG.value) tail =
      a.toBONG.value := by
    funext i
    refine Fin.addCases (m := 3) (n := T) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      fin_cases j
      · simp [typeIIIPair, GoodBONG.value,
          BONG.SegmentWitness.toGoodBONG]
        apply congrArg a.toBONG.value
        apply Fin.ext
        rfl
      · simp [typeIIIPair, GoodBONG.value,
          BONG.SegmentWitness.toGoodBONG]
        apply congrArg a.toBONG.value
        apply Fin.ext
        rfl
      · simp [typeIIIPair, GoodBONG.value,
          BONG.SegmentWitness.toGoodBONG]
        rw [show (2 : Fin 3) = (1 : Fin 2).succ by
          apply Fin.ext
          rfl, Fin.cons_succ]
        rw [a.typeIIIPairSegment.value_eq]
        apply congrArg a.toBONG.value
        apply Fin.ext
        rfl
    · simp only [Fin.append_right]
      simp [tail, tailUnits, GoodBONG.coe_valueUnit, GoodBONG.value]
  rw [hsource, ← htarget]
  exact hfull

theorem typeIIIValues_weak
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (hT : 2 ≤ T)
    (hzero : a.order (⟨0, by omega⟩ : Fin (3 + T)) ≤
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)
    (hone : a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 ≤
      a.order (⟨3, by omega⟩ : Fin (3 + T)))
    (htwo : a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 ≤
      a.order (⟨4, by omega⟩ : Fin (3 + T))) :
    ∀ (i : Fin (3 + T)) (hi : i.val + 2 < 3 + T),
      ordUnit K (typeIIIValues a D i) ≤
        ordUnit K (typeIIIValues a D ⟨i.val + 2, hi⟩) := by
  intro i hi
  by_cases hi0 : i.val = 0
  · have hcurrent : i = (⟨0, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi0
    have hnext :
        (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
          (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi0]
    rw [hnext, hcurrent, typeIIIValues_zero,
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit,
      ordUnit_typeIIIValues_two]
    exact hzero
  by_cases hi1 : i.val = 1
  · have hcurrent : i = (⟨1, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi1
    have hnext :
        (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
          (⟨3, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi1]
    rw [hnext, hcurrent, ordUnit_typeIIIValues_one,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit]
    exact hone
  by_cases hi2 : i.val = 2
  · have hcurrent : i = (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi2
    have hnext :
        (⟨i.val + 2, hi⟩ : Fin (3 + T)) =
          (⟨4, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi2]
    rw [hnext, hcurrent, ordUnit_typeIIIValues_two,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit]
    exact htwo
  · have hi3 : 3 ≤ i.val := by omega
    have hiNext3 : 3 ≤ i.val + 2 := by omega
    rw [typeIIIValues_of_three_le a D i hi3,
      typeIIIValues_of_three_le a D ⟨i.val + 2, hi⟩ hiNext3]
    unfold GoodBONG.valueUnit
    rw [← a.toBONG.order_eq_ordUnit, ← a.toBONG.order_eq_ordUnit]
    exact a.good i hi

theorem typeIIIValues_adjacent
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (hT : 2 ≤ T)
    (hleft : 0 ≤ a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 -
      a.order (⟨0, by omega⟩ : Fin (3 + T)))
    (hright : 0 ≤ a.order (⟨3, by omega⟩ : Fin (3 + T)) -
      (a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)) :
    ∀ (i : Fin (3 + T)) (hi : i.val + 1 < 3 + T),
      IsBinaryParameterAdmissible
        (typeIIIValues a D ⟨i.val + 1, hi⟩ / typeIIIValues a D i) := by
  intro i hi
  by_cases hi0 : i.val = 0
  · have hcurrent : i = (⟨0, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi0
    have hnext :
        (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
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
    have hnext :
        (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
          (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi1]
    rw [hnext, hcurrent, typeIIIValues_two, typeIIIValues_one]
    exact D.bong.adjacentParameter_isBinaryParameterAdmissible 0 (by norm_num)
  by_cases hi2 : i.val = 2
  · have hcurrent : i = (⟨2, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa using hi2
    have hnext :
        (⟨i.val + 1, hi⟩ : Fin (3 + T)) =
          (⟨3, by omega⟩ : Fin (3 + T)) := by
      apply Fin.ext
      simpa [hi2]
    rw [hnext, hcurrent]
    apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      typeIIIValues_of_three_le a D _ (by norm_num),
      GoodBONG.valueUnit, ← a.toBONG.order_eq_ordUnit,
      ordUnit_typeIIIValues_two]
    exact hright
  · have hi3 : 3 ≤ i.val := by omega
    have hiNext3 : 3 ≤ i.val + 1 := by omega
    rw [typeIIIValues_of_three_le a D i hi3,
      typeIIIValues_of_three_le a D ⟨i.val + 1, hi⟩ hiNext3]
    exact a.toBONG.adjacentParameter_isBinaryParameterAdmissible i hi

theorem exists_beli2019Lemma912TypeIIIRealization
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (hT : 2 ≤ T)
    (hboundary :
      (((a.order (⟨2, by omega⟩ : Fin (3 + T)) -
        a.order (⟨1, by omega⟩ : Fin (3 + T)) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (-(a.valueUnit (⟨1, by omega⟩ : Fin (3 + T)) *
          a.valueUnit (⟨2, by omega⟩ : Fin (3 + T)))) = 1)
    (hzero : a.order (⟨0, by omega⟩ : Fin (3 + T)) ≤
      a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)
    (hone : a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 ≤
      a.order (⟨3, by omega⟩ : Fin (3 + T)))
    (htwo : a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1 ≤
      a.order (⟨4, by omega⟩ : Fin (3 + T)))
    (hleft : 0 ≤ a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1 -
      a.order (⟨0, by omega⟩ : Fin (3 + T)))
    (hright : 0 ≤ a.order (⟨3, by omega⟩ : Fin (3 + T)) -
      (a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1)) :
    ∃ D : Beli2019Lemma911Data a.typeIIIPair,
      Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + T)
        (typeIIIValues a D)) := by
  rcases a.typeIIIPair.beli2019Lemma911 (a.typeIIIPair_boundary hboundary) with ⟨D⟩
  refine ⟨D, ?_⟩
  apply BONG.exists_prescribedValuesGoodBONGData a (typeIIIValues a D)
  · exact typeIIIValues_diagonalRepresents a D
  · exact typeIIIValues_weak a D hT hzero hone htwo
  · exact typeIIIValues_adjacent a D hT hleft hright

omit [BeliCorollary44Laws.{u, v} K] in
/-- In the type-III branch the second source order cannot lie below the first.
The alpha-two bound gives a gap of at most one, while the first gap is even. -/
theorem beli2019Lemma912_secondOrder_ge_firstOrder_of_typeIII
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hparams : Beli2019Lemma912TypeIIIParameters a c) :
    a.order (0 : Fin (N + 5)) ≤ a.order (1 : Fin (N + 5)) := by
  have hgapLe := a.orderGap_le_one_of_alphaValue_le_one
    (1 : Fin (N + 4)) (by rw [hparams.2.2])
  unfold orderGap at hgapLe
  change a.order (2 : Fin (N + 5)) - a.order (1 : Fin (N + 5)) ≤ 1 at hgapLe
  rw [← profile.firstThird_eq] at hgapLe
  rcases profile.firstGap_even with ⟨z, hz⟩
  unfold orderGap at hz
  change a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)) = z + z at hz
  omega

/-- A normalized type-III branch satisfies all numerical hypotheses of the
generic coefficient construction, hence yields a realized good BONG with the
second and third orders shifted by one. -/
theorem exists_beli2019Lemma912TypeIIIRealization_of_normalization
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hparams : Beli2019Lemma912TypeIIIParameters a c)
    (S : Beli2019Lemma912TypeIIINormalizationData a) :
    let hlength : N + 5 = 3 + (N + 2) := by omega
    let source := S.transformed.castLength hlength
    ∃ D : Beli2019Lemma911Data source.typeIIIPair,
      Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + (N + 2))
        (typeIIIValues source D)) := by
  let hlength : N + 5 = 3 + (N + 2) := by omega
  let source := S.transformed.castLength hlength
  have hsourceOrderNat (i : Nat) (hi : i < 3 + (N + 2))
      (hout : i < N + 5) :
      source.order (⟨i, hi⟩ : Fin (3 + (N + 2))) =
        S.transformed.order (⟨i, hout⟩ : Fin (N + 5)) := by
    simp only [source, GoodBONG.order_castLength]
  have hsourceValueNat (i : Nat) (hi : i < 3 + (N + 2))
      (hout : i < N + 5) :
      source.valueUnit (⟨i, hi⟩ : Fin (3 + (N + 2))) =
        S.transformed.valueUnit (⟨i, hout⟩ : Fin (N + 5)) := by
    simp only [source, valueUnit_castLength]
  have hsourceOrderOriginal (i : Nat) (hi : i < 3 + (N + 2))
      (hout : i < N + 5) :
      source.order (⟨i, hi⟩ : Fin (3 + (N + 2))) =
        a.order (⟨i, hout⟩ : Fin (N + 5)) := by
    rw [hsourceOrderNat i hi hout]
    exact (S.sameOrders _).symm
  have horderZero : source.order (⟨0, by omega⟩ : Fin (3 + (N + 2))) =
      a.order (0 : Fin (N + 5)) := by
    simpa using hsourceOrderOriginal 0 (by omega) (by omega)
  have horderOne : source.order (⟨1, by omega⟩ : Fin (3 + (N + 2))) =
      a.order (1 : Fin (N + 5)) := by
    simpa using hsourceOrderOriginal 1 (by omega) (by omega)
  have horderTwo : source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) =
      a.order (2 : Fin (N + 5)) := by
    calc
      source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) =
          a.order (⟨2, by omega⟩ : Fin (N + 5)) :=
        hsourceOrderOriginal 2 (by omega) (by omega)
      _ = a.order (2 : Fin (N + 5)) := by
        congr 1
  have horderThree : source.order (⟨3, by omega⟩ : Fin (3 + (N + 2))) =
      a.order (3 : Fin (N + 5)) := by
    calc
      source.order (⟨3, by omega⟩ : Fin (3 + (N + 2))) =
          a.order (⟨3, by omega⟩ : Fin (N + 5)) :=
        hsourceOrderOriginal 3 (by omega) (by omega)
      _ = a.order (3 : Fin (N + 5)) := by
        congr 1
  have horderFour : source.order (⟨4, by omega⟩ : Fin (3 + (N + 2))) =
      a.order (4 : Fin (N + 5)) := by
    calc
      source.order (⟨4, by omega⟩ : Fin (3 + (N + 2))) =
          a.order (⟨4, by omega⟩ : Fin (N + 5)) :=
        hsourceOrderOriginal 4 (by omega) (by omega)
      _ = a.order (4 : Fin (N + 5)) := by
        congr 1
  have hboundary :
      (((source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) -
        source.order (⟨1, by omega⟩ : Fin (3 + (N + 2))) : Int) : ℚ) :
          WithTop ℚ) +
        defectOrder (-(source.valueUnit
            (⟨1, by omega⟩ : Fin (3 + (N + 2))) *
          source.valueUnit (⟨2, by omega⟩ : Fin (3 + (N + 2))))) = 1 := by
    rw [hsourceOrderNat 2 (by omega) (by omega),
      hsourceOrderNat 1 (by omega) (by omega),
      hsourceValueNat 1 (by omega) (by omega),
      hsourceValueNat 2 (by omega) (by omega)]
    have h := S.pairBoundary
    unfold orderGap adjacentDefect adjacentProduct at h
    have hcast : Fin.castSucc (1 : Fin (N + 4)) =
        (⟨1, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    have hsucc : Fin.succ (1 : Fin (N + 4)) =
        (⟨2, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc] at h
    exact h
  have hsecondGe : a.order (0 : Fin (N + 5)) ≤
      a.order (1 : Fin (N + 5)) :=
    beli2019Lemma912_secondOrder_ge_firstOrder_of_typeIII (alpha := alphaV) (parity := parityV)
      a c profile hparams
  have hfirstFifth : a.order (0 : Fin (N + 5)) <
      a.order (4 : Fin (N + 5)) :=
    beli2019Lemma912_first_lt_fifth_of_typeIII
      (alphaV := alphaV) (alphaW := alphaW) (parityW := parityW)
      a c profile hfirst hparams
  have hzero : source.order (⟨0, by omega⟩ : Fin (3 + (N + 2))) ≤
      source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) + 1 := by
    rw [horderZero, horderTwo]
    have := profile.firstThird_eq
    omega
  have hone : source.order (⟨1, by omega⟩ : Fin (3 + (N + 2))) + 1 ≤
      source.order (⟨3, by omega⟩ : Fin (3 + (N + 2))) := by
    rw [horderOne, horderThree]
    have := profile.second_lt_fourth
    omega
  have htwo : source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) + 1 ≤
      source.order (⟨4, by omega⟩ : Fin (3 + (N + 2))) := by
    rw [horderTwo, horderFour]
    have := profile.firstThird_eq
    omega
  have hleft : 0 ≤
      source.order (⟨1, by omega⟩ : Fin (3 + (N + 2))) + 1 -
        source.order (⟨0, by omega⟩ : Fin (3 + (N + 2))) := by
    rw [horderOne, horderZero]
    omega
  have hright : 0 ≤
      source.order (⟨3, by omega⟩ : Fin (3 + (N + 2))) -
        (source.order (⟨2, by omega⟩ : Fin (3 + (N + 2))) + 1) := by
    rw [horderThree, horderTwo]
    have houter := profile.firstThird_eq
    have hfourth := profile.second_lt_fourth
    omega
  exact exists_beli2019Lemma912TypeIIIRealization source (by omega)
    hboundary hzero hone htwo hleft hright


end Bong.BONG.GoodBONG
