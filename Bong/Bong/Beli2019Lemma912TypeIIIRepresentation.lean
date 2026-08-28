/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIConstruction
import Bong.Bong.PrefixRepresentationExtension
import Bong.Bong.RepresentationDual
import Bong.Bong.BeliLemmas48To410
/-!
# Beli (2019), Lemma 9.12: the type-III representation

The binary non-generator sublattice produced by Lemma 9.11 is first adjoined
to the unchanged initial coefficient. Beli (2003), Lemma 2.7(ii), then extends
that ternary representation across the common tail after reverse duality.
Dualizing back proves that the original lattice represents the prescribed
Type-III coefficient realization.
-/


namespace Bong

open Dyadic
open Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

noncomputable def typeIIIInitialThreeSegment
    (a : GoodBONG q L (3 + T)) :
    BONG.SegmentWitness a.toBONG 0 3 (by omega) :=
  a.toBONG.segmentWitness 0 3 (by omega)

noncomputable def typeIIIInitialThree
    (a : GoodBONG q L (3 + T)) : GoodBONG
      (q.restrict a.typeIIIInitialThreeSegment.carrier
        a.typeIIIInitialThreeSegment.nondegenerate)
      a.typeIIIInitialThreeSegment.lattice 3 :=
  a.typeIIIInitialThreeSegment.toGoodBONG a.good

theorem beli2019Lemma912TypeIIIRealization_represents
    [BeliCorollary44Laws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    Lattice.Represents q q L C.lattice := by
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  let aThree := a.typeIIIInitialThree
  let cThree := C.bong.typeIIIInitialThree
  have hpair : Lattice.Represents
      (q.restrict a.typeIIIPairSegment.carrier
        a.typeIIIPairSegment.nondegenerate)
      (q.restrict a.typeIIIPairSegment.carrier
        a.typeIIIPairSegment.nondegenerate)
      a.typeIIIPairSegment.lattice D.lemma71.lattice :=
    Lattice.represents_of_le _ D.lemma71.indexP.lattice_le
  have hprefix : ∀ i : Fin 1,
      aThree.value ⟨i.val, by omega⟩ =
        cThree.value ⟨i.val, by omega⟩ := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change a.typeIIIInitialThreeSegment.bong.value (0 : Fin 3) =
      C.bong.typeIIIInitialThreeSegment.bong.value (0 : Fin 3)
    rw [BONG.SegmentWitness.value_eq, BONG.SegmentWitness.value_eq]
    have hunit : a.valueUnit (0 : Fin (3 + T)) =
        C.bong.valueUnit (0 : Fin (3 + T)) := by
      rw [C.values]
      simp [typeIIIValues]
    change a.value (0 : Fin (3 + T)) =
      C.bong.value (0 : Fin (3 + T))
    exact congrArg Units.val hunit
  have htargetSuffix : ∀ j : Fin 2,
      aThree.value ⟨1 + j.val, by omega⟩ =
        a.typeIIIPair.value j := by
    intro j
    change a.typeIIIInitialThreeSegment.bong.value
        ⟨1 + j.val, by omega⟩ =
      a.typeIIIPairSegment.bong.value j
    rw [BONG.SegmentWitness.value_eq, BONG.SegmentWitness.value_eq]
    congr 1
    apply Fin.ext
    simp only [BONG.SegmentWitness.sourceIndex_val]
    omega
  have hsourceSuffix : ∀ j : Fin 2,
      cThree.value ⟨1 + j.val, by omega⟩ = D.bong.value j := by
    intro j
    have hunit : C.bong.valueUnit
          (C.bong.typeIIIInitialThreeSegment.sourceIndex
            ⟨1 + j.val, by omega⟩) =
        D.bong.valueUnit j := by
      rw [C.values]
      fin_cases j
      · simpa [typeIIIInitialThreeSegment,
          BONG.SegmentWitness.sourceIndex] using typeIIIValues_one a D
      · simpa [typeIIIInitialThreeSegment,
          BONG.SegmentWitness.sourceIndex] using typeIIIValues_two a D
    apply congrArg Units.val at hunit
    change C.bong.typeIIIInitialThreeSegment.bong.value
        ⟨1 + j.val, by omega⟩ = D.bong.value j
    rw [BONG.SegmentWitness.value_eq]
    exact hunit
  have hternary : Lattice.Represents
      (q.restrict a.typeIIIInitialThreeSegment.carrier
        a.typeIIIInitialThreeSegment.nondegenerate)
      (q.restrict C.bong.typeIIIInitialThreeSegment.carrier
        C.bong.typeIIIInitialThreeSegment.nondegenerate)
      a.typeIIIInitialThreeSegment.lattice
      C.bong.typeIIIInitialThreeSegment.lattice :=
    BONG.represents_of_prefixValueEq_of_suffixModels
      (baseLength := 2) (steps := 1)
      aThree.toBONG cThree.toBONG a.typeIIIPair.toBONG D.bong
      hprefix htargetSuffix hsourceSuffix hpair
  rcases C.bong.exists_reverseDual_with_values with
    ⟨cDual, _hcVectors, hcValues, _hcOrders⟩
  rcases a.exists_reverseDual_with_values with
    ⟨aDual, _haVectors, haValues, _haOrders⟩
  rcases cThree.exists_reverseDual_with_values with
    ⟨cThreeDual, _hcThreeVectors, hcThreeValues, _hcThreeOrders⟩
  rcases aThree.exists_reverseDual_with_values with
    ⟨aThreeDual, _haThreeVectors, haThreeValues, _haThreeOrders⟩
  have hfinrankThree : Module.finrank K
        C.bong.typeIIIInitialThreeSegment.carrier =
      Module.finrank K a.typeIIIInitialThreeSegment.carrier := by
    rw [← cThree.toBONG.length_eq_finrank,
      ← aThree.toBONG.length_eq_finrank]
  have hternaryDual : Lattice.Represents
      (q.restrict C.bong.typeIIIInitialThreeSegment.carrier
        C.bong.typeIIIInitialThreeSegment.nondegenerate)
      (q.restrict a.typeIIIInitialThreeSegment.carrier
        a.typeIIIInitialThreeSegment.nondegenerate)
      (Lattice.dualLattice
        (q.restrict C.bong.typeIIIInitialThreeSegment.carrier
          C.bong.typeIIIInitialThreeSegment.nondegenerate)
        C.bong.typeIIIInitialThreeSegment.lattice)
      (Lattice.dualLattice
        (q.restrict a.typeIIIInitialThreeSegment.carrier
          a.typeIIIInitialThreeSegment.nondegenerate)
        a.typeIIIInitialThreeSegment.lattice) :=
    hternary.dual_of_finrank_eq hfinrankThree
  have hprefixDual : ∀ i : Fin T,
      cDual.value ⟨i.val, by omega⟩ =
        aDual.value ⟨i.val, by omega⟩ := by
    intro i
    let fullIndex : Fin (3 + T) := ⟨i.val, by omega⟩
    let originalIndex : Fin (3 + T) := Fin.rev fullIndex
    have horiginalLower : 3 ≤ originalIndex.val := by
      dsimp only [originalIndex, fullIndex]
      simp only [Fin.rev]
      omega
    rw [hcValues fullIndex, haValues fullIndex]
    have hunit : C.bong.valueUnit originalIndex =
        a.valueUnit originalIndex := by
      rw [C.values, typeIIIValues_of_three_le a D originalIndex
        horiginalLower]
    change (((C.bong.valueUnit originalIndex)⁻¹ : Kˣ) : K) =
      (((a.valueUnit originalIndex)⁻¹ : Kˣ) : K)
    rw [hunit]
  have htargetSuffix : ∀ j : Fin 3,
      cDual.value ⟨T + j.val, by omega⟩ = cThreeDual.value j := by
    intro j
    let fullIndex : Fin (3 + T) := ⟨T + j.val, by omega⟩
    have hrev : Fin.rev fullIndex =
        C.bong.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j) := by
      apply Fin.ext
      simp only [fullIndex, Fin.rev,
        BONG.SegmentWitness.sourceIndex_val]
      omega
    rw [hcValues fullIndex, hcThreeValues j, hrev]
    have hvalue : C.bong.valueUnit
          (C.bong.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j)) =
        cThree.valueUnit (Fin.rev j) := by
      dsimp only [cThree, typeIIIInitialThree, GoodBONG.valueUnit]
      exact (C.bong.typeIIIInitialThreeSegment.valueUnit_eq (Fin.rev j)).symm
    change (((C.bong.valueUnit
      (C.bong.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j)))⁻¹ : Kˣ) : K) =
      (((cThree.valueUnit (Fin.rev j))⁻¹ : Kˣ) : K)
    rw [hvalue]
  have hsourceSuffix : ∀ j : Fin 3,
      aDual.value ⟨T + j.val, by omega⟩ = aThreeDual.value j := by
    intro j
    let fullIndex : Fin (3 + T) := ⟨T + j.val, by omega⟩
    have hrev : Fin.rev fullIndex =
        a.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j) := by
      apply Fin.ext
      simp only [fullIndex, Fin.rev,
        BONG.SegmentWitness.sourceIndex_val]
      omega
    rw [haValues fullIndex, haThreeValues j, hrev]
    have hvalue : a.valueUnit
          (a.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j)) =
        aThree.valueUnit (Fin.rev j) := by
      dsimp only [aThree, typeIIIInitialThree, GoodBONG.valueUnit]
      exact (a.typeIIIInitialThreeSegment.valueUnit_eq (Fin.rev j)).symm
    change (((a.valueUnit
      (a.typeIIIInitialThreeSegment.sourceIndex (Fin.rev j)))⁻¹ : Kˣ) : K) =
      (((aThree.valueUnit (Fin.rev j))⁻¹ : Kˣ) : K)
    rw [hvalue]
  have hdual : Lattice.Represents q q
      (Lattice.dualLattice q C.lattice)
      (Lattice.dualLattice q L) :=
    BONG.represents_of_prefixValueEq_of_suffixModels
      (baseLength := 3) (steps := T)
      cDual.toBONG aDual.toBONG cThreeDual.toBONG aThreeDual.toBONG
      hprefixDual htargetSuffix hsourceSuffix hternaryDual
  have hback := hdual.dual_of_finrank_eq
    (rfl : finrank K V = finrank K V)
  simpa only [Lattice.dualLattice_dualLattice] using hback

end BONG.GoodBONG

end Bong
