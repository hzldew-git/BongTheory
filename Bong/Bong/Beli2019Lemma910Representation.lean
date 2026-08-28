/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma910Boundary
import Bong.Bong.PrefixRepresentationExtension
import Bong.Bong.RepresentationDual
import Bong.Bong.BeliLemmas48To410

/-!
# Beli (2019), Lemma 9.10: extending the ternary representation

This file formalizes the duality paragraph of Lemma 9.10.  The first three
coefficients are represented by the ternary construction, and every remaining
coefficient is unchanged.  After reversing the integral dual BONGs, the
unchanged tail becomes a common prefix.  Beli (2003), Lemma 2.7(ii), in the
form `BONG.represents_of_prefixValueEq_of_suffixModels`, then lifts the ternary
dual representation to full rank.  Dualizing once more gives the required
representation of the constructed lattice by the original lattice.
-/

namespace Bong

open Dyadic
open Module

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {M : Lattice K V} {P : Lattice K W} {N : Nat}

/-- The full coefficient realization from Lemma 9.10 is represented by the
original lattice.  This is exactly the reverse-dual use of [B1, Lemma 2.7(ii)]
in the paper. -/
theorem beli2019Lemma910FullCoefficientRealization_represents
    [structuralAmbient : BONGStructuralLaws.{u, v} K]
    [structuralPrefix : BONGStructuralLaws.{u, w} K]
    {R₁ R₂ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + N)
      (beli2019Lemma910Values D a))
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (hternary : Lattice.Represents r r P D.lattice) :
    Lattice.Represents q q M C.lattice := by
  letI : FiniteDimensional K V :=
    a.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K W :=
    reference.toBONG.basis.finiteDimensional_of_finite
  letI : BONGStructuralLaws.{u, v} K := structuralAmbient
  rcases C.bong.exists_reverseDual_with_values with
    ⟨cDual, _hcVectors, hcValues, _hcOrders⟩
  rcases a.exists_reverseDual_with_values with
    ⟨aDual, _haVectors, haValues, _haOrders⟩
  letI : BONGStructuralLaws.{u, w} K := structuralPrefix
  rcases D.bong.exists_reverseDual_with_values with
    ⟨dDual, _hdVectors, hdValues, _hdOrders⟩
  rcases reference.exists_reverseDual_with_values with
    ⟨referenceDual, _hrVectors, hrValues, _hrOrders⟩
  have hternaryDual : Lattice.Represents r r
      (Lattice.dualLattice r D.lattice)
      (Lattice.dualLattice r P) :=
    hternary.dual_of_finrank_eq rfl
  have hprefixDual : ∀ i : Fin N,
      cDual.value ⟨i.val, by omega⟩ =
        aDual.value ⟨i.val, by omega⟩ := by
    intro i
    let fullIndex : Fin (3 + N) := ⟨i.val, by omega⟩
    let originalIndex : Fin (3 + N) := Fin.rev fullIndex
    have horiginalLower : 3 ≤ originalIndex.val := by
      dsimp only [originalIndex, fullIndex]
      simp only [Fin.rev]
      omega
    let tailIndex : Fin N :=
      ⟨originalIndex.val - 3, by
        dsimp only [originalIndex, fullIndex]
        simp only [Fin.rev]
        omega⟩
    have horiginalIndex : originalIndex = Fin.natAdd 3 tailIndex := by
      apply Fin.ext
      dsimp only [tailIndex]
      simp only [Fin.natAdd]
      omega
    rw [hcValues fullIndex, haValues fullIndex]
    have hunit : C.bong.toBONG.valueUnit originalIndex =
        a.toBONG.valueUnit originalIndex := by
      change C.bong.valueUnit originalIndex = a.valueUnit originalIndex
      rw [C.values, horiginalIndex,
        beli2019Lemma910Values_right]
    change (((C.bong.toBONG.valueUnit originalIndex)⁻¹ : Kˣ) : K) =
      (((a.toBONG.valueUnit originalIndex)⁻¹ : Kˣ) : K)
    rw [hunit]
  have htargetSuffix : ∀ j : Fin 3,
      cDual.value ⟨N + j.val, by omega⟩ = dDual.value j := by
    intro j
    let fullIndex : Fin (3 + N) := ⟨N + j.val, by omega⟩
    have hrev : Fin.rev fullIndex = Fin.castAdd N (Fin.rev j) := by
      apply Fin.ext
      simp only [fullIndex, Fin.rev, Fin.castAdd, Fin.castLE]
      omega
    rw [hcValues fullIndex, hdValues j, hrev]
    have hunit : C.bong.toBONG.valueUnit
          (Fin.castAdd N (Fin.rev j)) =
        D.bong.toBONG.valueUnit (Fin.rev j) := by
      change C.bong.valueUnit (Fin.castAdd N (Fin.rev j)) =
        D.bong.valueUnit (Fin.rev j)
      rw [C.values, beli2019Lemma910Values_left]
    rw [hunit]
  have hsourceSuffix : ∀ j : Fin 3,
      aDual.value ⟨N + j.val, by omega⟩ = referenceDual.value j := by
    intro j
    let fullIndex : Fin (3 + N) := ⟨N + j.val, by omega⟩
    have hrev : Fin.rev fullIndex = Fin.castAdd N (Fin.rev j) := by
      apply Fin.ext
      simp only [fullIndex, Fin.rev, Fin.castAdd, Fin.castLE]
      omega
    rw [haValues fullIndex, hrValues j, hrev]
    have hunit : a.toBONG.valueUnit (Fin.castAdd N (Fin.rev j)) =
        reference.toBONG.valueUnit (Fin.rev j) := by
      change a.valueUnit (Fin.castAdd N (Fin.rev j)) =
        reference.valueUnit (Fin.rev j)
      exact (hprefix (Fin.rev j)).symm
    rw [hunit]
  have hdual : Lattice.Represents q q
      (Lattice.dualLattice q C.lattice)
      (Lattice.dualLattice q M) :=
    BONG.represents_of_prefixValueEq_of_suffixModels
      (baseLength := 3) (steps := N)
      cDual.toBONG aDual.toBONG dDual.toBONG referenceDual.toBONG
      hprefixDual htargetSuffix hsourceSuffix hternaryDual
  have hback := hdual.dual_of_finrank_eq (rfl : finrank K V = finrank K V)
  simpa only [Lattice.dualLattice_dualLattice] using hback

end BONG.GoodBONG

end Bong
