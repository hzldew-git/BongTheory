/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Reflexivity
import Bong.Bong.Beli2019SpaceApproximation
import Bong.Bong.DiagonalRepresentationParity
import Bong.Bong.DiagonalTernaryCore
import Bong.Bong.GoodBONGPrefixValues

/-!
# Beli (2019), canonical approximating spaces

A prefix of another good BONG is the approximating space used in the proof
of Corollary 3.11.  This file packages its unit coefficients, identifies its
determinant with the prefix product, and proves the self-approximation and
change-of-BONG statements needed by Lemmas 3.8 and 3.10.
-/

namespace Bong

open Dyadic

universe u v w

namespace DiagonalRepresents

variable {K : Type u} [Field K]

/-- A zero-dimensional diagonal form is represented by every diagonal
form, independently of its vacuous coefficient function. -/
theorem of_source_length_eq_zero
    {m n : Nat} (source : Fin m → K) (target : Fin n → K)
    (hm : m = 0) : DiagonalRepresents source target := by
  subst m
  convert prefixOfLE target (Nat.zero_le n) using 1

end DiagonalRepresents

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Complete good-BONG prefixes on the same ambient quadratic space
represent one another. -/
theorem fullPrefix_represents
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) :
    DiagonalRepresents
      (a.prefixValues (n + 1) (Nat.le_refl _))
      (b.prefixValues (n + 1) (Nat.le_refl _)) := by
  exact a.toBONG.diagonalRepresents_values b.toBONG

/-- Transport a representation between good-BONG prefixes across equal
prefix lengths. -/
theorem prefixRepresents_cast
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    {sourceRank targetRank sourceLength sourceLength' targetLength
      targetLength' : Nat}
    (source : GoodBONG r N sourceRank)
    (target : GoodBONG q L targetRank)
    {sourceBound : sourceLength ≤ sourceRank}
    {sourceBound' : sourceLength' ≤ sourceRank}
    {targetBound : targetLength ≤ targetRank}
    {targetBound' : targetLength' ≤ targetRank}
    (hsource : sourceLength = sourceLength')
    (htarget : targetLength = targetLength')
    (hrep : DiagonalRepresents
      (source.prefixValues sourceLength sourceBound)
      (target.prefixValues targetLength targetBound)) :
    DiagonalRepresents
      (source.prefixValues sourceLength' sourceBound')
      (target.prefixValues targetLength' targetBound') := by
  subst sourceLength'
  subst targetLength'
  simpa only using hrep

/-- Change only the good-BONG target-prefix length in a diagonal
representation. -/
theorem targetPrefixRepresents_cast
    {sourceLength targetRank targetLength targetLength' : Nat}
    (source : Fin sourceLength → K)
    (target : GoodBONG q L targetRank)
    {targetBound : targetLength ≤ targetRank}
    {targetBound' : targetLength' ≤ targetRank}
    (htarget : targetLength = targetLength')
    (hrep : DiagonalRepresents source
      (target.prefixValues targetLength targetBound)) :
    DiagonalRepresents source
      (target.prefixValues targetLength' targetBound') := by
  subst targetLength'
  simpa only using hrep

/-- Change only the good-BONG source-prefix length in a diagonal
representation. -/
theorem sourcePrefixRepresents_cast
    {targetLength sourceRank sourceLength sourceLength' : Nat}
    (source : GoodBONG q L sourceRank)
    (target : Fin targetLength → K)
    {sourceBound : sourceLength ≤ sourceRank}
    {sourceBound' : sourceLength' ≤ sourceRank}
    (hsource : sourceLength = sourceLength')
    (hrep : DiagonalRepresents
      (source.prefixValues sourceLength sourceBound) target) :
    DiagonalRepresents
      (source.prefixValues sourceLength' sourceBound') target := by
  subst sourceLength'
  simpa only using hrep

/-- The internal representation condition of Beli's classification theorem
for two good BONGs of the same lattice. -/
theorem internalRepresentationConditions_sameLattice
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a b : GoodBONG q L (n + 1)) :
    a.InternalRepresentationConditions b := by
  have hconditions :=
    (isometric_iff_classificationConditions
      (QuadraticSpace.isIsometric_refl q) a b).mp
        (Lattice.isIsometric_refl q L)
  exact hconditions.internalRepresentations

/-- A BONG prefix is a two-sided space approximation to itself. -/
theorem isSpaceApproximation_prefixValueUnits
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    a.IsSpaceApproximation i
      (a.prefixValueUnits (i.val + 1) (by omega)) := by
  unfold IsSpaceApproximation IsLeftSpaceApproximation
    IsRightSpaceApproximation
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [a.diagonalUnitDeterminant_prefixValueUnits]
    exact a.isPrefixApproximation_prefixProduct (i.val + 1)
  · intro _
    rw [a.diagonalUnitCoefficients_prefixValueUnits]
    exact a.prefixValues_represents_succ i.val (by omega)
  · rw [a.diagonalUnitDeterminant_prefixValueUnits]
    exact a.isPrefixApproximation_prefixProduct (i.val + 1)
  · intro _
    rw [a.diagonalUnitCoefficients_prefixValueUnits]
    exact a.prefixValues_represents_succ (i.val + 1) (by omega)

/-- The canonical prefix of a second good BONG supplies the conditional
representation bridge required by Lemma 3.8. -/
theorem spaceApproximationRepresentationBridge_prefixValueUnits
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Fin n) :
    a.SpaceApproximationRepresentationBridge a' i
      (a'.prefixValueUnits (i.val + 1) (by omega)) where
  left_iff htrigger := by
    rw [a'.diagonalUnitCoefficients_prefixValueUnits]
    have hself := a'.prefixValues_represents_succ i.val (by omega)
    have htrigger' :=
      (a.leftApproximationTrigger_changeBONG_iff a' i).mp htrigger
    have hcross : DiagonalRepresents
        (a.prefixValues i.val (by omega))
        (a'.prefixValues (i.val + 1) (by omega)) := by
      rcases htrigger' with hzero | ⟨hi, hsum⟩
      · exact DiagonalRepresents.of_source_length_eq_zero
          (a.prefixValues i.val (by omega))
          (a'.prefixValues (i.val + 1) (by omega)) hzero
      · exact (a'.internalRepresentationConditions_sameLattice a) i hi hsum
    exact ⟨fun _ ↦ hself, fun _ ↦ hcross⟩
  right_iff htrigger := by
    rw [a'.diagonalUnitCoefficients_prefixValueUnits]
    have hself := a'.prefixValues_represents_succ (i.val + 1) (by omega)
    have hcross : DiagonalRepresents
        (a'.prefixValues (i.val + 1) (by omega))
        (a.prefixValues (i.val + 2) (by omega)) := by
      rcases htrigger with hlast | ⟨hi, hsum⟩
      · have hfull := a'.fullPrefix_represents a
        have hlength : n + 1 = i.val + 2 := by omega
        have hfull' : DiagonalRepresents
            (a'.prefixValues (i.val + 2) (by omega))
            (a.prefixValues (i.val + 2) (by omega)) :=
          prefixRepresents_cast a' a hlength hlength hfull
        exact hself.trans hfull'
      · let j : Fin n := ⟨i.val + 1, hi⟩
        have hsum' : (2 * ramificationIndex K : ℚ) <
            a.alphaValue ⟨j.val - 1, by omega⟩ + a.alphaValue j := by
          have hpred : (⟨j.val - 1, by omega⟩ : Fin n) = i := by
            apply Fin.ext
            simp [j]
          rw [hpred]
          exact hsum
        have hrep :=
          (a.internalRepresentationConditions_sameLattice a') j
            (by dsimp [j]; omega) hsum'
        exact prefixRepresents_cast a' a (by simp [j]) (by simp [j]) hrep
    exact ⟨fun _ ↦ hself, fun _ ↦ hcross⟩

/-- Lemma 3.8 turns a prefix of a second good BONG into a space
approximation for the first good BONG. -/
theorem isSpaceApproximation_prefixValueUnits_of_bridge
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Fin n)
    (D : SpaceApproximationRepresentationBridge a a' i
      (a'.prefixValueUnits (i.val + 1) (by omega))) :
    a.IsSpaceApproximation i
      (a'.prefixValueUnits (i.val + 1) (by omega)) := by
  exact D.isSpaceApproximation_iff.mpr
    (a'.isSpaceApproximation_prefixValueUnits i)

end BONG.GoodBONG

end Bong
