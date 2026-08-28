/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma910Ternary
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.GoodBONGPrescribedValues

/-!
# Beli (2019), Lemma 9.10: assembling the unchanged tail

The paper replaces the first three BONG coefficients by the ternary lattice
from Lemma 9.9 and leaves every coefficient from the fourth onward fixed.
This file defines that coefficient family, proves that its complete diagonal
space is the original ambient quadratic space, and realizes it as a good
BONG once the two elementary Beli-2006 numerical criteria are supplied.

The remaining Lemma 9.10 boundary file proves those criteria from
`R₁ = R₃`, `R₄ ≥ R₂ + 2`, and the defect estimate at the pair `(b₃,a₄)`.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {M : Lattice K V} {P : Lattice K W} {N : Nat}

/-- The coefficient family `[b₁,b₂,b₃,a₄,…,aₙ]` used in Lemma 9.10. -/
noncomputable def beli2019Lemma910Values
    {R₁ R₂ β₁ : Int}
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (a : GoodBONG q M (3 + N)) : Fin (3 + N) → Kˣ :=
  Fin.append D.bong.valueUnit
    (fun j : Fin N => a.valueUnit (Fin.natAdd 3 j))

@[simp]
theorem beli2019Lemma910Values_left
    {R₁ R₂ β₁ : Int}
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (a : GoodBONG q M (3 + N)) (i : Fin 3) :
    beli2019Lemma910Values D a (Fin.castAdd N i) = D.bong.valueUnit i := by
  simp [beli2019Lemma910Values]

@[simp]
theorem beli2019Lemma910Values_right
    {R₁ R₂ β₁ : Int}
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (a : GoodBONG q M (3 + N)) (j : Fin N) :
    beli2019Lemma910Values D a (Fin.natAdd 3 j) =
      a.valueUnit (Fin.natAdd 3 j) := by
  simp [beli2019Lemma910Values]

@[simp]
theorem ordUnit_beli2019Lemma910Values_left
    {R₁ R₂ β₁ : Int}
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (a : GoodBONG q M (3 + N)) (i : Fin 3) :
    ordUnit K (beli2019Lemma910Values D a (Fin.castAdd N i)) =
      D.bong.order i := by
  rw [beli2019Lemma910Values_left]
  exact (D.bong.toBONG.order_eq_ordUnit i).symm

@[simp]
theorem ordUnit_beli2019Lemma910Values_right
    {R₁ R₂ β₁ : Int}
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (a : GoodBONG q M (3 + N)) (j : Fin N) :
    ordUnit K (beli2019Lemma910Values D a (Fin.natAdd 3 j)) =
      a.order (Fin.natAdd 3 j) := by
  rw [beli2019Lemma910Values_right]
  exact (a.toBONG.order_eq_ordUnit (Fin.natAdd 3 j)).symm

/-- Replacing the ternary prefix and retaining the tail preserves the full
ambient diagonal quadratic space. -/
theorem beli2019Lemma910Values_diagonalRepresents
    {R₁ R₂ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (beli2019Lemma910Values D a))
      a.toBONG.value := by
  let commonUnits : Fin N → Kˣ :=
    fun j => a.valueUnit (Fin.natAdd 3 j)
  let common : Fin N → K := fun j => (commonUnits j : K)
  have hternary : DiagonalRepresents D.bong.value reference.value := by
    change DiagonalRepresents D.bong.toBONG.value reference.toBONG.value
    exact D.bong.toBONG.diagonalRepresents_values reference.toBONG
  have happended := diagonalRepresents_append hternary common
  have hsource :
      diagonalUnitCoefficients (beli2019Lemma910Values D a) =
        Fin.append D.bong.value common := by
    funext i
    refine Fin.addCases (m := 3) (n := N) (fun j => ?_) (fun j => ?_) i
    · simp [beli2019Lemma910Values, diagonalUnitCoefficients]
    · simp [beli2019Lemma910Values, diagonalUnitCoefficients,
        common, commonUnits]
  have htarget :
      Fin.append reference.value common = a.value := by
    funext i
    refine Fin.addCases (m := 3) (n := N) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      have h := congrArg Units.val (hprefix j)
      simpa only [GoodBONG.coe_valueUnit] using h
    · simp [common, commonUnits]
  change DiagonalRepresents
    (diagonalUnitCoefficients (beli2019Lemma910Values D a)) a.value
  rw [hsource, ← htarget]
  exact happended

/-- Full coefficient realization for Lemma 9.10.  The hypotheses are the
two exact numerical conditions of Beli (2006), Definition 2.2; subsequent
lemmas discharge them from the paper's displayed inequalities. -/
theorem exists_beli2019Lemma910FullCoefficientRealization
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + N))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd N i))
    (hweak : ∀ (i : Fin (3 + N)) (hi : i.1 + 2 < 3 + N),
      ordUnit K (beli2019Lemma910Values D a i) ≤
        ordUnit K
          (beli2019Lemma910Values D a ⟨i.1 + 2, hi⟩))
    (hadjacent : ∀ (i : Fin (3 + N)) (hi : i.1 + 1 < 3 + N),
      IsBinaryParameterAdmissible
        (beli2019Lemma910Values D a ⟨i.1 + 1, hi⟩ /
          beli2019Lemma910Values D a i)) :
    Nonempty (BONG.PrescribedValuesGoodBONGData q (3 + N)
      (beli2019Lemma910Values D a)) := by
  apply BONG.exists_prescribedValuesGoodBONGData a
    (beli2019Lemma910Values D a)
  · exact beli2019Lemma910Values_diagonalRepresents reference a D hprefix
  · exact hweak
  · exact hadjacent

end BONG.GoodBONG

end Bong
