/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517CollisionProfiles
import Bong.Bong.Beli2019Lemma37Models

/-!
# Lemma 3.7(i) models from Section 5 boundary resolutions

A `StrictBoundaryResolution` remembers the strict weak-Jordan refinement
behind a terminal coordinate and identifies its prefix carrier with the
original almost-Jordan prefix.  This file converts that certificate into
the actual ambient approximation model required by conditions (iii) and
(iv).
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG.SpaceApproximationModel

/-- Transport an approximation model along equality of its BONG index. -/
noncomputable def castIndex
    {n : Nat} {a : BONG.GoodBONG q L (n + 1)} {i j : Fin n}
    (M : SpaceApproximationModel a i) (h : i = j) :
    SpaceApproximationModel a j := by
  subst j
  exact M

@[simp] theorem castIndex_carrier
    {n : Nat} {a : BONG.GoodBONG q L (n + 1)} {i j : Fin n}
    (M : SpaceApproximationModel a i) (h : i = j) :
    (M.castIndex h).carrier = M.carrier := by
  subst j
  rfl

/-- A diagonal representation into a concrete approximation model is
preserved when the model is transported along equality of its BONG index. -/
theorem castIndex_diagonalRepresentedBy
    {n m : Nat} {a : BONG.GoodBONG q L (n + 1)} {i j : Fin n}
    (M : SpaceApproximationModel a i) (h : i = j)
    {source : Fin m → K}
    (hrep : DiagonalRepresents source
      (diagonalUnitCoefficients M.units)) :
    DiagonalRepresents source
      (diagonalUnitCoefficients (M.castIndex h).units) := by
  subst j
  exact hrep

/-- A diagonal representation out of a concrete approximation model is
also preserved by transport of its BONG index. -/
theorem castIndex_diagonalRepresents
    {n m : Nat} {a : BONG.GoodBONG q L (n + 1)} {i j : Fin n}
    (M : SpaceApproximationModel a i) (h : i = j)
    {target : Fin m → K}
    (hrep : DiagonalRepresents (diagonalUnitCoefficients M.units) target) :
    DiagonalRepresents
      (diagonalUnitCoefficients (M.castIndex h).units) target := by
  subst j
  exact hrep

end BONG.GoodBONG.SpaceApproximationModel

namespace BONG.StrictBoundaryResolution

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {W : Lattice.WeakJordanDecomposition q L t}
  {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {g : Fin (n + 1)}

/-- View the stored profile on the strict weak-Jordan refinement which
produced the resolved Jordan decomposition. -/
noncomputable def strictProfile
    (R : StrictBoundaryResolution a W x g) :
    BONG.JordanOrderProfileWitness a.toBONG
      (R.strictWeak.toJordan R.scaleOrder_strict) := by
  rw [← R.jordan_eq]
  exact R.profile

theorem strictProfile_boundaryIndex_eq
    (R : StrictBoundaryResolution a W x g) :
    R.strictProfile.boundaryIndex R.boundary = g := by
  rcases R with ⟨boundaryCount, strictWeak, hstrict, hparity,
    jordan, hjordan, profile, boundary, weakNext, hweakNext,
    hboundary, hcarrier, hleft, hright⟩
  cases hjordan
  exact hboundary

/-- Lemma 3.7(i), realized on the strict prefix selected by a boundary
resolution and then reindexed to the original BONG coordinate. -/
noncomputable def lemma37Model_i
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (R : StrictBoundaryResolution a W x g) :
    BONG.GoodBONG.SpaceApproximationModel a g :=
  (BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
      a R.strictWeak R.hasImproperEvenRank
      R.scaleOrder_strict R.strictProfile R.boundary).castIndex
        R.strictProfile_boundaryIndex_eq

/-- The carrier of the resolved Lemma 3.7(i) model is exactly the original
almost-Jordan prefix recorded by the resolution. -/
theorem lemma37Model_i_carrier_eq
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (R : StrictBoundaryResolution a W x g) :
    R.lemma37Model_i.carrier =
      W.toOrthogonalDecomposition.prefixCarrier R.weakNext.val := by
  unfold lemma37Model_i
  rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
  change R.strictWeak.toOrthogonalDecomposition.prefixCarrier
      (R.boundary.val + 1) =
    W.toOrthogonalDecomposition.prefixCarrier R.weakNext.val
  calc
    R.strictWeak.toOrthogonalDecomposition.prefixCarrier
        (R.boundary.val + 1) =
        R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.boundary.val + 1) := by
      rw [R.jordan_eq]
      rfl
    _ = W.toOrthogonalDecomposition.prefixCarrier R.weakNext.val :=
      R.prefixCarrier_eq

end BONG.StrictBoundaryResolution

end Bong
