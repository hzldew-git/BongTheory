/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.OrthogonalSumDiagonal
import Bong.Bong.DiagonalTailCancellation

/-!
# Witt cancellation for finite orthogonal sums

This file proves cancellation of a common nondegenerate orthogonal summand.
The proof diagonalizes all three spaces, cancels the common finite diagonal
prefix one anisotropic line at a time, and transports the result back.  No
local classification law is used.
-/

namespace Bong

open Dyadic
open BONG.GoodBONG

namespace QuadraticSpace

universe u v w z z'

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type z} [AddCommGroup U] [Module K U]
  {U' : Type z'} [AddCommGroup U'] [Module K U']
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K U] [FiniteDimensional K U']
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- Cancel a literally common finite nondegenerate orthogonal summand from
an isometric representation.  Unlike Witt cancellation, the two tails may
have different dimensions. -/
theorem orthogonalSumLeftCancelRepresents
    (p : QuadraticSpace K U) (q : QuadraticSpace K V)
    (r : QuadraticSpace K W)
    (h : (p.orthogonalSum r).Represents (p.orthogonalSum q)) :
    r.Represents q := by
  rcases h with ⟨f⟩
  let sourceDiagonal := p.orthogonalSumDiagonalizationIsometry q
  let targetDiagonal := p.orthogonalSumDiagonalizationIsometry r
  let diagonalRepresentation : Representation
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.append p.diagonalUnits q.diagonalUnits))
        (fun i => Units.ne_zero
          (Fin.append p.diagonalUnits q.diagonalUnits i)))
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.append p.diagonalUnits r.diagonalUnits))
        (fun i => Units.ne_zero
          (Fin.append p.diagonalUnits r.diagonalUnits i))) :=
    targetDiagonal.toRepresentation.trans <|
      f.trans sourceDiagonal.symm.toRepresentation
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append p.diagonalUnits q.diagonalUnits))
      (diagonalUnitCoefficients (Fin.append p.diagonalUnits r.diagonalUnits)) := by
    apply (finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.append p.diagonalUnits q.diagonalUnits)
      (Fin.append p.diagonalUnits r.diagonalUnits)).mp
    exact ⟨diagonalRepresentation⟩
  have hsource :
      diagonalUnitCoefficients (Fin.append p.diagonalUnits q.diagonalUnits) =
        Fin.append (diagonalUnitCoefficients p.diagonalUnits)
          (diagonalUnitCoefficients q.diagonalUnits) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [diagonalUnitCoefficients]
  have htarget :
      diagonalUnitCoefficients (Fin.append p.diagonalUnits r.diagonalUnits) =
        Fin.append (diagonalUnitCoefficients p.diagonalUnits)
          (diagonalUnitCoefficients r.diagonalUnits) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [diagonalUnitCoefficients]
  rw [hsource, htarget] at hfull
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients r.diagonalUnits) :=
    DiagonalRepresents.cancel_common_prefix
      (diagonalUnitCoefficients p.diagonalUnits)
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients r.diagonalUnits)
      (fun i => Units.ne_zero (p.diagonalUnits i))
      (fun i => Units.ne_zero (q.diagonalUnits i))
      (fun i => Units.ne_zero (r.diagonalUnits i)) hfull
  exact (represents_iff_diagonalRepresents q r).mpr htail

/-- Cancel isometric finite head summands from a representation. -/
theorem orthogonalSumCancelRepresents
    (p : QuadraticSpace K U) (p' : QuadraticSpace K U')
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (head : Isometry p p')
    (total : (p'.orthogonalSum r).Represents (p.orthogonalSum q)) :
    r.Represents q := by
  rcases total with ⟨f⟩
  apply orthogonalSumLeftCancelRepresents p q r
  exact ⟨(head.symm.orthogonalSum (Isometry.refl r)).toRepresentation.trans f⟩

/-- Cancel a literally common finite nondegenerate orthogonal summand. -/
noncomputable def orthogonalSumLeftCancel
    (p : QuadraticSpace K U) (q : QuadraticSpace K V)
    (r : QuadraticSpace K W)
    (f : Isometry (p.orthogonalSum q) (p.orthogonalSum r)) :
    Isometry q r := by
  have hsum := f.toLinearEquiv.finrank_eq
  have hfinrank : Module.finrank K V = Module.finrank K W := by
    rw [Module.finrank_prod, Module.finrank_prod] at hsum
    exact Nat.add_left_cancel hsum
  let sourceDiagonal := p.orthogonalSumDiagonalizationIsometry q
  let targetDiagonal := p.orthogonalSumDiagonalizationIsometry r
  let diagonalIsometry := sourceDiagonal.symm.trans (f.trans targetDiagonal)
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append p.diagonalUnits q.diagonalUnits))
      (diagonalUnitCoefficients (Fin.append p.diagonalUnits r.diagonalUnits)) := by
    apply (finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.append p.diagonalUnits q.diagonalUnits)
      (Fin.append p.diagonalUnits r.diagonalUnits)).mp
    exact ⟨diagonalIsometry.toRepresentation⟩
  have hsource :
      diagonalUnitCoefficients (Fin.append p.diagonalUnits q.diagonalUnits) =
        Fin.append (diagonalUnitCoefficients p.diagonalUnits)
          (diagonalUnitCoefficients q.diagonalUnits) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [diagonalUnitCoefficients]
  have htarget :
      diagonalUnitCoefficients (Fin.append p.diagonalUnits r.diagonalUnits) =
        Fin.append (diagonalUnitCoefficients p.diagonalUnits)
          (diagonalUnitCoefficients r.diagonalUnits) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [diagonalUnitCoefficients]
  rw [hsource, htarget] at hfull
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients r.diagonalUnits) := by
    exact DiagonalRepresents.cancel_common_prefix
      (diagonalUnitCoefficients p.diagonalUnits)
      (diagonalUnitCoefficients q.diagonalUnits)
      (diagonalUnitCoefficients r.diagonalUnits)
      (fun i => Units.ne_zero (p.diagonalUnits i))
      (fun i => Units.ne_zero (q.diagonalUnits i))
      (fun i => Units.ne_zero (r.diagonalUnits i)) hfull
  have hrep : r.Represents q :=
    (represents_iff_diagonalRepresents q r).mpr htail
  exact (Classical.choice hrep).toIsometryOfFinrankEq hfinrank

/-- Cancel isometric, rather than definitionally identical, finite
nondegenerate orthogonal summands. -/
noncomputable def orthogonalSumCancel
    (p : QuadraticSpace K U) (p' : QuadraticSpace K U')
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (head : Isometry p p')
    (total : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)) :
    Isometry q r :=
  orthogonalSumLeftCancel p q r <|
    total.trans (head.symm.orthogonalSum (Isometry.refl r))

end QuadraticSpace

end Bong
