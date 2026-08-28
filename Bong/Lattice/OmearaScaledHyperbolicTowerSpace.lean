/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ScaledHyperbolicChangeScale
import Bong.Lattice.OmearaDisplayedTower
import Bong.Lattice.Omeara9328TailConditions
import Bong.Lattice.OrthogonalSumRescale

/-!
# Field isometries for scaled hyperbolic towers

The integral change-of-scale map for a hyperbolic plane requires equal
valuation of the two scale generators.  Over the field alone no such
restriction is needed.  This file records the unrestricted field isometry,
iterates it over the coordinate tower, and gives the associativity isometry
which concatenates two finite towers.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The recursively parenthesized tower of `n` scaled zero-coefficient
O'Meara planes. -/
noncomputable def scaledZeroOmearaTowerForm (s : Kˣ) :
    (n : Nat) →
      QuadraticSpace K
        (Lattice.HyperbolicExtension K (Fin 0 → K) n)
  | 0 => Lattice.zeroCoordinateQuadraticSpace (K := K)
  | n + 1 =>
      ((omearaPlane (K := K) 0).rescaleUnit s).orthogonalSum
        (scaledZeroOmearaTowerForm s n)

/-- Any two scaled hyperbolic planes are isometric over the field. -/
noncomputable def scaledHyperbolicChangeScaleSpaceIsometry
    (s t : Kˣ) :
    Isometry (hyperbolicPlane s) (hyperbolicPlane t) := by
  let c : Kˣ := s / t
  refine
    { toLinearEquiv := Lattice.hyperbolicLeftScaleLinearEquiv c
      map_bilin := ?_ }
  intro x y
  rw [hyperbolicPlane_bilin_apply, hyperbolicPlane_bilin_apply]
  change (t : K) *
      (((c : K) * x 0) * y 1 + x 1 * ((c : K) * y 0)) = _
  have htc : (t : K) * (c : K) = (s : K) := by
    exact congrArg Units.val (by
      simp [c, div_eq_mul_inv] : t * c = s)
  rw [show (t : K) *
      (((c : K) * x 0) * y 1 + x 1 * ((c : K) * y 0)) =
      ((t : K) * (c : K)) * (x 0 * y 1 + x 1 * y 0) by ring,
    htc]

/-- Change the scale of a zero-coefficient O'Meara plane over the field. -/
noncomputable def scaledZeroOmearaPlaneChangeScaleSpaceIsometry
    (s t : Kˣ) :
    Isometry
      ((omearaPlane (K := K) 0).rescaleUnit s)
      ((omearaPlane (K := K) 0).rescaleUnit t) :=
  (Lattice.scaledZeroOmearaPlaneLatticeIsometry s).toQuadraticSpaceIsometry
    |>.trans (scaledHyperbolicChangeScaleSpaceIsometry s t)
    |>.trans
      ((Lattice.scaledZeroOmearaPlaneLatticeIsometry t).symm
        |>.toQuadraticSpaceIsometry)

/-- Change the common scale on every plane in a finite zero-coefficient
O'Meara tower. -/
noncomputable def scaledZeroOmearaTowerChangeScaleSpaceIsometry
    (s t : Kˣ) :
    (n : Nat) →
      Isometry
        (scaledZeroOmearaTowerForm s n)
        (scaledZeroOmearaTowerForm t n)
  | 0 => Isometry.refl (Lattice.zeroCoordinateQuadraticSpace (K := K))
  | n + 1 =>
      (scaledZeroOmearaPlaneChangeScaleSpaceIsometry s t).orthogonalSum
      (scaledZeroOmearaTowerChangeScaleSpaceIsometry s t n)

/-- A common rescaling of a scaled zero-coefficient tower multiplies its
displayed scale.  This is the recursive distributivity identity used when a
Jordan component is normalized to scale one. -/
noncomputable def scaledZeroOmearaTowerRescaleSpaceIsometry
    (s c : Kˣ) :
    (n : Nat) →
      Isometry
        ((scaledZeroOmearaTowerForm s n).rescaleUnit c)
        (scaledZeroOmearaTowerForm (c * s) n)
  | 0 =>
      { toLinearEquiv := LinearEquiv.refl K (Fin 0 → K)
        map_bilin := by
          intro x y
          have hx : x = 0 := by
            change (x : Fin 0 → K) = 0
            funext i
            exact Fin.elim0 i
          have hy : y = 0 := by
            change (y : Fin 0 → K) = 0
            funext i
            exact Fin.elim0 i
          subst x
          subst y
          simp [scaledZeroOmearaTowerForm,
            Lattice.zeroCoordinateQuadraticSpace] }
  | n + 1 =>
      (rescaleUnitOrthogonalSumIsometry
        ((omearaPlane (K := K) 0).rescaleUnit s)
        (scaledZeroOmearaTowerForm s n) c).trans
        ((rescaleUnitMulIsometry (omearaPlane (K := K) 0) s c).orthogonalSum
          (scaledZeroOmearaTowerRescaleSpaceIsometry s c n))

/-- Identify the ordinary hyperbolic extension with the scaled
zero-coefficient O'Meara tower. -/
noncomputable def hyperbolicExtensionToScaledZeroOmearaTowerSpaceIsometry
    (s : Kˣ) :
    (n : Nat) →
      Isometry
        (Lattice.hyperbolicExtensionForm
          (Lattice.zeroCoordinateQuadraticSpace (K := K)) n)
        (scaledZeroOmearaTowerForm s n)
  | 0 => Isometry.refl (Lattice.zeroCoordinateQuadraticSpace (K := K))
  | n + 1 =>
      ((scaledHyperbolicChangeScaleSpaceIsometry (1 : Kˣ) s).trans
        ((Lattice.scaledZeroOmearaPlaneLatticeIsometry s).symm
          |>.toQuadraticSpaceIsometry)).orthogonalSum
        (hyperbolicExtensionToScaledZeroOmearaTowerSpaceIsometry s n)

/-- The zero-dimensional coordinate lattice used only to forget the empty
left factor in the base case of tower concatenation. -/
noncomputable def zeroCoordinateBasisLattice :
    Bong.Lattice K (Fin 0 → K) :=
  Lattice.basisLattice (Pi.basisFun K (Fin 0))

/-- Concatenate two equally scaled zero-coefficient O'Meara towers. -/
noncomputable def scaledZeroOmearaTowerAppendSpaceIsometry (s : Kˣ) :
    (m n : Nat) →
      Isometry
        ((scaledZeroOmearaTowerForm s m).orthogonalSum
          (scaledZeroOmearaTowerForm s n))
        (scaledZeroOmearaTowerForm s (n + m))
  | 0, n => by
      rw [Nat.add_zero]
      change Isometry
        ((Lattice.zeroCoordinateQuadraticSpace (K := K)).orthogonalSum
          (scaledZeroOmearaTowerForm s n))
        (scaledZeroOmearaTowerForm s n)
      exact
        (Lattice.zeroLeftOrthogonalProductIsometry
          (K := K) zeroCoordinateBasisLattice
          (scaledZeroOmearaTowerForm s n)
          (Lattice.hyperbolicExtensionLattice
            zeroCoordinateBasisLattice n)).toQuadraticSpaceIsometry
  | Nat.succ m, n => by
      rw [Nat.add_succ]
      let head := (omearaPlane (K := K) 0).rescaleUnit s
      let leftTail := scaledZeroOmearaTowerForm s m
      let right := scaledZeroOmearaTowerForm s n
      let reassociate := orthogonalSumAssoc head leftTail right
      let recursive := scaledZeroOmearaTowerAppendSpaceIsometry s m n
      change Isometry ((head.orthogonalSum leftTail).orthogonalSum right)
        (head.orthogonalSum (scaledZeroOmearaTowerForm s (n + m)))
      exact reassociate.trans
        ((Isometry.refl head).orthogonalSum recursive)

/-- Finite generation of the recursively nested coordinate tower. -/
@[reducible] noncomputable def hyperbolicExtensionZeroModuleFinite :
    (n : Nat) →
      Module.Finite K
        (Lattice.HyperbolicExtension K (Fin 0 → K) n)
  | 0 => Module.Finite.pi
  | n + 1 => by
      letI := hyperbolicExtensionZeroModuleFinite n
      exact Module.Finite.prod

/-- The coordinate tower on `n` planes has dimension `2n`. -/
theorem finrank_hyperbolicExtension_zero (n : Nat) :
    finrank K (Lattice.HyperbolicExtension K (Fin 0 → K) n) = 2 * n := by
  induction n with
  | zero =>
      change finrank K (Fin 0 → K) = 0
      exact Module.finrank_fin_fun K
  | succ n ih =>
      letI := hyperbolicExtensionZeroModuleFinite (K := K) n
      change finrank K
          ((Fin 2 → K) ×
            Lattice.HyperbolicExtension K (Fin 0 → K) n) =
        2 * (n + 1)
      rw [Module.finrank_prod, Module.finrank_fin_fun, ih]
      omega

end QuadraticSpace

end Bong
