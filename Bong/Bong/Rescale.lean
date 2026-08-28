/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.GoodMap
import Bong.Lattice.NormRescale
import Bong.Lattice.ProjectionScaling

/-!
# Rescaling a BONG together with its lattice

Globally multiplying a lattice by a nonzero scalar multiplies every vector
of a BONG by the same scalar.  The recursive step uses the canonical
identity-on-vectors isometry between the two orthogonal-complement subtype
models and the fact that projection commutes with lattice rescaling.

This is the basis-free construction used for the binary block
`J' = \mathfrak p J` in Beli (2019), Lemma 7.14.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private noncomputable def rescaleNil (a : Kˣ)
    {V' : Type v} [AddCommGroup V'] [Module K V']
    (q' : QuadraticSpace K V') (L' : Lattice K V')
    (exhausted : Subsingleton V') :
    BONG V' q' (Lattice.rescale a L') 0 :=
  BONG.nil q' (Lattice.rescale a L') exhausted

private noncomputable def rescaleCons (a : Kˣ)
    {V' : Type v} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'} {m : Nat}
    (x : V') (generator : Lattice.IsNormGenerator q' L' x)
    (anisotropic : q'.IsAnisotropic x)
    (_tail : BONG (q'.vectorOrthogonal x)
      (q'.orthogonalSpace x anisotropic)
      (L'.projectedLattice q' x anisotropic) m)
    (rescaledTail : BONG (q'.vectorOrthogonal x)
      (q'.orthogonalSpace x anisotropic)
      (Lattice.rescale a (L'.projectedLattice q' x anisotropic)) m) :
    BONG V' q' (Lattice.rescale a L') (m + 1) := by
  let scaledAnisotropic :=
    q'.isAnisotropic_smul anisotropic a.ne_zero
  let tailIsometry :=
    (q'.orthogonalSpaceSMulIsometry anisotropic a.ne_zero).symm
  let mappedTail := rescaledTail.map tailIsometry
  let transportedTail := mappedTail.castLattice
    (Lattice.map_rescale_projectedLattice_smul_symm
      q' L' anisotropic a)
  exact BONG.cons ((a : K) • x) (generator.rescale a)
    scaledAnisotropic transportedTail

/-- Multiply the lattice and every recursively selected BONG vector by the
same nonzero field scalar. -/
noncomputable def rescale (a : Kˣ) (b : BONG V q L n) :
    BONG V q (Lattice.rescale a L) n :=
  BONG.rec
    (motive := fun V _ _ q L n _ =>
      BONG V q (Lattice.rescale a L) n)
    (rescaleNil a) (rescaleCons a)
    b

/-- The ambient orthogonal basis vectors are literally multiplied by the
rescaling scalar. -/
@[simp]
theorem ambientVector_rescale (a : Kˣ) (b : BONG V q L n)
    (i : Fin n) :
    (b.rescale a).ambientVector i = (a : K) • b.ambientVector i := by
  induction b with
  | nil => exact Fin.elim0 i
  | cons x generator anisotropic tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [rescale, rescaleCons]
      · have h := congrArg Subtype.val (ih j)
        simpa [rescale, rescaleCons,
          QuadraticSpace.orthogonalSpaceSMulIsometry,
          QuadraticSpace.Isometry.symm] using h

/-- Every quadratic value is multiplied by the square of the rescaling
scalar. -/
@[simp]
theorem value_rescale (a : Kˣ) (b : BONG V q L n) (i : Fin n) :
    (b.rescale a).value i = (a : K) ^ 2 * b.value i := by
  induction b with
  | nil => exact Fin.elim0 i
  | cons x generator anisotropic tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [rescale, rescaleCons, QuadraticSpace.quadratic_smul]
      · simpa [rescale, rescaleCons] using ih j

/-- The unit-valued coefficient sequence is multiplied by `a²`. -/
@[simp]
theorem valueUnit_rescale (a : Kˣ) (b : BONG V q L n) (i : Fin n) :
    (b.rescale a).valueUnit i = a ^ 2 * b.valueUnit i := by
  apply Units.ext
  simp [value_rescale]

/-- Rescaling translates every BONG order by the same even amount. -/
@[simp]
theorem order_rescale (a : Kˣ) (b : BONG V q L n) (i : Fin n) :
    (b.rescale a).order i = b.order i + 2 * ordUnit K a := by
  rw [order_eq_ordUnit, valueUnit_rescale, ordUnit_mul, ordUnit_pow,
    order_eq_ordUnit]
  omega

/-- The two-step inequalities defining a good BONG are invariant under
global lattice rescaling. -/
theorem IsGood.rescale (a : Kˣ) {b : BONG V q L n}
    (hgood : b.IsGood) : (b.rescale a).IsGood := by
  intro i hi
  rw [order_rescale, order_rescale]
  have h := hgood i hi
  omega

namespace GoodBONG

/-- Rescale a good BONG together with its lattice. -/
noncomputable def rescale (a : Kˣ) (b : GoodBONG q L n) :
    GoodBONG q (Lattice.rescale a L) n where
  toBONG := b.toBONG.rescale a
  good := b.good.rescale a

@[simp]
theorem ambientVector_rescale (a : Kˣ) (b : GoodBONG q L n)
    (i : Fin n) :
    (b.rescale a).toBONG.ambientVector i =
      (a : K) • b.toBONG.ambientVector i :=
  BONG.ambientVector_rescale a b.toBONG i

@[simp]
theorem value_rescale (a : Kˣ) (b : GoodBONG q L n) (i : Fin n) :
    (b.rescale a).value i = (a : K) ^ 2 * b.value i :=
  BONG.value_rescale a b.toBONG i

@[simp]
theorem valueUnit_rescale (a : Kˣ) (b : GoodBONG q L n) (i : Fin n) :
    (b.rescale a).valueUnit i = a ^ 2 * b.valueUnit i :=
  BONG.valueUnit_rescale a b.toBONG i

@[simp]
theorem order_rescale (a : Kˣ) (b : GoodBONG q L n) (i : Fin n) :
    (b.rescale a).order i = b.order i + 2 * ordUnit K a :=
  BONG.order_rescale a b.toBONG i

end GoodBONG

end BONG

end Bong
