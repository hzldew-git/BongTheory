/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basis
import Bong.Lattice.ProjectionPreimage

/-!
# Constructing BONGs by replacing projected tails

This file formalizes the one-step inverse-image construction in Beli (2003),
Lemma 2.7(ii).  A BONG of a full sublattice of the projected tail can be
prepended by the original norm generator.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V} {n : Nat}
  {anisotropic : q.IsAnisotropic x}

/-- Prepend a norm generator after replacing its projected tail by a sublattice. -/
noncomputable def prependProjectionPreimage
    (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x anisotropic)
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic) N n) :
    BONG V q
      (Lattice.projectionPreimage q L x anisotropic generator.mem N hN)
      (n + 1) := by
  have generatorPreimage := Lattice.isNormGenerator_projectionPreimage
    q L x generator anisotropic N hN
  have hprojection := Lattice.projectedLattice_projectionPreimage
    q L x anisotropic generator.mem N hN
  let tail' : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
      ((Lattice.projectionPreimage q L x anisotropic generator.mem N hN)
        |>.projectedLattice q x anisotropic) n :=
    tail.castLattice hprojection.symm
  exact BONG.cons x generatorPreimage anisotropic tail'

@[simp]
theorem ambientVector_prependProjectionPreimage_zero
    (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x anisotropic)
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic) N n) :
    (prependProjectionPreimage generator N hN tail).ambientVector 0 = x := by
  simp [prependProjectionPreimage]

@[simp]
theorem ambientVector_prependProjectionPreimage_succ
    (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x anisotropic)
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic) N n)
    (i : Fin n) :
    (prependProjectionPreimage generator N hN tail).ambientVector i.succ =
      (tail.ambientVector i : V) := by
  simp [prependProjectionPreimage]

end BONG

end Bong
