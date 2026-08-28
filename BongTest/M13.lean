/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M13 projection-preimage smoke tests

These examples exercise the one-step replacement construction from Beli
(2003), Lemma 2.7(ii).
-/

namespace BongTest.M13

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V} {n : Nat}
  {hx : q.IsAnisotropic x}

example (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x hx) :
    Lattice.IsNormGenerator q
      (Lattice.projectionPreimage q L x hx generator.mem N hN) x :=
  Lattice.isNormGenerator_projectionPreimage q L x generator hx N hN

example (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x hx) :
    Lattice.projectedLattice q
      (Lattice.projectionPreimage q L x hx generator.mem N hN) x hx = N :=
  Lattice.projectedLattice_projectionPreimage q L x hx generator.mem N hN

example (generator : Lattice.IsNormGenerator q L x)
    (N : Lattice K (q.vectorOrthogonal x))
    (hN : N ≤ L.projectedLattice q x hx)
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x hx) N n) :
    BONG V q (Lattice.projectionPreimage q L x hx generator.mem N hN) (n + 1) :=
  tail.prependProjectionPreimage generator N hN

#print axioms Bong.Lattice.projectionPreimage
#print axioms Bong.Lattice.projectedLattice_projectionPreimage
#print axioms Bong.Lattice.isNormGenerator_projectionPreimage
#print axioms Bong.BONG.prependProjectionPreimage

end

end BongTest.M13
