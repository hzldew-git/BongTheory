/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.SectionTwo

/-!
# M11 smoke tests

Beli's mixed-pairing estimate, Lemma 2.2, and Corollary 2.6 are available
without additional local-law assumptions.
-/

namespace BongTest.M11

open Bong
open Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

example : BONGMixedPairingLaws.{u, v} K := inferInstance

example : BONGReconstructionLaws.{u, v} K := inferInstance

example (q : QuadraticSpace K V) (M N : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    (norm_le : Lattice.normIdeal q N ≤ Lattice.normIdeal q M)
    (projection_le :
      Lattice.projectedLattice q N x anisotropic ≤
        Lattice.projectedLattice q M x anisotropic) : N ≤ M :=
  Lattice.le_of_normIdeal_le_of_projectedLattice_le
    q M N x generator anisotropic norm_le projection_le

example {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (b : BONG V q L n) (c : BONG V q M n)
    (vectors : ∀ i, b.ambientVector i = c.ambientVector i) : L = M :=
  b.lattice_eq_of_ambientVector_eq_from_projection c vectors

#print axioms Bong.Lattice.two_bilin_mem_normIdeal_of_normGenerator
#print axioms Bong.Lattice.le_of_normIdeal_le_of_projectedLattice_le
#print axioms Bong.BONG.lattice_eq_of_ambientVector_eq_from_projection

end BongTest.M11
