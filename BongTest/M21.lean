/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M21 norm-generator and BONG-existence smoke tests
-/

namespace BongTest.M21

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  (q : QuadraticSpace K V) (L : Lattice K V)

example :
    Lattice.normIdeal q L =
      Submodule.span (IntegerRing K)
        (Lattice.normValueCandidates q L : Set K) :=
  Lattice.normIdeal_eq_span_normValueCandidates q L

example (hfin : 0 < Module.finrank K V) :
    ∃ x : V, Lattice.IsNormGenerator q L x ∧ q.IsAnisotropic x :=
  Lattice.exists_isNormGenerator_of_finrank_pos q L hfin

-- Deliberately no `BONGStructuralLaws` assumption.
example : Nonempty (BONG V q L (Module.finrank K V)) :=
  exists_bong q L

#print axioms Bong.Lattice.normIdeal_eq_span_normValueCandidates
#print axioms Bong.Lattice.exists_isNormGenerator_of_finrank_pos
#print axioms Bong.BONG.ofLattice
#print axioms Bong.exists_bong

end

end BongTest.M21
