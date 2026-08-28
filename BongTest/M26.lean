/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M26 exact BONG-prefix restriction smoke tests
-/

namespace BongTest.M26

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) (length : Nat) (bound : length ≤ n)
    (y : (b.prefixWitness length bound).carrier) :
    y ∈ (b.prefixWitness length bound).lattice ↔ (y : V) ∈ L :=
  b.mem_prefixWitness_lattice_iff length bound y

example (b : BONG V q L n) (length : Nat) (bound : length ≤ n) :
    (b.prefixWitness length bound).lattice =
      Lattice.comapSubtype L (b.prefixWitness length bound).carrier
        (b.prefixWitness length bound).parentIntersection_spans :=
  b.prefixWitness_lattice_eq_comapSubtype length bound

#print axioms Bong.BONG.mem_prefixWitness_lattice_iff
#print axioms Bong.BONG.prefixWitness_lattice_eq_comapSubtype

end

end BongTest.M26
