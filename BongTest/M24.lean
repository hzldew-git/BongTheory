/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M24 coordinate-segment and lattice-restriction smoke tests
-/

namespace BongTest.M24

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) :
    (q.bilin.restrict
      (b.segmentCarrier start length bound)).Nondegenerate :=
  b.segmentCarrier_nondegenerate start length bound

example (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) :
    Module.finrank K (b.segmentCarrier start length bound) = length :=
  b.finrank_segmentCarrier start length bound

variable (P : Submodule K V)
  (hspan : Submodule.span K
    ({x : P | (x : V) ∈ L} : Set P) = ⊤)

example (x : P) :
    x ∈ Lattice.comapSubtype L P hspan ↔ (x : V) ∈ L :=
  Lattice.mem_comapSubtype_iff L P hspan x

#print axioms Bong.BONG.segmentCarrier_nondegenerate
#print axioms Bong.BONG.finrank_segmentCarrier
#print axioms Bong.Lattice.comapSubtype
#print axioms Bong.Lattice.isNormGenerator_comapSubtype

end

end BongTest.M24
