/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M25 unconditional consecutive-segment smoke tests
-/

namespace BongTest.M25

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

-- Deliberately no `BONGStructuralLaws` assumption in this file.
example (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) :
    Nonempty (BONG.SegmentWitness b start length bound) :=
  b.exists_segmentWitness start length bound

example (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) :
    (b.segmentWitness start length bound).carrier =
      b.segmentCarrier start length bound :=
  (b.segmentWitness start length bound).carrier_eq_segmentCarrier

example (b : BONG V q L n) (start length : Nat)
    (bound : start + length ≤ n) (i : Fin length) :
    (b.segmentWitness start length bound).bong.value i =
      b.value ((b.segmentWitness start length bound).sourceIndex i) :=
  (b.segmentWitness start length bound).value_eq i

#print axioms Bong.BONG.prefixWitness
#print axioms Bong.BONG.segmentWitness
#print axioms Bong.BONG.exists_segmentWitness

end

end BongTest.M25
