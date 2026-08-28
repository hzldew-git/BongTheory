/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M23 recursive BONG-suffix smoke tests
-/

namespace BongTest.M23

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L n) (start : Nat) (bound : start ≤ n) :
    Nonempty
      (BONG.SegmentWitness b start (n - start) (by omega)) :=
  b.exists_suffixWitness start bound

example (b : BONG V q L n) (start : Nat) (bound : start ≤ n)
    (i : Fin (n - start)) :
    (b.suffixWitness start bound).bong.value i =
      b.value ((b.suffixWitness start bound).sourceIndex i) :=
  (b.suffixWitness start bound).value_eq i

#print axioms Bong.BONG.suffixWitness
#print axioms Bong.BONG.exists_suffixWitness

end

end BongTest.M23
