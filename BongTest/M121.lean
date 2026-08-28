/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SequenceDual

/-!
# M121 Beli 2019, reversal and duality smoke tests
-/

namespace BongTest.M121

open Bong

variable {n : Nat}

example (x : BeliOrderSequence n) :
    x.reverseNegate.reverseNegate = x :=
  x.reverseNegate_reverseNegate

example (x : BeliOrderSequence n) (kappa : Int) :
    x.reverseNegate.IsKappaBounded kappa ↔ x.IsKappaBounded kappa :=
  x.reverseNegate_isKappaBounded_iff kappa

example (x y : BeliOrderSequence n) :
    BeliOrderLE x.reverseNegate y.reverseNegate ↔ BeliOrderLE y x :=
  BeliOrderLE.reverseNegate_le_reverseNegate_iff x y

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG.GoodBONG q L n) :
    b.orderSequence.IsKappaBounded
      (2 * (Dyadic.ramificationIndex K : Int)) :=
  b.orderSequence_isKappaBounded_two_mul_e

#print axioms Bong.BeliOrderSequence.reverseNegate_reverseNegate
#print axioms Bong.BeliOrderSequence.reverseNegate_isKappaBounded_iff
#print axioms Bong.BeliOrderLE.reverseNegate_le_reverseNegate_iff
#print axioms Bong.BONG.GoodBONG.orderSequence_isKappaBounded_two_mul_e
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_orderSequence

end BongTest.M121
