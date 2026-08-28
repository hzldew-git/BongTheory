/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019WeightSequence

/-!
# M122 Beli 2019, the W-sequence smoke tests
-/

namespace BongTest.M122

open Bong

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    b.weightSequence.value ⟨2 * i.1, by omega⟩ =
      (b.order i.castSucc : ℚ) + b.alphaValue i :=
  b.weightSequence_even i

example (b : BONG.GoodBONG q L (n + 1)) (i : Fin n) :
    b.weightSequence.value ⟨2 * i.1 + 1, by omega⟩ =
      (b.order i.succ : ℚ) - b.alphaValue i :=
  b.weightSequence_odd i

#print axioms Bong.BeliOrderSequence.interleave_value_even
#print axioms Bong.BeliOrderSequence.reverseNegate_interleave_value_odd
#print axioms Bong.BONG.GoodBONG.weightSequence_even
#print axioms Bong.BONG.GoodBONG.weightSequence_odd
#print axioms Bong.BONG.GoodBONG.exists_reverseDual_weightSequence

end BongTest.M122
