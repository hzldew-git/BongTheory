/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryValueSet

/-!
# M59 power ideals and Corollary 3.10(a) smoke tests
-/

namespace BongTest.M59

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (r : Int) (a : K) :
    a ∈ Lattice.powerIdeal (K := K) r ↔
      (r : WithTop Int) ≤ ord K a :=
  Lattice.mem_powerIdeal_iff r a

example (b : BONG V q L 2) (hvalue : b.value 0 = 1)
    (hgap : 0 < b.binaryOrderGap) :
    Lattice.quadraticValueSet q L ⊆
      Lattice.integralSquareResidueSet
        (Lattice.powerIdeal (K := K) b.binaryOrderGap) :=
  b.quadraticValueSet_subset_powerIdeal_of_normalized_binaryOrderGap_pos
    hvalue hgap

#print axioms Bong.Dyadic.ordUnit_uniformizerPowerUnit
#print axioms Bong.Lattice.mem_powerIdeal_iff
#print axioms Bong.Lattice.principalIdeal_eq_powerIdeal
#print axioms Bong.BONG.quadraticValueSet_subset_powerIdeal_of_normalized_binaryOrderGap_pos

end

end BongTest.M59
