/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M19 unconditional Section 2 API smoke tests
-/

namespace BongTest.M19

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : ℕ}

-- Deliberately no `BONGStructuralLaws` assumption in this file.
example (b : BONG V q L n) :
    Lattice.determinantClass q L = unitSquareClass K b.valueProduct :=
  Lattice.determinantClass_eq_bongValueProduct b

example (b : BONG V q L n) (c : BONG V q M n)
    (h : ∀ i, b.ambientVector i = c.ambientVector i) : L = M :=
  b.lattice_eq_of_ambientVector_eq c h

#print axioms Bong.Lattice.determinantClass_eq_bongValueProduct
#print axioms Bong.BONG.lattice_eq_of_ambientVector_eq

end

end BongTest.M19
