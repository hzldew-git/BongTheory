/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma67

/-!
# M99 Beli 2003, Lemma 6.7 smoke tests
-/

namespace BongTest.M99

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Nonempty b.Lemma67Violation :=
  b.exists_lemma67Violation hA hnotB

example (b : BONG V q L (n + 3)) (i : Fin (n + 2)) :
    b.lemma67LocalFactor i ≤ b.theoremOneRHS :=
  b.lemma67LocalFactor_le_theoremOneRHS i

variable [BONG.BeliLemma67Laws.{u, v} K]

example (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    ∃ i : Fin (n + 2), b.lemma67LocalFactor i = ⊤ :=
  b.beliLemma67 hA hnotB

example (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    b.theoremOneRHS = ⊤ :=
  b.theoremOneRHS_eq_top_of_not_propertyB hA hnotB

#print axioms Bong.BONG.exists_lemma67Violation
#print axioms Bong.BONG.lemma67LocalFactor_le_theoremOneRHS
#print axioms Bong.BONG.beliLemma67
#print axioms Bong.BONG.theoremOneRHS_eq_top_of_not_propertyB

end BongTest.M99
