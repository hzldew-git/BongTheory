/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma66

/-!
# M98 Beli 2003, Lemma 6.6 and its remark smoke tests
-/

namespace BongTest.M98

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (f : Lattice.IntegralRotation q L) (x : V) :
    q.quadratic (f.apply x) = q.quadratic x :=
  f.quadratic_apply x

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66FlooredDepth ≤ b.lemma66SharpDepth :=
  b.lemma66FlooredDepth_le_sharpDepth hB

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB) :
    b.lemma66SharpHeadFactor ≤ b.lemma66FlooredHeadFactor :=
  b.lemma66SharpHeadFactor_le_floored hB

example (b : BONG V q L (n + 3)) (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head) :
    Lattice.IsNormGenerator q L x :=
  b.isNormGenerator_of_quadratic_eq_head x hx heq

variable [BONG.BeliLemma66Laws.{u, v} K]

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66SharpTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧ f.spinorNorm ∈ b.lemma66SharpHeadFactor :=
  b.beliLemma66 hB x hx heq hproper

example (b : BONG V q L (n + 3)) (hB : b.HasPropertyB)
    (x : V) (hx : x ∈ L)
    (heq : q.quadratic x = q.quadratic b.head)
    (hproper : b.lemma66FlooredTailFactor ≠ ⊤) :
    ∃ f : Lattice.IntegralRotation q L,
      f.apply b.head = x ∧ f.spinorNorm ∈ b.lemma66FlooredHeadFactor :=
  b.beliLemma66_floored hB x hx heq hproper

#print axioms Bong.Lattice.IntegralRotation.quadratic_apply
#print axioms Bong.Lattice.IntegralRotation.apply_mem
#print axioms Bong.BONG.lemma66FlooredDepth_le_sharpDepth
#print axioms Bong.BONG.lemma66SharpCongruenceFactor_le_floored
#print axioms Bong.BONG.lemma66SharpHeadFactor_le_floored
#print axioms Bong.BONG.isNormGenerator_of_quadratic_eq_head
#print axioms Bong.BONG.beliLemma66
#print axioms Bong.BONG.beliLemma66_floored

end BongTest.M98
