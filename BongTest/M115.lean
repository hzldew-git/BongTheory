/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009MainTheorem

/-!
# M115 Beli 2009/2010, Lemmas 3.8--3.9 and Theorem 3.1 smoke tests
-/

namespace BongTest.M115

open Bong Bong.Dyadic

example (D : Beli2009RegularBoundaryThresholdData) : True := by
  have _ := D.beli2009Lemma38_i
  have _ := D.beli2009Lemma38_ii
  trivial

example (D : Beli2009UnaryBoundaryThresholdData) : True := by
  have _ := D.beli2009Lemma38_iii
  trivial

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

example (D : Beli2009RepresentationReduction a b) :
    a.InternalRepresentationConditions b ↔ D.omearaII ∧ D.omearaIII :=
  D.beli2009Lemma39

example (ambient : q.IsIsometric r)
    (D : Beli2009ClassificationReduction ambient a b) : True := by
  have _ := D.firstThree_iff
  trivial

example (ambient : q.IsIsometric r)
    (D : Beli2009ClassificationReduction ambient a b)
    [Beli2009Omeara9328Laws D] :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b :=
  D.beli2009Theorem31

#print axioms Bong.threshold_congr_of_eq_or_both_gt
#print axioms Bong.sum_gt_iff_sum_capped_min
#print axioms Bong.Beli2009RegularBoundaryThresholdData.beli2009Lemma38_i
#print axioms Bong.Beli2009RegularBoundaryThresholdData.beli2009Lemma38_ii
#print axioms Bong.Beli2009UnaryBoundaryThresholdData.beli2009Lemma38_iii
#print axioms Bong.Beli2009RepresentationReduction.beli2009Lemma39
#print axioms Bong.Beli2009ClassificationReduction.firstThree_iff
#print axioms Bong.Beli2009ClassificationReduction.beli2009Theorem31

end BongTest.M115
