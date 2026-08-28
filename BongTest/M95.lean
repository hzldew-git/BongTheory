/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma63Proof

/-!
# M95 Beli 2003, Definition 11 and Lemma 6.3 smoke tests
-/

namespace BongTest.M95

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (a : Kˣ) :
    beliNormGeneratorGroup K a ≤ beliNormGeneratorUpperGroup K a :=
  beliNormGeneratorGroup_le_upperGroup K a

example (b : BONG V q L (n + 2)) :
    (beliNormGeneratorGroup K (b.adjacentParameter 0 (by simp)) :
        Set (ValuationUnitClass K)) ⊆
      b.normGeneratorValueRatioClassSet :=
  b.beliNormGeneratorGroup_subset_normGeneratorValueRatioClassSet

example (b : BONG V q L (n + 2))
    (w : b.HeadInverseRescaleWitness) (hB : b.HasPropertyBOrInverse w) :
    (beliNormGeneratorGroup K (b.adjacentParameter 0 (by simp)) :
        Set (ValuationUnitClass K)) ⊆
        b.normGeneratorValueRatioClassSet ∧
      b.normGeneratorValueRatioClassSet ⊆
        (beliNormGeneratorUpperGroup K
          (b.adjacentParameter 0 (by simp)) :
            Set (ValuationUnitClass K)) :=
  b.beliLemma63_i w hB

example (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K
        (b.adjacentParameter 0 (by simp)) : Set (ValuationUnitClass K)) :=
  b.beliLemma63_ii hB

#print axioms Bong.Dyadic.beliNormGeneratorGroup_le_upperGroup
#print axioms Bong.BONG.beliNormGeneratorGroup_subset_normGeneratorValueRatioClassSet
#print axioms Bong.BONG.beliLemma63_i
#print axioms Bong.BONG.beliLemma63_ii

end

end BongTest.M95
