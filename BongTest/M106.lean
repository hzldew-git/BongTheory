/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionTwo

/-!
# M106 Beli 2006, Section 2 smoke tests
-/

namespace BongTest.M106

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

example (b : BONG V q L 2) :
    b.binarySimilarityOrder = b.order 1 - b.order 0 :=
  b.binarySimilarityOrder_eq

variable [BeliLemma43ConstructionLaws.{u, v} K]
  [Beli2006SectionTwoLaws.{u, v} K]

example (X : BONG.OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.SatisfiesGoodBONGCriteria :=
  X.hasGoodRealization_iff_beli2006Criteria

variable [BeliSectionFourLaws.{u, v} K]

example (b : BONG V q L n) :
    b.IsGood ↔
      ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
          (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
        b.IsPutTogether M.toOrthogonalDecomposition c ∧
          BONG.AllBinaryComponentsImproper M c :=
  b.isGood_iff_exists_maximalNormSplitting

#print axioms Bong.BONG.binarySimilarityOrder_eq
#print axioms Bong.BONG.OrthogonalBasisData.adjacentPair_binaryParameter_eq
#print axioms Bong.BONG.OrthogonalBasisData.hasGoodRealization_iff_beli2006Criteria
#print axioms Bong.BONG.isGood_iff_exists_maximalNormSplitting

end BongTest.M106
