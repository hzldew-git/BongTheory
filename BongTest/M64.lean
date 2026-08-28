/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorGroup

/-!
# M64 Beli paragraph 3.12 representative smoke tests
-/

namespace BongTest.M64

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

example (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y)
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    b.normGeneratorValueRatioUnit ((u : K) • y)
        (hy.smul_valuationUnit u hu) =
      u ^ 2 * b.normGeneratorValueRatioUnit y hy :=
  b.normGeneratorValueRatioUnit_smul y hy u hu

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

example (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.binaryParameter) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) :=
  b.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup u hu

#print axioms Bong.Lattice.IsNormGenerator.smul_valuationUnit
#print axioms Bong.BONG.normGeneratorValueRatioUnit_smul
#print axioms
  Bong.BONG.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup

end

end BongTest.M64
