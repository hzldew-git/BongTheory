/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma318

/-!
# M84 Beli 2003, Lemma 3.18 smoke tests
-/

namespace BongTest.M84

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  [BinaryNormGeneratorLocalLaws.{u, v} K]
  [BinarySpinorLocalLaws.{u, v} K]

example (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x')) :
    Lattice.IsIntegralReflection (L := L) hsub :=
  b.isIntegralReflection_sub_of_equal_normGenerators_binary
    x x' hx hx' heq hsub

example (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap) :
    BONG.BeliLemma318OrderConclusion q x x' :=
  b.equalNormGenerators_orderConclusion_of_two_e_lt_binaryOrderGap
    x x' hx hx' heq hgap

example (b : BONG V q L 2) (x x' : V)
    (hx : Lattice.IsNormGenerator q L x)
    (hx' : Lattice.IsNormGenerator q L x')
    (heq : q.quadratic x = q.quadratic x')
    (hsub : q.IsAnisotropic (x - x'))
    (hgap : 2 * (ramificationIndex K : Int) < b.binaryOrderGap)
    (hminusOrder :
      ord K (q.quadratic (x - x')) =
        ord K (q.quadratic x) + ord K (2 : K) + ord K (2 : K)) :
    squareClass K
        (Units.mk0
          (q.quadratic x * q.quadratic (x - x'))
          (mul_ne_zero
            (b.isAnisotropic_of_isNormGenerator_binary hx) hsub)) ∈
      beliAuxiliarySpinorGroup K b.binaryParameter (by
        have hparameterOrder :
            ordUnit K b.binaryParameter = b.binaryOrderGap := by
          simpa [BONG.binaryParameterOrder, ordUnit] using
            b.binaryParameterOrder_eq_orderGap
        rwa [hparameterOrder]) :=
  b.squareClass_quadratic_mul_sub_mem_auxiliarySpinorGroup
    x x' hx hx' heq hsub hgap hminusOrder

#print axioms Bong.BONG.isIntegralReflection_sub_of_equal_normGenerators_binary
#print axioms Bong.BONG.equalNormGenerators_orderConclusion_of_two_e_lt_binaryOrderGap
#print axioms Bong.BONG.equalNormGenerator_reflectionProduct_mem_auxiliarySpinorGroup
#print axioms Bong.BONG.beliLemma318

end

end BongTest.M84
