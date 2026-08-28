/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009TwoAdic

/-!
# M116 Beli 2009/2010, Section 4 smoke tests
-/

namespace BongTest.M116

open Bong Bong.Dyadic

example (leftGap rightGap : Int) : True := by
  have _ := twoAdic_alpha_sum_gt_two_iff leftGap rightGap
  trivial

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

section Lemma41

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

example (a : BONG.GoodBONG q L (n + 1)) (i : Fin n)
    (htwoAdic : ramificationIndex K = 1) : True := by
  have _ := a.beli2009Lemma41 i htwoAdic
  trivial

end Lemma41

section Theorem42

variable [alphaV : Beli2006AlphaLaws.{u, v} K]
  [parityV : Beli2009AlphaParityLaws.{u, v} K]
  [alphaW : Beli2006AlphaLaws.{u, w} K]
  [parityW : Beli2009AlphaParityLaws.{u, w} K]
  [QuadraticDefectLaws K]
  [twoAdicLaws : Beli2009TwoAdicDefectClassLaws K]
  {ambient : q.IsIsometric r}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

example (D : Beli2009ClassificationReduction ambient a b)
    [Beli2009Omeara9328Laws D]
    (htwoAdic : ramificationIndex K = 1) : True := by
  have _ := D.beli2009Theorem42
    (alphaV := alphaV) (parityV := parityV)
    (alphaW := alphaW) (parityW := parityW) htwoAdic
  trivial

end Theorem42

#print axioms Bong.twoAdic_alpha_sum_gt_two_iff
#print axioms Bong.BONG.GoodBONG.orderGap_ge_neg_two_mul_e
#print axioms Bong.BONG.GoodBONG.orderGap_even_of_negative
#print axioms Bong.BONG.GoodBONG.beli2009Lemma41
#print axioms Bong.BONG.GoodBONG.defectOrder_ge_iff_isSquare_of_two_lt
#print axioms Bong.BONG.GoodBONG.twoAdicInternalTrigger_iff
#print axioms Bong.BONG.GoodBONG.prefixDefectBounds_iff_twoAdic
#print axioms Bong.Beli2009TwoAdicClassificationConditions.classificationConditions_iff
#print axioms Bong.Beli2009ClassificationReduction.beli2009Theorem42

end BongTest.M116
