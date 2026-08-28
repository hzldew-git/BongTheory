/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas45To47

/-!
# M89 Beli 2003, Lemmas 4.5--4.7 smoke tests
-/

namespace BongTest.M89

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

variable [BeliLemma45Laws.{u, v} K]

example (P : Lattice.ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ∃ P' : Lattice.ModularPairSplitting q L,
      P.PreservesRanksAndScales P' ∧ P.NormsEqualOldSecond P' :=
  P.beliLemma45_i hscale hnorm

variable [BeliLemma46Laws.{u, v} K]
  [BeliSectionFourLaws.{u, v} K]

example : Nonempty (BONG.GoodBONG q L (Module.finrank K V)) :=
  exists_good_bong_of_sectionFour q L

variable [BeliLemma47Laws.{u, v} K]

example (b : BONG V q L n) (hgood : b.IsGood)
    (J : Lattice.JordanDecomposition q L t) :
    Nonempty (BONG.JordanOrderProfileWitness b J) :=
  b.beliLemma47_profile hgood J

example (b c : BONG V q L n) (hb : b.IsGood) (hc : c.IsGood) :
    ∀ i, b.order i = c.order i :=
  b.beliLemma47_orders_eq c hb hc

#print axioms Bong.Lattice.ModularPairSplitting.beliLemma45_i
#print axioms Bong.Lattice.ModularPairSplitting.beliLemma45_ii
#print axioms Bong.exists_good_bong_of_sectionFour
#print axioms Bong.BONG.beliLemma47_profile
#print axioms Bong.BONG.beliLemma47_orders_eq

end

end BongTest.M89
