/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EqualRankInduction
import Bong.Bong.Beli2019SameRankCommonSpace
import Bong.Bong.BasisLattice

/-!
# Beli (2019): low-rank boundary cases

The final induction starts in rank one.  In that rank condition (i) is
exactly the reverse order inequality for unary lattices, hence gives a
literal lattice inclusion after the ambient spaces are identified.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The rank-one base of Theorem 2.1, proved directly from condition (i). -/
theorem beli2019_rankOne_sufficiency
    (a : GoodBONG q L 1) (b : GoodBONG r M 1)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl 0)) :
    Lattice.Represents q r L M := by
  let D : Beli2019SameRankCommonSpace a b :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  have hconditions : RepresentationConditions a D.sourceImageBONG
      (Nat.le_refl 0) := D.conditions conditions
  have horder : a.order (0 : Fin 1) ≤
      D.sourceImageBONG.order (0 : Fin 1) := by
    rcases hconditions.orderCondition (0 : Fin 1) with h | h
    · exact h
    · rcases h with ⟨hpositive, _⟩
      simp at hpositive
  have hinclusion : D.sourceImage ≤ L :=
    D.sourceImageBONG.toBONG.le_of_order_ge a.toBONG horder
  exact D.represents_image_iff.mp (Lattice.represents_of_le q hinclusion)

end BONG.GoodBONG

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Bundled rank-one base case for the recursive representation problem. -/
theorem not_counterexample_of_sourceIndex_eq_zero
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hzero : p.sourceIndex = 0) : ¬p.Counterexample := by
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  let a := p.targetBONG.castLength
    (show p.targetIndex + 1 = 1 by omega)
  let b := p.sourceBONG.castLength
    (show p.sourceIndex + 1 = 1 by omega)
  let conditions' := representationConditions_castIndices
    p.targetBONG p.sourceBONG p.rankBound p.conditions
      (show p.targetIndex = 0 by omega) hzero
  intro hp
  apply hp
  exact BONG.GoodBONG.beli2019_rankOne_sufficiency
    a b p.ambient conditions'

end Beli2019RepresentationProblem

end Bong
