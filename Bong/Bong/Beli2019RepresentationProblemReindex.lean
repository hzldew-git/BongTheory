/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationProblem
import Bong.Bong.GoodExistence

/-!
# Reindexing concrete Beli (2019) representation problems

Recursive Section 9 arguments frequently expose an index as `k + 1` and
therefore transport a good BONG from length `m + 1` to the propositionally
equal length `(k + 1) + 1`.  This file proves once and for all that this
transport preserves the four representation conditions and the bundled
recursive problem.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Transporting the two numerical rank indices transports the complete
four-condition certificate. -/
theorem representationConditions_castIndices
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    {m n m' n' : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (conditions : RepresentationConditions a b hRank)
    (hm : m = m') (hn : n = n') :
    RepresentationConditions
      (a.castLength (show m + 1 = m' + 1 by omega))
      (b.castLength (show n + 1 = n' + 1 by omega))
      (show n' ≤ m' by omega) := by
  subst m'
  subst n'
  simpa [BONG.GoodBONG.castLength] using conditions

/-- Reindexing the BONG lengths does not change the concrete recursive
problem built from them. -/
theorem ofData_castIndices_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    {m n m' n' : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank)
    (hm : m = m') (hn : n = n') :
    ofData
        (a.castLength (show m + 1 = m' + 1 by omega))
        (b.castLength (show n + 1 = n' + 1 by omega))
        (show n' ≤ m' by omega) ambient
        (representationConditions_castIndices a b hRank conditions hm hn) =
      ofData a b hRank ambient conditions := by
  subst m'
  subst n'
  rfl

section Eta

variable (p : Beli2019RepresentationProblem.{u, v, w} K)

local instance : AddCommGroup p.Target := p.targetAddCommGroup
local instance : Module K p.Target := p.targetModule
local instance : AddCommGroup p.Source := p.sourceAddCommGroup
local instance : Module K p.Source := p.sourceModule

/-- Every bundled problem is reconstructed exactly by `ofData` from its
projections. -/
@[simp]
theorem ofData_self :
    ofData p.targetBONG p.sourceBONG p.rankBound p.ambient p.conditions = p := by
  cases p
  rfl

end Eta

end Beli2019RepresentationProblem

end Bong
