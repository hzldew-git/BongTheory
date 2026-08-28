/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SameRankCommonSpaceCore
import Bong.Bong.Beli2019RepresentationProblem

/-!
# An equal-rank representation problem in one quadratic space

This file adds the recursive Section 9 problem wrapper to the light-weight
common-space transport developed in `Beli2019SameRankCommonSpaceCore`.
-/

namespace Bong

open Dyadic

universe u v w

namespace Beli2019SameRankCommonSpace

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

variable (D : Beli2019SameRankCommonSpace a b)

/-- The literal same-space representation problem attached to an original
equal-rank four-condition package. -/
noncomputable def problem
    (h : RepresentationConditions a b (Nat.le_refl n)) :
    Beli2019RepresentationProblem.{u, v, v} K :=
  Beli2019RepresentationProblem.ofData a D.sourceImageBONG
    (Nat.le_refl n) (QuadraticSpace.represents_refl q) (D.conditions h)

/-- The mapped problem is representable exactly when the original pair of
lattices is representable. -/
theorem problem_represents_iff
    (h : RepresentationConditions a b (Nat.le_refl n)) :
    (D.problem h).Represents ↔ Lattice.Represents q r L M := by
  change Lattice.Represents q q L D.sourceImage ↔ _
  exact D.represents_image_iff

/-- Counterexample status is preserved by the same-space reduction. -/
theorem problem_counterexample_iff
    (h : RepresentationConditions a b (Nat.le_refl n)) :
    (D.problem h).Counterexample ↔ ¬Lattice.Represents q r L M := by
  exact not_congr (D.problem_represents_iff h)

end Beli2019SameRankCommonSpace

end Bong
