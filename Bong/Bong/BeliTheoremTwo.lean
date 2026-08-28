/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma71
import Bong.Bong.BeliLemma64
import Bong.Bong.Properties

/-!
# Beli (2003), Theorem 2

The lattice is represented by an exact orthogonal decomposition into a finite
tower of scaled hyperbolic planes followed by a residual lattice.  The latter
comes with a nonempty BONG and is required not to split another scaled
hyperbolic plane.  This makes every hypothesis and both conditions of Theorem
2 literal Lean data.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}

namespace Lattice

/-- An exact decomposition into `t` scaled hyperbolic planes and one residual
lattice carrying a nonempty BONG. -/
structure HyperbolicTowerSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) (t n : Nat) where
  /-- The first `t` components are hyperbolic and the final one is residual. -/
  decomposition : OrthogonalDecomposition q L (t + 1)
  /-- Scale exponent of every hyperbolic component. -/
  scaleOrder : Fin t → Int
  /-- Exact hyperbolic models for the first `t` components. -/
  hyperbolic : ∀ i : Fin t,
    IsIsometric (decomposition.component i.castSucc).space
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (scaleOrder i)))
      (decomposition.component i.castSucc).lattice
      (hyperbolicPlaneLattice (K := K))
  /-- A good-coordinate candidate on the residual component. -/
  remainderBONG :
    BONG (decomposition.component (Fin.last t)).carrier
      (decomposition.component (Fin.last t)).space
      (decomposition.component (Fin.last t)).lattice (n + 1)
  /-- The residual lattice contains no scaled hyperbolic plane. -/
  remainderDoesNotSplitHyperbolicPlane :
    ∀ r : Int,
      ¬(decomposition.component (Fin.last t)).ContainsScaledHyperbolicPlane r

namespace HyperbolicTowerSplitting

/-- The residual lattice has property A. -/
def RemainderHasPropertyA
    (S : HyperbolicTowerSplitting q L t n) : Prop :=
  S.remainderBONG.HasPropertyA

/-- The residual spinor-norm group is contained in unit square classes. -/
def RemainderIsUnitBounded
    (S : HyperbolicTowerSplitting q L t n) : Prop :=
  SpinorNormIsUnitBounded
    (S.decomposition.component (Fin.last t)).space
    (S.decomposition.component (Fin.last t)).lattice

/-- Every hyperbolic norm order `rᵢ + e` has the parity of the residual norm
order. -/
def AllNormOrdersSameParity
    (S : HyperbolicTowerSplitting q L t n) : Prop :=
  ∀ i : Fin t,
    Int.ModEq 2 (S.scaleOrder i + ramificationIndex K)
      (S.remainderBONG.order 0)

/-- The two conditions displayed in Beli (2003), Theorem 2. -/
def SatisfiesTheoremTwoConditions
    (S : HyperbolicTowerSplitting q L t n) : Prop :=
  (S.RemainderHasPropertyA ∧ S.RemainderIsUnitBounded) ∧
    S.AllNormOrdersSameParity

end HyperbolicTowerSplitting

end Lattice

/-- The residual-extraction and hyperbolic-tower induction in Beli (2003),
Theorem 2.  This interface has no default instance. -/
class BeliTheoremTwoLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  remainder_propertyA_of_full_unit_bound
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
    (S : Lattice.HyperbolicTowerSplitting q L t n) :
    Lattice.SpinorNormIsUnitBounded q L →
      S.RemainderHasPropertyA
  remainder_unit_bound_of_full_unit_bound
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
    (S : Lattice.HyperbolicTowerSplitting q L t n) :
    Lattice.SpinorNormIsUnitBounded q L →
      S.RemainderIsUnitBounded
  norm_parity_of_full_unit_bound
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
    (S : Lattice.HyperbolicTowerSplitting q L t n) :
    Lattice.SpinorNormIsUnitBounded q L →
      S.AllNormOrdersSameParity
  full_unit_bound_of_conditions
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
    (S : Lattice.HyperbolicTowerSplitting q L t n) :
    S.SatisfiesTheoremTwoConditions →
      Lattice.SpinorNormIsUnitBounded q L
  spinorNorm_eq_unit_of_conditions_of_hyperbolic
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}
    (S : Lattice.HyperbolicTowerSplitting q L t n) :
    S.SatisfiesTheoremTwoConditions → 0 < t →
      Lattice.spinorNormImageSubgroup (q := q) (L := L) =
        valuationUnitSquareClassSubgroup K

namespace Lattice

variable [BeliTheoremTwoLaws.{u, v} K]

/-- Beli (2003), Theorem 2. -/
theorem beliTheoremTwo
    (S : HyperbolicTowerSplitting q L t n) :
    SpinorNormIsUnitBounded q L ↔
      S.SatisfiesTheoremTwoConditions := by
  constructor
  · intro hunit
    exact ⟨⟨
      BeliTheoremTwoLaws.remainder_propertyA_of_full_unit_bound S hunit,
      BeliTheoremTwoLaws.remainder_unit_bound_of_full_unit_bound S hunit⟩,
      BeliTheoremTwoLaws.norm_parity_of_full_unit_bound S hunit⟩
  · exact BeliTheoremTwoLaws.full_unit_bound_of_conditions S

/-- If at least one hyperbolic plane occurs, Theorem 2's inclusion is an
equality. -/
theorem beliTheoremTwo_eq_unit
    (S : HyperbolicTowerSplitting q L t n)
    (hconditions : S.SatisfiesTheoremTwoConditions) (ht : 0 < t) :
    spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K :=
  BeliTheoremTwoLaws.spinorNorm_eq_unit_of_conditions_of_hyperbolic
    S hconditions ht

/-- Failure of either displayed condition is equivalent to failure of the
unit-square-class bound. -/
theorem not_spinorNormIsUnitBounded_iff_not_theoremTwoConditions
    (S : HyperbolicTowerSplitting q L t n) :
    ¬SpinorNormIsUnitBounded q L ↔
      ¬S.SatisfiesTheoremTwoConditions :=
  not_congr (beliTheoremTwo S)

end Lattice

end Bong
