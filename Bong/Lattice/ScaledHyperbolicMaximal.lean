/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Lattice.Dual
import Bong.QuadraticSpace.HyperbolicPlane

/-!
# Norm-maximal scaled hyperbolic plane lattices

O'Meara's maximal-lattice theorems imply that a scaled hyperbolic plane
lattice is maximal among lattices in its quadratic space with a fixed norm
ideal.  Its integral dual has the corresponding property as well.  These are
the precise external local-lattice inputs used in Beli (2019), Lemma 9.7(ii).

They are kept as a narrow law package because O'Meara's maximal-lattice
theory is not yet available in mathlib.  No Beli representation criterion is
stored in this interface.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A lattice is a uniformizer-scaled copy of the standard hyperbolic plane
lattice. -/
def IsScaledHyperbolicLattice (q : QuadraticSpace K V) (L : Lattice K V) :
    Prop :=
  ∃ R : Int,
    IsIsometric q
      (QuadraticSpace.hyperbolicPlane (uniformizerPowerUnit K R))
      L (hyperbolicPlaneLattice (K := K))

/-- `L` is norm-maximal if it represents every lattice in an isometric
ambient quadratic space whose norm ideal is contained in that of `L`. -/
def IsNormMaximal (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W},
    q.IsIsometric r → normIdeal r M ≤ normIdeal q L →
      Represents q r L M

end Lattice

/-- The O'Meara maximality input for a scaled hyperbolic plane and its
integral dual.  This class intentionally has no default instance. -/
class ScaledHyperbolicMaximalLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  normMaximal
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (h : Lattice.IsScaledHyperbolicLattice q L) :
    Lattice.IsNormMaximal.{u, v, w} q L
  dualNormMaximal
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (h : Lattice.IsScaledHyperbolicLattice q L) :
    Lattice.IsNormMaximal.{u, v, w} q (Lattice.dualLattice q L)

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  [ScaledHyperbolicMaximalLaws.{u, v, w} K]
  {q : QuadraticSpace K V} {L : Lattice K V}

theorem IsScaledHyperbolicLattice.isNormMaximal
    (h : IsScaledHyperbolicLattice q L) : IsNormMaximal.{u, v, w} q L :=
  ScaledHyperbolicMaximalLaws.normMaximal h

theorem IsScaledHyperbolicLattice.dual_isNormMaximal
    (h : IsScaledHyperbolicLattice q L) :
    IsNormMaximal.{u, v, w} q (dualLattice q L) :=
  ScaledHyperbolicMaximalLaws.dualNormMaximal h

end Lattice

end Bong
