/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup
import Bong.Lattice.Jordan
import Bong.Lattice.SpinorNormMultiplicative
import Bong.QuadraticSpace.HyperbolicPlane

/-!
# Beli (2003), Lemma 7.1

This file introduces the unit-square-class bound used throughout Section 7,
records norm orders by generators of norm ideals, and packages an exact
orthogonal splitting with one scaled hyperbolic plane.  The parity
characterization of unit square classes is proved directly.  The remaining
Eichler-transformation argument in Lemma 7.1 is isolated as a non-default
local law.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- A field square class is represented by a valuation unit exactly when its
valuation has even parity. -/
theorem squareClass_mem_valuationUnitSquareClassSubgroup_iff_even
    (a : Kˣ) :
    squareClass K a ∈ valuationUnitSquareClassSubgroup K ↔
      Even (ordUnit K a) := by
  constructor
  · rintro ⟨u, hu, hclass⟩
    change QuotientGroup.mk' (Subgroup.square Kˣ) u =
      QuotientGroup.mk' (Subgroup.square Kˣ) a at hclass
    rw [QuotientGroup.mk'_eq_mk'] at hclass
    rcases hclass with ⟨s, hs, husa⟩
    change IsSquare s at hs
    rcases hs with ⟨t, rfl⟩
    have huOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).1 hu
    have hord := congrArg (ordUnit K) husa
    rw [ordUnit_mul, ordUnit_mul, huOrder] at hord
    refine ⟨ordUnit K t, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    let t : Kˣ := uniformizerPowerUnit K (-k)
    let u : Kˣ := a * t ^ 2
    have huOrder : ordUnit K u = 0 := by
      simp only [u, t, ordUnit_mul, ordUnit_pow,
        ordUnit_uniformizerPowerUnit]
      omega
    have hu : IsValuationUnit K (u : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
    refine ⟨u, hu, ?_⟩
    exact squareClass_mul_square K a t

end Dyadic

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace Lattice

/-- The assertion `θ(L) ⊆ 𝒪ˣFˣ²`. -/
def SpinorNormIsUnitBounded (q : QuadraticSpace K V)
    (L : Lattice K V) : Prop :=
  spinorNormImageSubgroup (q := q) (L := L) ≤
    valuationUnitSquareClassSubgroup K

/-- A chosen generator of the norm ideal and its valuation order. -/
structure NormOrderDatum (q : QuadraticSpace K V)
    (L : Lattice K V) where
  /-- A nonzero generator of the norm ideal. -/
  generator : Kˣ
  /-- The chosen element generates the norm ideal. -/
  normIdeal_eq : normIdeal q L =
    principalIdeal (K := K) (generator : K)

namespace NormOrderDatum

/-- The order of the norm of a lattice. -/
noncomputable def order (N : NormOrderDatum q L) : Int :=
  ordUnit K N.generator

end NormOrderDatum

/-- Norm-order data for every component of an orthogonal decomposition. -/
def OrthogonalComponentNormData
    (D : OrthogonalDecomposition q L t) :=
  ∀ i : Fin t,
    NormOrderDatum (D.component i).space (D.component i).lattice

/-- An exact orthogonal splitting `L = H ⊥ L₀` with `H` a scaled hyperbolic
plane `πʳ A(0,0)`. -/
structure HyperbolicPlaneSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) where
  /-- The two orthogonal components, hyperbolic first. -/
  decomposition : OrthogonalDecomposition q L 2
  /-- The scale exponent `r`. -/
  scaleOrder : Int
  /-- The first component is the standard scaled hyperbolic plane. -/
  hyperbolic : IsIsometric (decomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane
      (uniformizerPowerUnit K scaleOrder))
    (decomposition.component 0).lattice
    (hyperbolicPlaneLattice (K := K))
  /-- A norm generator for the residual component. -/
  remainderNorm : NormOrderDatum (decomposition.component 1).space
    (decomposition.component 1).lattice

namespace HyperbolicPlaneSplitting

/-- The norm order of `πʳ A(0,0)` is `r + e`. -/
noncomputable def hyperbolicNormOrder
    (S : HyperbolicPlaneSplitting q L) : Int :=
  S.scaleOrder + ramificationIndex K

/-- The residual component has unit-bounded spinor norm. -/
def RemainderIsUnitBounded
    (S : HyperbolicPlaneSplitting q L) : Prop :=
  SpinorNormIsUnitBounded (S.decomposition.component 1).space
    (S.decomposition.component 1).lattice

/-- The hyperbolic and residual norm orders have the same parity. -/
def NormOrdersSameParity
    (S : HyperbolicPlaneSplitting q L) : Prop :=
  Int.ModEq 2 S.hyperbolicNormOrder S.remainderNorm.order

end HyperbolicPlaneSplitting

end Lattice

/-- The remaining reflection and Eichler-transformation arguments in Beli
(2003), Lemma 7.1.  This interface has no default instance. -/
class BeliLemma71Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  component_norm_orders_modEq
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}
    (D : Lattice.OrthogonalDecomposition q L t)
    (N : Lattice.OrthogonalComponentNormData D)
    (hunit : Lattice.SpinorNormIsUnitBounded q L)
    (i j : Fin t) :
    Int.ModEq 2 (N i).order (N j).order
  spinorNorm_eq_unit_of_hyperbolic_splitting
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (S : Lattice.HyperbolicPlaneSplitting q L) :
    S.RemainderIsUnitBounded → S.NormOrdersSameParity →
      Lattice.spinorNormImageSubgroup (q := q) (L := L) =
        valuationUnitSquareClassSubgroup K
  spinorNorm_eq_top_of_hyperbolic_splitting
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (S : Lattice.HyperbolicPlaneSplitting q L) :
    S.RemainderIsUnitBounded → ¬S.NormOrdersSameParity →
      Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤

namespace Lattice

variable [BeliLemma71Laws.{u, v} K]

/-- Beli (2003), Lemma 7.1(i). -/
theorem beliLemma71_i
    (D : OrthogonalDecomposition q L t)
    (N : OrthogonalComponentNormData D)
    (hunit : SpinorNormIsUnitBounded q L) (i j : Fin t) :
    Int.ModEq 2 (N i).order (N j).order :=
  BeliLemma71Laws.component_norm_orders_modEq D N hunit i j

/-- Beli (2003), Lemma 7.1(ii), equal-parity branch. -/
theorem beliLemma71_ii_same
    (S : HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : S.NormOrdersSameParity) :
    spinorNormImageSubgroup (q := q) (L := L) =
      valuationUnitSquareClassSubgroup K :=
  BeliLemma71Laws.spinorNorm_eq_unit_of_hyperbolic_splitting
    S hunit hparity

/-- Beli (2003), Lemma 7.1(ii), unequal-parity branch. -/
theorem beliLemma71_ii_different
    (S : HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded)
    (hparity : ¬S.NormOrdersSameParity) :
    spinorNormImageSubgroup (q := q) (L := L) = ⊤ :=
  BeliLemma71Laws.spinorNorm_eq_top_of_hyperbolic_splitting
    S hunit hparity

/-- The two branches of Lemma 7.1(ii) in one statement. -/
theorem beliLemma71_ii
    (S : HyperbolicPlaneSplitting q L)
    (hunit : S.RemainderIsUnitBounded) :
    (S.NormOrdersSameParity →
      spinorNormImageSubgroup (q := q) (L := L) =
        valuationUnitSquareClassSubgroup K) ∧
    (¬S.NormOrdersSameParity →
      spinorNormImageSubgroup (q := q) (L := L) = ⊤) :=
  ⟨beliLemma71_ii_same S hunit,
    beliLemma71_ii_different S hunit⟩

end Lattice

end Bong
