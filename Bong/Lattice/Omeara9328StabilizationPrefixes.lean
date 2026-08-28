/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionPrefixProduct
import Bong.Lattice.Omeara9328StabilizationCancellation

/-!
# Prefix geometry of O'Meara's rank stabilization

For every nonempty cut, the corresponding prefix of the twice-stabilized
Jordan decomposition is gathered into a paired hyperbolic tower over the
original prefix.  This is the local prefix form of the global gathering used
in O'Meara 93:21 and is the geometric input for preservation of all three
conditions in 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {N m : Nat}

/-- Jordan scale generators restricted to a nonempty prefix. -/
noncomputable abbrev prefixScaleGenerator
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) : Kˣ :=
  J.scaleGenerator
    (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- Raw stabilized carrier over a component of a prefix. -/
abbrev prefixSaturationStableCarrier
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) : Type (max u v) :=
  J.saturationStableCarrier
    (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- Raw stabilized form over a component of a prefix. -/
noncomputable abbrev prefixSaturationStableForm
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :=
  J.saturationStableForm
    (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- Raw stabilized lattice over a component of a prefix. -/
noncomputable abbrev prefixSaturationStableLattice
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :=
  J.saturationStableLattice
    (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hk i).1

/-- The numerical prefix embeddings do not depend on the decomposition. -/
theorem prefixIndexEquiv_component_eq
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (D : OrthogonalDecomposition q L (N + 2))
    (E : OrthogonalDecomposition r M (N + 2))
    (hk : m + 1 ≤ N + 2) (i : Fin (m + 1)) :
    (D.prefixIndexEquiv (m + 1) hk i).1 =
      (E.prefixIndexEquiv (m + 1) hk i).1 := by
  apply Fin.ext
  rfl

/-- The raw stabilized prefix product is integrally isometric to the prefix
of the displayed stabilized Jordan splitting. -/
noncomputable def rawSaturationStablePrefixIsometry
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (J.prefixSaturationStableCarrier hk)
        (J.prefixSaturationStableForm hk))
      (J.saturationStableJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).space
      (BONG.blockProductLattice m
        (J.prefixSaturationStableCarrier hk)
        (J.prefixSaturationStableLattice hk))
      (J.saturationStableJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).lattice := by
  let D := J.toOrthogonalDecomposition
  let S := J.saturationStableJordan.toOrthogonalDecomposition
  let rawComponent : ∀ i : Fin (m + 1), Isometry
      (J.prefixSaturationStableForm hk i)
      (S.component (S.prefixIndexEquiv (m + 1) hk i).1).space
      (J.prefixSaturationStableLattice hk i)
      (S.component (S.prefixIndexEquiv (m + 1) hk i).1).lattice := fun i => by
    let f := BONG.blockProductComponentIsometry
      J.saturationStableCarrier J.saturationStableForm
        J.saturationStableLattice
        (D.prefixIndexEquiv (m + 1) hk i).1
    have hidx := prefixIndexEquiv_component_eq D S hk i
    rw [← hidx]
    exact f
  let productIso := BONG.blockProductLatticeIsometry
    (J.prefixSaturationStableForm hk)
    (S.prefixBlockSpace hk)
    (J.prefixSaturationStableLattice hk)
    (S.prefixBlockLattice hk)
    rawComponent
  exact productIso.trans (S.prefixBlockProductIsometry hk)

/-- Gather a stabilized prefix into a paired hyperbolic tower over the raw
coordinate product of the original prefix components. -/
noncomputable def gatherRawSaturationStablePrefix
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) :
    Isometry
      (BONG.blockOrthogonalForm m
        (J.prefixSaturationStableCarrier hk)
        (J.prefixSaturationStableForm hk))
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm m
          (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (J.toOrthogonalDecomposition.prefixBlockSpace hk))
        (m + 1) (J.prefixScaleGenerator hk))
      (BONG.blockProductLattice m
        (J.prefixSaturationStableCarrier hk)
        (J.prefixSaturationStableLattice hk))
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice m
          (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
          (J.toOrthogonalDecomposition.prefixBlockLattice hk))
        (m + 1)) :=
  gatherPairedHyperbolicBlockProduct
    (J.toOrthogonalDecomposition.prefixBlockCarrier hk)
    (J.toOrthogonalDecomposition.prefixBlockSpace hk)
    (J.toOrthogonalDecomposition.prefixBlockLattice hk)
    (J.prefixScaleGenerator hk)

/-- Every stabilized prefix is a paired hyperbolic tower over the actual
original prefix, integrally and quadratically. -/
noncomputable def saturationStablePrefixGatherIsometry
    (J : JordanDecomposition q L (N + 2))
    (hk : m + 1 ≤ N + 2) :
    Isometry
      (J.saturationStableJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).space
      (pairedHyperbolicExtensionForm
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).space
        (m + 1) (J.prefixScaleGenerator hk))
      (J.saturationStableJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (m + 1)).lattice
      (pairedHyperbolicExtensionLattice
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (m + 1)).lattice
        (m + 1)) :=
  (J.rawSaturationStablePrefixIsometry hk).symm |>.trans
    ((J.gatherRawSaturationStablePrefix hk).trans
      (pairedHyperbolicExtensionIsometry
        (J.toOrthogonalDecomposition.prefixBlockProductIsometry hk)
        (m + 1) (J.prefixScaleGenerator hk)))

end JordanDecomposition
end Lattice

end Bong
