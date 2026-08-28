/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationStabilization
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.LatticeRescaleIsometry

/-!
# Componentwise transfer of O'Meara fundamental norm groups

Two Jordan splittings with the same ordered scale generators have the same
fundamental norm groups whenever corresponding components have the same
scale ideals and scalar norm groups.  The proof passes through every scale
truncation, including its componentwise lattice rescalings.

The auxiliary scalar-multiplication isometry below relates rescaling a
lattice to rescaling its quadratic form.  It lets equality of norm groups
be transported through a common lattice rescaling without requiring the
two component spaces themselves to be isometric.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Equality of scalar norm groups is preserved when both quadratic forms
are multiplied by the same nonzero scalar. -/
theorem normGroupSet_rescaleQuadraticUnit_eq_of_eq
    (c : Kˣ) (hgroup : normGroupSet q L = normGroupSet r M) :
    normGroupSet (q.rescaleUnit c) L =
      normGroupSet (r.rescaleUnit c) M := by
  ext z
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
    mem_normGroupSet_rescaleQuadraticUnit_iff, hgroup]

/-- Equality of norm groups is preserved by a common lattice rescaling,
even when the two lattices lie in different quadratic spaces. -/
theorem normGroupSet_rescaleLattice_eq_of_eq
    (a : Kˣ) (hgroup : normGroupSet q L = normGroupSet r M) :
    normGroupSet q (rescale a L) = normGroupSet r (rescale a M) := by
  let f := scalarMultiplicationRescaleLatticeIsometry q L a
  let g := scalarMultiplicationRescaleLatticeIsometry r M a
  calc
    normGroupSet q (rescale a L) =
        normGroupSet (q.rescaleUnit (a ^ 2)) L :=
      normGroupSet_eq_of_latticeIsometry f
    _ = normGroupSet (r.rescaleUnit (a ^ 2)) M :=
      normGroupSet_rescaleQuadraticUnit_eq_of_eq (a ^ 2) hgroup
    _ = normGroupSet r (rescale a M) :=
      (normGroupSet_eq_of_latticeIsometry g).symm

namespace JordanDecomposition

variable {s t : Nat}
  {J : JordanDecomposition q L t} {H : JordanDecomposition r M t}

/-- Equal scale generators make the componentwise truncation factors
literally equal. -/
theorem scaleTruncationFactor_eq_of_scaleGenerator_eq
    (hgenerator : ∀ i, H.scaleGenerator i = J.scaleGenerator i)
    (k : Int) (i : Fin t) :
    H.scaleTruncationFactor k i = J.scaleTruncationFactor k i := by
  unfold scaleTruncationFactor
  rw [hgenerator i]

/-- Scale ideals of corresponding scale-truncation components agree when
the original component scale ideals and chosen scale generators agree. -/
theorem scaleTruncationComponent_scaleIdeal_eq_of_componentwise_eq
    (hgenerator : ∀ i, H.scaleGenerator i = J.scaleGenerator i)
    (hscale : ∀ i,
      scaleIdeal (H.component i).space (H.component i).lattice =
        scaleIdeal (J.component i).space (J.component i).lattice)
    (k : Int) (i : Fin t) :
    scaleIdeal ((H.scaleTruncationDecomposition k).component i).space
        ((H.scaleTruncationDecomposition k).component i).lattice =
      scaleIdeal ((J.scaleTruncationDecomposition k).component i).space
        ((J.scaleTruncationDecomposition k).component i).lattice := by
  let c := J.scaleTruncationFactor k i
  have hc : H.scaleTruncationFactor k i = c :=
    scaleTruncationFactor_eq_of_scaleGenerator_eq
      (J := J) (H := H) hgenerator k i
  rw [H.scaleTruncationDecomposition_component,
    J.scaleTruncationDecomposition_component, hc]
  simp only [QuadraticSublattice.rescaleLattice_space,
    QuadraticSublattice.rescaleLattice_lattice]
  change scaleIdeal (H.component i).space
      (rescale c (H.component i).lattice) =
    scaleIdeal (J.component i).space
      (rescale c (J.component i).lattice)
  rw [scaleIdeal_rescale_eq_scalarIdeal_sq,
    scaleIdeal_rescale_eq_scalarIdeal_sq, hscale i]

/-- Norm groups of corresponding scale-truncation components agree under
the same hypotheses. -/
theorem scaleTruncationComponent_normGroupSet_eq_of_componentwise_eq
    (hgenerator : ∀ i, H.scaleGenerator i = J.scaleGenerator i)
    (hgroup : ∀ i,
      normGroupSet (H.component i).space (H.component i).lattice =
        normGroupSet (J.component i).space (J.component i).lattice)
    (k : Int) (i : Fin t) :
    normGroupSet ((H.scaleTruncationDecomposition k).component i).space
        ((H.scaleTruncationDecomposition k).component i).lattice =
      normGroupSet ((J.scaleTruncationDecomposition k).component i).space
        ((J.scaleTruncationDecomposition k).component i).lattice := by
  let c := J.scaleTruncationFactor k i
  have hc : H.scaleTruncationFactor k i = c :=
    scaleTruncationFactor_eq_of_scaleGenerator_eq
      (J := J) (H := H) hgenerator k i
  rw [H.scaleTruncationDecomposition_component,
    J.scaleTruncationDecomposition_component, hc]
  simp only [QuadraticSublattice.rescaleLattice_space,
    QuadraticSublattice.rescaleLattice_lattice]
  change normGroupSet (H.component i).space
      (rescale c (H.component i).lattice) =
    normGroupSet (J.component i).space
      (rescale c (J.component i).lattice)
  exact normGroupSet_rescaleLattice_eq_of_eq c (hgroup i)

/-- Componentwise equality of scale ideals and norm groups preserves every
O'Meara fundamental norm group. -/
theorem fundamentalNormGroup_eq_of_componentwise_eq
    (hgenerator : ∀ i, H.scaleGenerator i = J.scaleGenerator i)
    (hscale : ∀ i,
      scaleIdeal (H.component i).space (H.component i).lattice =
        scaleIdeal (J.component i).space (J.component i).lattice)
    (hgroup : ∀ i,
      normGroupSet (H.component i).space (H.component i).lattice =
        normGroupSet (J.component i).space (J.component i).lattice)
    (i : Fin t) :
    H.fundamentalNormGroup i = J.fundamentalNormGroup i := by
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  rw [hgenerator i]
  exact OrthogonalDecomposition.normGroupSet_eq_of_componentwise_eq
    (H.scaleTruncationDecomposition (ordUnit K (J.scaleGenerator i)))
    (J.scaleTruncationDecomposition (ordUnit K (J.scaleGenerator i)))
    (scaleTruncationComponent_scaleIdeal_eq_of_componentwise_eq
      (J := J) (H := H) hgenerator hscale
        (ordUnit K (J.scaleGenerator i)))
    (scaleTruncationComponent_normGroupSet_eq_of_componentwise_eq
      (J := J) (H := H) hgenerator hgroup
        (ordUnit K (J.scaleGenerator i)))

end JordanDecomposition

end Lattice

end Bong
