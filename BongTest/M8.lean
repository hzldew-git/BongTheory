/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M8 reconstruction-reduction smoke tests

These examples exercise lattice sums, their norm ideals and projections, and
the derivation of Beli's reconstruction law from smaller local ingredients.
-/

namespace BongTest.M8

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

section LatticeSum

variable (q : QuadraticSpace K V) (L M : Bong.Lattice K V)

example : L ≤ Bong.Lattice.sup L M :=
  Bong.Lattice.le_sup_left L M

example {z : V} :
    z ∈ Bong.Lattice.sup L M ↔ ∃ x ∈ L, ∃ y ∈ M, x + y = z :=
  Bong.Lattice.mem_sup_iff

example (x : V) (hx : q.IsAnisotropic x) :
    Bong.Lattice.projectedLattice q (Bong.Lattice.sup L M) x hx =
      Bong.Lattice.sup (Bong.Lattice.projectedLattice q L x hx)
        (Bong.Lattice.projectedLattice q M x hx) :=
  Bong.Lattice.projectedLattice_sup q L M x hx

variable (I : Bong.Lattice.CoefficientIdeal (K := K))

example (hL : Bong.Lattice.normIdeal q L ≤ I)
    (hM : Bong.Lattice.normIdeal q M ≤ I)
    (hcross : ∀ x ∈ L, ∀ y ∈ M,
      (2 : IntegerRing K) • q.bilin x y ∈ I) :
    Bong.Lattice.normIdeal q (Bong.Lattice.sup L M) ≤ I :=
  Bong.Lattice.normIdeal_sup_le q L M I hL hM hcross

end LatticeSum

section DeterminantAndVolume

variable (q : QuadraticSpace K V) (L M : Bong.Lattice K V)

example (h : Bong.Lattice.determinantClass q L = Bong.Lattice.determinantClass q M) :
    Bong.Lattice.volumeIdeal q L = Bong.Lattice.volumeIdeal q M :=
  Bong.Lattice.volumeIdeal_eq_of_determinantClass_eq q L M h

end DeterminantAndVolume

section LocalReconstruction

variable [Bong.BONGDeterminantProjectionLaws.{u, v} K]
  [Bong.BONGMixedPairingLaws.{u, v} K]
  [Bong.LatticeVolumeRigidityLaws.{u, v} K]

example : Bong.BONGReconstructionLaws.{u, v} K :=
  inferInstance

example (q : QuadraticSpace K V) (M N : Bong.Lattice K V) (x : V)
    (generator : Bong.Lattice.IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    (norm_le : Bong.Lattice.normIdeal q N ≤ Bong.Lattice.normIdeal q M)
    (projection_le :
      Bong.Lattice.projectedLattice q N x anisotropic ≤
        Bong.Lattice.projectedLattice q M x anisotropic) :
    N ≤ M :=
  Bong.Lattice.le_of_normIdeal_le_of_projectedLattice_le_of_local_laws
    q M N x generator anisotropic norm_le projection_le

end LocalReconstruction

section CombinedLocalLaws

variable [Bong.BONGSectionTwoLocalLaws.{u, v} K]

example : Bong.BONGReconstructionLaws.{u, v} K :=
  inferInstance

end CombinedLocalLaws

end

end BongTest.M8
