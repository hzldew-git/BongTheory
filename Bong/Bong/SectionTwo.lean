/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantProjection
import Bong.Lattice.MixedPairing
import Bong.Lattice.VolumeRigidity

/-!
# Beli 2003, Section 2: recursive BONG consequences

Beli's determinant formula and uniqueness theorem are recursive consequences
of local projection statements.  This file exposes both direct interfaces and
a finer reduction of Lemma 2.2.

The direct classes contain the one-step determinant identity and Lemma 2.2's
containment criterion.  The finer interface replaces the latter by a dyadic
mixed-pairing estimate; general equal-volume rigidity is proved for all full
lattices.  Lattice sums, their norm ideals, and their projected lattices then
supply the rest of the reconstruction argument concretely.
-/

namespace Bong

open Dyadic

universe u v

/-- The one-step integral determinant identity underlying Beli's Lemma 2.1. -/
class BONGDeterminantProjectionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  determinant_projection
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) :
    Lattice.determinantClass q L =
      unitSquareClass K (Units.mk0 (q.quadratic x) anisotropic) *
        Lattice.determinantClass (q.orthogonalSpace x anisotropic)
          (L.projectedLattice q x anisotropic)

/-- The norm-and-projection containment criterion of Beli's Lemma 2.2. -/
class BONGReconstructionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  reconstruction_le
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (M N : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    (norm_le : Lattice.normIdeal q N ≤ Lattice.normIdeal q M)
    (projection_le :
      Lattice.projectedLattice q N x anisotropic ≤
        Lattice.projectedLattice q M x anisotropic) :
    N ≤ M

/--
The dyadic mixed-pairing estimate used when Beli adjoins `N` to `M` in the
proof of Lemma 2.2.
-/
class BONGMixedPairingLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  two_bilin_mem_normIdeal
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (M N : Lattice K V) (x : V)
    (generator : Lattice.IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    (norm_le : Lattice.normIdeal q N ≤ Lattice.normIdeal q M)
    (projection_le :
      Lattice.projectedLattice q N x anisotropic ≤
        Lattice.projectedLattice q M x anisotropic)
    (y z : V) (hy : y ∈ M) (hz : z ∈ N) :
    (2 : IntegerRing K) • q.bilin y z ∈ Lattice.normIdeal q M

/-- Equal-volume nested full lattices coincide. -/
class LatticeVolumeRigidityLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  eq_of_le_of_volumeIdeal_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L M : Lattice K V)
    (hLM : L ≤ M) (hvolume : Lattice.volumeIdeal q L = Lattice.volumeIdeal q M) :
    L = M

/--
The three local ingredients from which the reconstruction law is derived:
one-step determinant, mixed-pairing control, and volume rigidity.
-/
class BONGSectionTwoLocalLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop
    extends BONGDeterminantProjectionLaws.{u, v} K,
      BONGMixedPairingLaws.{u, v} K,
      LatticeVolumeRigidityLaws.{u, v} K

/-- The two independent local law packages used throughout Beli's Section 2. -/
class BONGSectionTwoLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop
    extends BONGDeterminantProjectionLaws.{u, v} K,
      BONGReconstructionLaws.{u, v} K

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Volume rigidity is available for every full lattice over the valuation ring. -/
instance latticeVolumeRigidityLaws : LatticeVolumeRigidityLaws.{u, v} K where
  eq_of_le_of_volumeIdeal_eq := Lattice.eq_of_le_of_volumeIdeal_eq

/-- Beli's one-step determinant identity holds over every dyadic context. -/
instance bongDeterminantProjectionLaws :
    BONGDeterminantProjectionLaws.{u, v} K where
  determinant_projection :=
    Lattice.determinantClass_projection_of_normGenerator

/-- Beli's dyadic mixed-pairing estimate holds over every dyadic context. -/
instance bongMixedPairingLaws : BONGMixedPairingLaws.{u, v} K where
  two_bilin_mem_normIdeal :=
    Lattice.two_bilin_mem_normIdeal_of_normGenerator

namespace Lattice

/-- The one-step determinant identity used in Beli's Lemma 2.1. -/
theorem determinantClass_projection (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    [BONGDeterminantProjectionLaws.{u, v} K] :
    determinantClass q L =
      unitSquareClass K (Units.mk0 (q.quadratic x) anisotropic) *
        determinantClass (q.orthogonalSpace x anisotropic)
          (L.projectedLattice q x anisotropic) :=
  BONGDeterminantProjectionLaws.determinant_projection
    q L x generator anisotropic

/--
Beli's Lemma 2.2 reconstructed from its three smaller local ingredients.  The
sum-lattice, norm-ideal, and projection steps are all proved concretely.
-/
theorem le_of_normIdeal_le_of_projectedLattice_le_of_local_laws
    (q : QuadraticSpace K V) (M N : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x)
    [BONGDeterminantProjectionLaws.{u, v} K]
    [BONGMixedPairingLaws.{u, v} K]
    [LatticeVolumeRigidityLaws.{u, v} K]
    (norm_le : normIdeal q N ≤ normIdeal q M)
    (projection_le :
      projectedLattice q N x anisotropic ≤
        projectedLattice q M x anisotropic) :
    N ≤ M := by
  let P := sup M N
  have hcross : ∀ y ∈ M, ∀ z ∈ N,
      (2 : IntegerRing K) • q.bilin y z ∈ normIdeal q M := by
    intro y hy z hz
    exact BONGMixedPairingLaws.two_bilin_mem_normIdeal
      q M N x generator anisotropic norm_le projection_le y z hy hz
  have generatorP : IsNormGenerator q P x :=
    generator.sup_right norm_le hcross
  have hprojection :
      projectedLattice q P x anisotropic =
        projectedLattice q M x anisotropic :=
    projectedLattice_sup_eq_left_of_le q M N x anisotropic projection_le
  have hdeterminant : determinantClass q P = determinantClass q M := by
    calc
      determinantClass q P =
          unitSquareClass K (Units.mk0 (q.quadratic x) anisotropic) *
            determinantClass (q.orthogonalSpace x anisotropic)
              (projectedLattice q P x anisotropic) :=
        determinantClass_projection q P x generatorP anisotropic
      _ = unitSquareClass K (Units.mk0 (q.quadratic x) anisotropic) *
            determinantClass (q.orthogonalSpace x anisotropic)
              (projectedLattice q M x anisotropic) := by
        rw [hprojection]
      _ = determinantClass q M :=
        (determinantClass_projection q M x generator anisotropic).symm
  have hvolume : volumeIdeal q M = volumeIdeal q P :=
    (volumeIdeal_eq_of_determinantClass_eq q P M hdeterminant).symm
  have hMP : M = P :=
    LatticeVolumeRigidityLaws.eq_of_le_of_volumeIdeal_eq
      q M P (le_sup_left M N) hvolume
  intro z hz
  rw [hMP]
  exact le_sup_right M N hz

/-- Beli's Lemma 2.2, exposed from its minimal local interface. -/
theorem le_of_normIdeal_le_of_projectedLattice_le (q : QuadraticSpace K V)
    (M N : Lattice K V) (x : V) (generator : IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    [BONGReconstructionLaws.{u, v} K]
    (norm_le : normIdeal q N ≤ normIdeal q M)
    (projection_le :
      projectedLattice q N x anisotropic ≤
        projectedLattice q M x anisotropic) :
    N ≤ M :=
  BONGReconstructionLaws.reconstruction_le q M N x generator anisotropic
    norm_le projection_le

/-- Two lattices with a common norm generator and equal projections are equal. -/
theorem eq_of_normIdeal_eq_of_projectedLattice_eq (q : QuadraticSpace K V)
    (M N : Lattice K V) (x : V) (generatorM : IsNormGenerator q M x)
    (generatorN : IsNormGenerator q N x) (anisotropic : q.IsAnisotropic x)
    [BONGReconstructionLaws.{u, v} K]
    (norm_eq : normIdeal q M = normIdeal q N)
    (projection_eq :
      projectedLattice q M x anisotropic =
        projectedLattice q N x anisotropic) :
    M = N := by
  apply Lattice.ext
  apply le_antisymm
  · apply le_of_normIdeal_le_of_projectedLattice_le
      q N M x generatorN anisotropic norm_eq.le
    rw [projection_eq]
    exact fun _ hz ↦ hz
  · apply le_of_normIdeal_le_of_projectedLattice_le
      q M N x generatorM anisotropic norm_eq.ge
    rw [projection_eq]
    exact fun _ hz ↦ hz

end Lattice

/-- The smaller local law package supplies Beli's reconstruction interface. -/
instance bongReconstructionLawsOfLocal
    [BONGDeterminantProjectionLaws.{u, v} K]
    [BONGMixedPairingLaws.{u, v} K]
    [LatticeVolumeRigidityLaws.{u, v} K] :
    BONGReconstructionLaws.{u, v} K where
  reconstruction_le q M N x generator anisotropic norm_le projection_le :=
    Lattice.le_of_normIdeal_le_of_projectedLattice_le_of_local_laws
      q M N x generator anisotropic norm_le projection_le

/-- The three proved local ingredients form Beli's complete Section 2 local package. -/
instance bongSectionTwoLocalLaws : BONGSectionTwoLocalLaws.{u, v} K where
  toBONGDeterminantProjectionLaws := inferInstance
  toBONGMixedPairingLaws := inferInstance
  toLatticeVolumeRigidityLaws := inferInstance

/-- Beli's complete Section 2 law package is unconditional over a dyadic context. -/
instance bongSectionTwoLaws : BONGSectionTwoLaws.{u, v} K where
  toBONGDeterminantProjectionLaws := inferInstance
  toBONGReconstructionLaws := inferInstance

namespace BONG

variable {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Beli's Lemma 2.1, reduced to the one-step projection identity. -/
theorem determinantClass_eq_valueProduct
    [BONGDeterminantProjectionLaws.{u, v} K] (b : BONG V q L n) :
    Lattice.determinantClass q L = unitSquareClass K b.valueProduct := by
  induction b with
  | nil q L exhausted =>
      rw [valueProduct_nil]
      exact Lattice.determinantClass_eq_one_of_subsingleton q L exhausted
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      rw [Lattice.determinantClass_projection q L x generator anisotropic,
        ih, valueProduct_cons, unitSquareClass_mul]
      congr 2

/--
Beli's Corollary 2.6: two lattices carrying the same ambient BONG vectors are
equal, reduced to Lemma 2.2.
-/
theorem lattice_eq_of_ambientVector_eq_from_projection
    [BONGReconstructionLaws.{u, v} K]
    {M : Lattice K V} (b : BONG V q L n) (c : BONG V q M n)
    (vectors : ∀ i, b.ambientVector i = c.ambientVector i) : L = M := by
  induction b with
  | nil q L exhausted =>
      apply Lattice.ext
      ext z
      have hz : z = 0 := Subsingleton.elim z 0
      subst z
      simp
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      cases c with
      | cons y generator' anisotropic' tail' =>
          have hxy : x = y := by
            simpa using vectors 0
          subst y
          have htailVectors :
              ∀ i, tail.ambientVector i = tail'.ambientVector i := by
            intro i
            apply Subtype.ext
            simpa using vectors i.succ
          have hprojection :
              L.projectedLattice q x anisotropic =
                M.projectedLattice q x anisotropic' :=
            ih tail' htailVectors
          have hnorm : Lattice.normIdeal q L = Lattice.normIdeal q M := by
            rw [generator.normIdeal_eq, generator'.normIdeal_eq]
          exact Lattice.eq_of_normIdeal_eq_of_projectedLattice_eq
            q L M x generator generator' anisotropic hnorm hprojection

end BONG

end Bong
