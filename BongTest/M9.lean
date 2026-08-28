/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M9 volume-rigidity smoke tests

These examples exercise the inclusion-matrix determinant formula, unconditional
volume rigidity, and reconstruction using only the two remaining local inputs.
-/

namespace BongTest.M9

open Bong
open Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

section VolumeRigidity

variable (q : QuadraticSpace K V) (L M : Bong.Lattice K V)

example (hLM : L ≤ M) :
    Bong.Lattice.determinant q L = Bong.Lattice.determinant q M *
      (((Bong.Lattice.inclusionMatrix hLM).det : IntegerRing K) : K) ^ 2 :=
  Bong.Lattice.determinant_eq_mul_sq_inclusionMatrix_det q hLM

example (hLM : L ≤ M)
    (hvolume : Bong.Lattice.volumeIdeal q L = Bong.Lattice.volumeIdeal q M) :
    L = M :=
  Bong.Lattice.eq_of_le_of_volumeIdeal_eq q L M hLM hvolume

example : Bong.LatticeVolumeRigidityLaws.{u, v} K :=
  inferInstance

end VolumeRigidity

section Reconstruction

variable [Bong.BONGDeterminantProjectionLaws.{u, v} K]
  [Bong.BONGMixedPairingLaws.{u, v} K]

example : Bong.BONGReconstructionLaws.{u, v} K :=
  inferInstance

end Reconstruction

end

end BongTest.M9
