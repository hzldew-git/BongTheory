/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularVolume
import Bong.Lattice.VolumeRigidity

/-!
# A scale-and-volume criterion for modularity

If all pairings of `L` are divisible by `a`, then `a⁻¹L` lies in the
integral dual.  If the volume has the modular order forced by `a`, volume
rigidity upgrades this inclusion to equality.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- Divisibility of every scale pairing by `a` puts `a⁻¹L` inside the
integral dual. -/
theorem rescale_inv_le_dualLattice_of_scaleIdeal_le
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hscale : scaleIdeal q L ≤ principalIdeal (K := K) (a : K)) :
    rescale a⁻¹ L ≤ dualLattice q L := by
  intro z hz
  change z ∈ rescale a⁻¹ L at hz
  rw [mem_rescale_iff] at hz
  rcases hz with ⟨y, hy, rfl⟩
  change ((a⁻¹ : Kˣ) : K) • y ∈ dualLattice q L
  rw [mem_dualLattice_iff]
  intro w hw
  have hpair := hscale (bilin_mem_scaleIdeal_of_mem q L hy hw)
  rw [principalIdeal, Submodule.mem_span_singleton] at hpair
  rcases hpair with ⟨c, hc⟩
  have hcField : algebraMap (IntegerRing K) K c * (a : K) =
      q.bilin y w := by
    simpa only [Algebra.smul_def] using hc
  change q.bilin (((a⁻¹ : Kˣ) : K) • y) w ∈ IntegerRing K
  rw [LinearMap.BilinForm.smul_left, ← hcField]
  convert c.property using 1
  simp [mul_comm]

/-- An inclusion `a⁻¹L ⊆ L♯` with the correct volume is equality. -/
theorem isModular_of_rescale_inv_le_dualLattice
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hinclusion : rescale a⁻¹ L ≤ dualLattice q L)
    (hvolume : volumeOrder q L =
      (finrank K V : Int) * ordUnit K a) :
    IsModular q L a := by
  rw [IsModular]
  apply Eq.symm
  apply eq_of_le_of_volumeOrder_eq q
    (rescale a⁻¹ L) (dualLattice q L) hinclusion
  rw [volumeOrder_rescale, volumeOrder_dualLattice,
    ordUnit_inv, hvolume]
  ring

/-- Scale divisibility plus the expected determinant order characterizes
modularity in the direction needed for binary BONGs. -/
theorem isModular_of_scaleIdeal_le_of_volumeOrder_eq
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hscale : scaleIdeal q L ≤ principalIdeal (K := K) (a : K))
    (hvolume : volumeOrder q L =
      (finrank K V : Int) * ordUnit K a) :
    IsModular q L a :=
  isModular_of_rescale_inv_le_dualLattice q L a
    (rescale_inv_le_dualLattice_of_scaleIdeal_le q L a hscale)
    hvolume

end Lattice

end Bong
