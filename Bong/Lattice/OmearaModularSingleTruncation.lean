/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.NormRescale
import Bong.Lattice.PowerIdeal
import Bong.Lattice.HyperbolicLatticeModular
import Bong.Lattice.HyperbolicLatticeInvariants

/-!
# Scale truncation of one modular lattice

O'Meara's scale truncation of an `s`-modular lattice is just the original
lattice rescaled by the positive part of `pi^r / s`.  This one-component
formula is the basic calculation used in 93:28, Step 8.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- A scale truncation of one modular lattice is an explicit lattice
rescaling. -/
theorem scaleTruncation_eq_rescale_of_isModular
    (hL : IsModular q L s) (r : Int) :
    scaleTruncation q L r =
      rescale
        (positivePartUnit
          (scaleTruncationUnit (K := K) r * s⁻¹)) L := by
  let D := singleOrthogonalDecomposition q L
  let c := positivePartUnit
    (scaleTruncationUnit (K := K) r * s⁻¹)
  have hmodular : ∀ i : Fin 1,
      IsModular (D.component i).space
        (D.component i).lattice s := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hL.mapLatticeIsometry
      (wholeQuadraticSublatticeIsometry q L)
  rw [D.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
    (fun _ => s) hmodular r]
  have hfactor :
      OrthogonalDecomposition.modularScaleTruncationFactor
          (fun _ : Fin 1 => s) r = fun _ => c := by
    funext i
    rfl
  rw [hfactor]
  calc
    D.componentwiseRescaleLattice (fun _ => c) =
        rescale c
          (D.componentwiseRescaleLattice (fun _ => 1)) := by
      rw [D.rescale_componentwiseRescaleLattice]
      congr 1
      funext i
      simp
    _ = rescale c L := by
      rw [D.componentwiseRescaleLattice_one]

/-- The norm ideal of a modular scale truncation has the expected adjusted
order. -/
theorem normIdeal_scaleTruncation_eq_powerIdeal_of_isModular
    (hL : IsModular q L s) (hpos : 0 < Module.finrank K V)
    (n : Kˣ)
    (hn : normIdeal q L = principalIdeal (K := K) (n : K))
    (r : Int) :
    normIdeal q (scaleTruncation q L r) =
      powerIdeal (K := K)
        (2 * max 0 (r - ordUnit K s) + ordUnit K n) := by
  rw [scaleTruncation_eq_rescale_of_isModular hL r,
    normIdeal_rescale_eq_principal_of_finrank_pos hpos
      (positivePartUnit
        (scaleTruncationUnit (K := K) r * s⁻¹)) n hn,
    principalIdeal_eq_powerIdeal]
  congr 1
  rw [ordUnit_mul, ordUnit_pow, ordUnit_positivePartUnit,
    ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
    ordUnit_uniformizerPowerUnit]
  ring_nf

/-- Explicit norm ideal of a truncated scaled hyperbolic plane. -/
theorem normIdeal_scaleTruncation_hyperbolicPlane
    (s : Kˣ) (r : Int) :
    normIdeal (QuadraticSpace.hyperbolicPlane s)
        (scaleTruncation (QuadraticSpace.hyperbolicPlane s)
          (hyperbolicPlaneLattice (K := K)) r) =
      powerIdeal (K := K)
        ((ramificationIndex K : Int) + ordUnit K s +
          2 * max 0 (r - ordUnit K s)) := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let twoS : Kˣ := Units.mk0 (2 * (s : K))
    (mul_ne_zero (by norm_num) (Units.ne_zero s))
  have htwoOrder : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact (ramificationIndex_spec K).symm
  have htwoS : twoS = two * s := by
    apply Units.ext
    rfl
  rw [normIdeal_scaleTruncation_eq_powerIdeal_of_isModular
      (hyperbolicPlaneLattice_isModular (K := K) s) (by simp)
      twoS (by
        simpa only [twoS, Units.val_mk0] using
          normIdeal_hyperbolicPlaneLattice (K := K) s) r]
  congr 1
  rw [htwoS, ordUnit_mul, htwoOrder]
  ring_nf

/-- At every target scale, the norm group contributed by a scaled
hyperbolic plane lies in the doubled target scale ideal. -/
theorem normGroupSet_scaleTruncation_hyperbolicPlane_subset_powerIdeal
    (s : Kˣ) (r : Int) :
    normGroupSet (QuadraticSpace.hyperbolicPlane s)
        (scaleTruncation (QuadraticSpace.hyperbolicPlane s)
          (hyperbolicPlaneLattice (K := K)) r) ⊆
      powerIdeal (K := K) ((ramificationIndex K : Int) + r) := by
  intro z hz
  have hzIdeal := normGroupSet_subset_normIdeal
    (QuadraticSpace.hyperbolicPlane s)
    (scaleTruncation (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) r) hz
  rw [normIdeal_scaleTruncation_hyperbolicPlane] at hzIdeal
  apply ((powerIdeal_le_iff
    ((ramificationIndex K : Int) + ordUnit K s +
      2 * max 0 (r - ordUnit K s))
    ((ramificationIndex K : Int) + r)).2 ?_) hzIdeal
  by_cases h : ordUnit K s ≤ r
  · rw [max_eq_right]
    · omega
    · omega
  · rw [max_eq_left]
    · omega
    · omega

end Lattice

end Bong
