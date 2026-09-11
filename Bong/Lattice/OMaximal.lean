/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009WeightIdealProof
import Bong.Lattice.FormRescale
import Bong.Lattice.Omeara933MaximalLattice
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.Universality

/-!
# Maximal integral lattices

This file formalizes O'Meara's notion of an `O`-maximal lattice: an
integral lattice which has no proper integral over-lattice in the same
quadratic space.  It also proves O'Meara 82:18, the existence of a maximal
integral over-lattice.

The existence proof uses the discreteness of the dyadic valuation.  Although
the volume order of an integral quadratic lattice need not be nonnegative,
rescaling the quadratic form by `2` makes its scale integral.  Consequently

`volumeOrder q L + rank(L) * e >= 0`,

and a volume-minimal integral over-lattice exists by well-ordering of the
natural numbers.  Volume rigidity then proves maximality.  No maximal-lattice
or choice axiom beyond Lean's ordinary classical choice is assumed.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- An `O`-maximal lattice is maximal, under inclusion in its fixed ambient
quadratic space, among lattices whose quadratic values lie in `O`. -/
def IsOMaximal (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  IsIntegral q L ∧
    ∀ M : Lattice K V, L ≤ M → IsIntegral q M → M = L

namespace IsOMaximal

theorem isIntegral (h : IsOMaximal q L) : IsIntegral q L := h.1

theorem eq_of_le (h : IsOMaximal q L) (M : Lattice K V)
    (hLM : L ≤ M) (hM : IsIntegral q M) : M = L :=
  h.2 M hLM hM

end IsOMaximal

/-- Multiplication of a coefficient ideal by the field element `2` is the
same operation as `twiceIdeal`. -/
theorem scalarIdeal_two_eq_twiceIdeal
    (I : CoefficientIdeal (K := K)) :
    scalarIdeal (2 : K) I = twiceIdeal I := by
  rw [scalarIdeal, twiceIdeal]
  congr 1

/-- The form obtained by multiplying `q` by two has integral scale whenever
`L` is an integral quadratic lattice for `q`. -/
theorem scaleIdeal_rescaleTwo_le_unitIdeal
    (hL : IsIntegral q L) :
    scaleIdeal (q.rescaleUnit (Units.mk0 (2 : K) (by norm_num))) L ≤
      unitIdeal (K := K) := by
  rw [scaleIdeal_rescaleQuadraticUnit]
  change scalarIdeal (2 : K) (scaleIdeal q L) ≤ unitIdeal (K := K)
  rw [scalarIdeal_two_eq_twiceIdeal]
  exact (twoScaleIdeal_le_normIdeal q L).trans
    ((isIntegral_iff_normIdeal_le q L).1 hL)

/-- The shifted volume order used in the maximal-lattice argument. -/
noncomputable def integralShiftedVolumeOrder
    (q : QuadraticSpace K V) (L : Lattice K V) : Int :=
  volumeOrder q L +
    (finrank K V : Int) * (ramificationIndex K : Int)

/-- Shifted volume is nonnegative on every integral lattice. -/
theorem integralShiftedVolumeOrder_nonneg
    (hL : IsIntegral q L) :
    0 ≤ integralShiftedVolumeOrder q L := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have hnonneg := volumeOrder_nonneg_of_scaleIdeal_le_unitIdeal
    (q := q.rescaleUnit two) (L := L)
    (scaleIdeal_rescaleTwo_le_unitIdeal (q := q) (L := L) hL)
  have htwo : ordUnit K two = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (2 : K) =
      (((ramificationIndex K : Nat) : Int) : WithTop Int)
    exact (ramificationIndex_spec (K := K)).symm
  rw [volumeOrder_rescaleUnit, htwo] at hnonneg
  exact hnonneg

/-- Integral over-lattices considered in the proof of O'Meara 82:18. -/
structure OMaximalCandidate (q : QuadraticSpace K V)
    (L : Lattice K V) where
  lattice : Lattice K V
  contains : L ≤ lattice
  integral : IsIntegral q lattice

namespace OMaximalCandidate

variable (q L)

def initial (hL : IsIntegral q L) : OMaximalCandidate q L where
  lattice := L
  contains := fun _ hx => hx
  integral := hL

theorem shiftedVolume_nonneg (C : OMaximalCandidate q L) :
    0 ≤ integralShiftedVolumeOrder q C.lattice :=
  integralShiftedVolumeOrder_nonneg C.integral

end OMaximalCandidate

/-- A volume-minimal integral over-lattice of `L`. -/
structure OMaximalMinimalData (q : QuadraticSpace K V)
    (L : Lattice K V) where
  candidate : OMaximalCandidate q L
  minimal : ∀ D : OMaximalCandidate q L,
    volumeOrder q candidate.lattice ≤ volumeOrder q D.lattice

/-- Choose an integral over-lattice of smallest volume order. -/
noncomputable def oMaximalMinimalData
    (hL : IsIntegral q L) : OMaximalMinimalData q L := by
  classical
  let ExistsAt : Nat → Prop := fun n =>
    ∃ C : OMaximalCandidate q L,
      integralShiftedVolumeOrder q C.lattice = (n : Int)
  have hexists : ∃ n, ExistsAt n := by
    let C := OMaximalCandidate.initial q L hL
    refine ⟨(integralShiftedVolumeOrder q L).toNat, C, ?_⟩
    dsimp only [C, OMaximalCandidate.initial]
    exact (Int.toNat_of_nonneg
      (OMaximalCandidate.shiftedVolume_nonneg q L C)).symm
  let n := Nat.find hexists
  have hn : ExistsAt n := Nat.find_spec hexists
  let C : OMaximalCandidate q L := Classical.choose hn
  have hC : integralShiftedVolumeOrder q C.lattice = (n : Int) :=
    Classical.choose_spec hn
  refine ⟨C, ?_⟩
  intro D
  have hDnonneg := D.shiftedVolume_nonneg q L
  have hDexists : ExistsAt
      (integralShiftedVolumeOrder q D.lattice).toNat := by
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hDnonneg]
  have hnat : n ≤ (integralShiftedVolumeOrder q D.lattice).toNat := by
    simpa only [n] using Nat.find_min' hexists hDexists
  have hshifted : integralShiftedVolumeOrder q C.lattice ≤
      integralShiftedVolumeOrder q D.lattice := by
    rw [hC]
    calc
      (n : Int) ≤
          ((integralShiftedVolumeOrder q D.lattice).toNat : Nat) := by
        exact_mod_cast hnat
      _ = integralShiftedVolumeOrder q D.lattice := by
        exact Int.toNat_of_nonneg hDnonneg
  simpa only [integralShiftedVolumeOrder, add_le_add_iff_right] using hshifted

namespace OMaximalMinimalData

/-- Minimal volume excludes every proper integral enlargement. -/
theorem candidate_isOMaximal (D : OMaximalMinimalData q L) :
    IsOMaximal q D.candidate.lattice := by
  refine ⟨D.candidate.integral, ?_⟩
  intro M hle hM
  let C : OMaximalCandidate q L :=
    { lattice := M
      contains := fun x hx => hle (D.candidate.contains hx)
      integral := hM }
  have hvolEq : volumeOrder q D.candidate.lattice = volumeOrder q M :=
    le_antisymm (D.minimal C) (volumeOrder_mono_of_le q hle)
  exact (eq_of_le_of_volumeOrder_eq q D.candidate.lattice M hle hvolEq).symm

end OMaximalMinimalData

/-- An integral lattice whose volume order is minimal among all integral
lattices in the same quadratic space is `O`-maximal.  This is the reusable
volume-minimality argument used in He--Hu, Proposition 3.7. -/
theorem isOMaximal_of_isIntegral_of_volumeOrder_minimal
    (hL : IsIntegral q L)
    (hminimal : ∀ M : Lattice K V, IsIntegral q M →
      volumeOrder q L ≤ volumeOrder q M) :
    IsOMaximal q L := by
  refine ⟨hL, ?_⟩
  intro M hle hM
  have hvolEq : volumeOrder q L = volumeOrder q M :=
    le_antisymm (hminimal M hM) (volumeOrder_mono_of_le q hle)
  exact (eq_of_le_of_volumeOrder_eq q L M hle hvolEq).symm

/-- O'Meara 82:18: every integral lattice is contained in an `O`-maximal
integral lattice over the same quadratic space. -/
theorem exists_oMaximal_superlattice
    (hL : IsIntegral q L) :
    ∃ M : Lattice K V, L ≤ M ∧ IsOMaximal q M := by
  let D := oMaximalMinimalData (q := q) (L := L) hL
  exact ⟨D.candidate.lattice, D.candidate.contains,
    D.candidate_isOMaximal⟩

end Lattice

end Bong
