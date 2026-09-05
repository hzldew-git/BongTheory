/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OMaximal

/-!
# Classic integral quadratic lattices

This file supplies the paper-level meanings used in Zilong He's work on
classic `n`-universal forms.  With the repository convention
`Q(x) = B(x,x)`, a lattice is classic integral precisely when its scale ideal
is contained in the valuation ring.  This is stronger than norm integrality.

The final section proves the classic analogue of the maximal-lattice testing
reduction: a classic integral lattice is classic `n`-universal exactly when it
represents every classic-maximal rank-`n` lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A quadratic lattice is classic integral when every bilinear pairing of
lattice vectors lies in the valuation ring, equivalently `s(L) ⊆ O`. -/
noncomputable def IsClassicIntegral
    (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  IsScaleIntegral q L

theorem isClassicIntegral_iff_scaleIdeal_le
    (q : QuadraticSpace K V) (L : Lattice K V) :
    IsClassicIntegral q L ↔ scaleIdeal q L ≤ unitIdeal (K := K) :=
  Iff.rfl

theorem isClassicIntegral_iff_forall
    (q : QuadraticSpace K V) (L : Lattice K V) :
    IsClassicIntegral q L ↔
      ∀ x y : V, x ∈ L → y ∈ L → Dyadic.IsIntegral K (q.bilin x y) := by
  rw [isClassicIntegral_iff_scaleIdeal_le]
  constructor
  · intro h x y hx hy
    exact mem_unitIdeal_iff_isIntegral.mp
      (h (bilin_mem_scaleIdeal_of_mem q L hx hy))
  · intro h
    rw [scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact mem_unitIdeal_iff_isIntegral.mpr
      (h (p.1 : V) (p.2 : V) p.1.property p.2.property)

/-- Classic integrality implies ordinary (norm) integrality. -/
theorem IsClassicIntegral.isIntegral (h : IsClassicIntegral q L) :
    IsIntegral q L := by
  rw [isIntegral_iff_normIdeal_le]
  exact (normIdeal_le_scaleIdeal q L).trans h

/-- Integral isometries preserve classic integrality. -/
theorem isClassicIntegral_iff_of_latticeIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (f : Isometry q r L M) :
    IsClassicIntegral q L ↔ IsClassicIntegral r M := by
  rw [isClassicIntegral_iff_scaleIdeal_le,
    isClassicIntegral_iff_scaleIdeal_le]
  have hscale : scaleIdeal r M = scaleIdeal q L := by
    rw [← f.map_eq]
    simpa only [Isometry.toQuadraticSpaceIsometry] using
      (scaleIdeal_map_isometry f.toQuadraticSpaceIsometry L)
  rw [hscale]

/-- A classic integral lattice is classic `n`-universal when it represents
every classic integral rank-`n` lattice over the same local field. -/
def IsClassicNUniversal
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  IsClassicIntegral q L ∧
    ∀ {W : Type w} [AddCommGroup W] [Module K W]
      (r : QuadraticSpace K W) (M : Lattice K W),
      finrank K W = n → IsClassicIntegral r M → Represents q r L M

namespace IsClassicNUniversal

theorem isClassicIntegral
    (h : IsClassicNUniversal.{u, v, w} q L n) :
    IsClassicIntegral q L :=
  h.1

theorem isIntegral
    (h : IsClassicNUniversal.{u, v, w} q L n) : IsIntegral q L :=
  h.isClassicIntegral.isIntegral

theorem represents
    (h : IsClassicNUniversal.{u, v, w} q L n)
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hrank : finrank K W = n) (hM : IsClassicIntegral r M) :
    Represents q r L M :=
  h.2 r M hrank hM

end IsClassicNUniversal

/-- Maximality among classic integral lattices in a fixed quadratic space. -/
def IsClassicMaximal (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  IsClassicIntegral q L ∧
    ∀ M : Lattice K V, L ≤ M → IsClassicIntegral q M → M = L

namespace IsClassicMaximal

theorem isClassicIntegral (h : IsClassicMaximal q L) :
    IsClassicIntegral q L :=
  h.1

theorem eq_of_le (h : IsClassicMaximal q L) (M : Lattice K V)
    (hLM : L ≤ M) (hM : IsClassicIntegral q M) : M = L :=
  h.2 M hLM hM

end IsClassicMaximal

/-- Classic integral over-lattices used in the maximality argument. -/
structure ClassicMaximalCandidate
    (q : QuadraticSpace K V) (L : Lattice K V) where
  lattice : Lattice K V
  contains : L ≤ lattice
  classicIntegral : IsClassicIntegral q lattice

namespace ClassicMaximalCandidate

variable (q L)

def initial (hL : IsClassicIntegral q L) : ClassicMaximalCandidate q L where
  lattice := L
  contains := fun _ hx => hx
  classicIntegral := hL

theorem volumeOrder_nonneg (C : ClassicMaximalCandidate q L) :
    0 ≤ volumeOrder q C.lattice :=
  volumeOrder_nonneg_of_scaleIdeal_le_unitIdeal C.classicIntegral

end ClassicMaximalCandidate

/-- A volume-minimal classic integral over-lattice. -/
structure ClassicMaximalMinimalData
    (q : QuadraticSpace K V) (L : Lattice K V) where
  candidate : ClassicMaximalCandidate q L
  minimal : ∀ D : ClassicMaximalCandidate q L,
    volumeOrder q candidate.lattice ≤ volumeOrder q D.lattice

/-- Choose a classic integral over-lattice of smallest volume order. -/
noncomputable def classicMaximalMinimalData
    (hL : IsClassicIntegral q L) : ClassicMaximalMinimalData q L := by
  classical
  let ExistsAt : Nat → Prop := fun n =>
    ∃ C : ClassicMaximalCandidate q L, volumeOrder q C.lattice = (n : Int)
  have hexists : ∃ n, ExistsAt n := by
    let C := ClassicMaximalCandidate.initial q L hL
    refine ⟨(volumeOrder q L).toNat, C, ?_⟩
    dsimp only [C, ClassicMaximalCandidate.initial]
    exact (Int.toNat_of_nonneg
      (ClassicMaximalCandidate.volumeOrder_nonneg q L C)).symm
  let n := Nat.find hexists
  have hn : ExistsAt n := Nat.find_spec hexists
  let C : ClassicMaximalCandidate q L := Classical.choose hn
  have hC : volumeOrder q C.lattice = (n : Int) := Classical.choose_spec hn
  refine ⟨C, ?_⟩
  intro D
  have hDnonneg := D.volumeOrder_nonneg q L
  have hDexists : ExistsAt (volumeOrder q D.lattice).toNat := by
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hDnonneg]
  have hnat : n ≤ (volumeOrder q D.lattice).toNat := by
    simpa only [n] using Nat.find_min' hexists hDexists
  rw [hC]
  calc
    (n : Int) ≤ ((volumeOrder q D.lattice).toNat : Nat) := by
      exact_mod_cast hnat
    _ = volumeOrder q D.lattice := Int.toNat_of_nonneg hDnonneg

namespace ClassicMaximalMinimalData

/-- Minimal volume excludes every proper classic integral enlargement. -/
theorem candidate_isClassicMaximal
    (D : ClassicMaximalMinimalData q L) :
    IsClassicMaximal q D.candidate.lattice := by
  refine ⟨D.candidate.classicIntegral, ?_⟩
  intro M hle hM
  let C : ClassicMaximalCandidate q L :=
    { lattice := M
      contains := fun x hx => hle (D.candidate.contains hx)
      classicIntegral := hM }
  have hvolEq : volumeOrder q D.candidate.lattice = volumeOrder q M :=
    le_antisymm (D.minimal C) (volumeOrder_mono_of_le q hle)
  exact (eq_of_le_of_volumeOrder_eq q D.candidate.lattice M hle hvolEq).symm

end ClassicMaximalMinimalData

/-- Every classic integral lattice lies in a classic-maximal lattice in the
same ambient quadratic space. -/
theorem exists_classicMaximal_superlattice
    (hL : IsClassicIntegral q L) :
    ∃ M : Lattice K V, L ≤ M ∧ IsClassicMaximal q M := by
  let D := classicMaximalMinimalData (q := q) (L := L) hL
  exact ⟨D.candidate.lattice, D.candidate.contains,
    D.candidate_isClassicMaximal⟩

/-- The classic testing family: all classic-maximal rank-`n` lattices. -/
def RepresentsAllClassicMaximalOfRank
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    finrank K W = n → IsClassicMaximal r M → Represents q r L M

/-- A classic integral lattice is classic `n`-universal exactly when it
represents every classic-maximal rank-`n` lattice. -/
theorem isClassicNUniversal_iff_representsAllClassicMaximal
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsClassicNUniversal.{u, v, w} q L n ↔
      IsClassicIntegral q L ∧
        RepresentsAllClassicMaximalOfRank.{u, v, w} q L n := by
  constructor
  · rintro ⟨hintegral, hall⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r M hr hmaximal
    exact hall r M hr hmaximal.isClassicIntegral
  · rintro ⟨hintegral, hmaximal⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r N hr hN
    obtain ⟨M, hNM, hMmaximal⟩ :=
      exists_classicMaximal_superlattice (q := r) (L := N) hN
    exact (hmaximal r M hr hMmaximal).trans (represents_of_le r hNM)

end Lattice

end Bong
