/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009WeightIdealProof
import Bong.Lattice.ScaleTruncationIsometry

/-!
# O'Meara norm groups and weight ideals under isometry

The scalar norm group `gL = Q(L) + 2sL` and O'Meara's weight ideal are
preserved by integral isometry.  Weight invariance is derived from the proved
uniqueness characterization of the weight ideal, so this file introduces no
new local-field law interface.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The scalar norm group `gL = Q(L) + 2sL` is preserved by an ambient
quadratic isometry. -/
theorem normGroupSet_map_isometry
    (f : QuadraticSpace.Isometry q r) (L : Lattice K V) :
    normGroupSet r (map f.toLinearEquiv L) = normGroupSet q L := by
  ext z
  constructor
  · rintro ⟨y, hy, c, hc, hzc⟩
    have hy' : f.toLinearEquiv.symm y ∈ L :=
      (mem_map_iff f.toLinearEquiv L y).1 hy
    have hc' : c ∈ twoScaleIdeal q L := by
      unfold twoScaleIdeal at hc ⊢
      rwa [scaleIdeal_map_isometry f L] at hc
    refine ⟨f.toLinearEquiv.symm y, hy', c, hc', ?_⟩
    calc
      z = r.quadratic y + c := hzc
      _ = r.quadratic
          (f.toLinearEquiv (f.toLinearEquiv.symm y)) + c := by
        rw [f.toLinearEquiv.apply_symm_apply]
      _ = q.quadratic (f.toLinearEquiv.symm y) + c := by
        rw [f.map_quadratic]
  · rintro ⟨x, hx, c, hc, hzc⟩
    have hx' : f.toLinearEquiv x ∈ map f.toLinearEquiv L :=
      (map_mem_map_iff f.toLinearEquiv L x).2 hx
    have hc' : c ∈ twoScaleIdeal r (map f.toLinearEquiv L) := by
      unfold twoScaleIdeal at hc ⊢
      rwa [scaleIdeal_map_isometry f L]
    refine ⟨f.toLinearEquiv x, hx', c, hc', ?_⟩
    rw [f.map_quadratic]
    exact hzc

/-- A scalar norm generator remains a scalar norm generator under an
ambient quadratic isometry. -/
theorem IsNormGeneratorValue.mapIsometry
    {a : Kˣ} (ha : IsNormGeneratorValue q L a)
    (f : QuadraticSpace.Isometry q r) :
    IsNormGeneratorValue r (map f.toLinearEquiv L) a := by
  constructor
  · simpa only [normGroupSet_map_isometry f L] using ha.1
  · rw [normIdeal_map_isometry f L]
    exact ha.2

/-- A scalar norm generator is transported by an integral lattice
isometry. -/
theorem IsNormGeneratorValue.mapLatticeIsometry
    {a : Kˣ} (ha : IsNormGeneratorValue q L a)
    (f : Isometry q r L M) :
    IsNormGeneratorValue r M a := by
  rw [← f.map_eq]
  exact ha.mapIsometry f.toQuadraticSpaceIsometry

/-- O'Meara's weight ideal is preserved by an ambient quadratic isometry.
This is derived from the proved uniqueness characterization of the weight,
not postulated as a new local-field law. -/
theorem weightIdeal_map_isometry
    (f : QuadraticSpace.Isometry q r) (L : Lattice K V)
    (hpos : 0 < Module.finrank K V) :
    weightIdeal r (map f.toLinearEquiv L) = weightIdeal q L := by
  rcases exists_isNormGenerator_of_finrank_pos q L hpos with
    ⟨x, hx, hxa⟩
  let a : Kˣ := Units.mk0 (q.quadratic x) hxa
  have ha : IsNormGeneratorValue q L a := by
    exact hx.isNormGeneratorValue hxa
  have haMap : IsNormGeneratorValue r (map f.toLinearEquiv L) a :=
    ha.mapIsometry f
  let sourceWeight : OrderedFractionalIdeal K :=
    Beli2009WeightIdealData.weight q L
  have hsourceTwo : twoScaleIdeal q L ≤ sourceWeight.carrier :=
    Beli2009WeightIdealData.twoScale_le_weight q L
  have hsource : SatisfiesWeightIdealConditions q L a sourceWeight :=
    (beli2009Lemma210 a ha sourceWeight hsourceTwo).1 rfl
  have htargetTwo :
      twoScaleIdeal r (map f.toLinearEquiv L) ≤ sourceWeight.carrier := by
    unfold twoScaleIdeal
    rw [scaleIdeal_map_isometry f L]
    exact hsourceTwo
  have htarget : SatisfiesWeightIdealConditions
      r (map f.toLinearEquiv L) a sourceWeight := by
    rcases hsource with ⟨hgroup, hbranch⟩
    constructor
    · simpa only [normGroupSet_map_isometry f L] using hgroup
    · rcases hbranch with htwo | hodd
      · left
        unfold twoScaleIdeal at htwo ⊢
        rwa [scaleIdeal_map_isometry f L]
      · exact Or.inr hodd
  have hweight :=
    (beli2009Lemma210 a haMap sourceWeight htargetTwo).2 htarget
  exact hweight.symm

/-- Integral lattice isometries preserve O'Meara's weight ideal. -/
theorem weightIdeal_eq_of_isometry
    (f : Isometry q r L M) (hpos : 0 < Module.finrank K V) :
    weightIdeal r M = weightIdeal q L := by
  rw [← f.map_eq]
  exact weightIdeal_map_isometry f.toQuadraticSpaceIsometry L hpos

/-- Integral lattice isometries preserve the integral order of the weight
ideal. -/
theorem weightIdealOrder_eq_of_isometry
    (f : Isometry q r L M) (hpos : 0 < Module.finrank K V) :
    weightIdealOrder r M = weightIdealOrder q L := by
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  exact weightIdeal_eq_of_isometry f hpos

/-- Integral isometries identify the scalar norm groups of all O'Meara
scale truncations. -/
theorem normGroupSet_scaleTruncation_eq_of_isometry
    (f : Isometry q r L M) (s : Int) :
    normGroupSet r (Lattice.scaleTruncation r M s) =
      normGroupSet q (Lattice.scaleTruncation q L s) := by
  rw [← (f.scaleTruncation s).map_eq]
  exact normGroupSet_map_isometry
    (f.scaleTruncation s).toQuadraticSpaceIsometry
    (Lattice.scaleTruncation q L s)

/-- Integral isometries identify the weight ideals of all O'Meara scale
truncations. -/
theorem weightIdeal_scaleTruncation_eq_of_isometry
    (f : Isometry q r L M) (s : Int)
    (hpos : 0 < Module.finrank K V) :
    weightIdeal r (Lattice.scaleTruncation r M s) =
      weightIdeal q (Lattice.scaleTruncation q L s) :=
  weightIdeal_eq_of_isometry (f.scaleTruncation s) hpos

/-- Integral isometries preserve the integral orders of the weight ideals of
all O'Meara scale truncations. -/
theorem weightIdealOrder_scaleTruncation_eq_of_isometry
    (f : Isometry q r L M) (s : Int)
    (hpos : 0 < Module.finrank K V) :
    weightIdealOrder r (Lattice.scaleTruncation r M s) =
      weightIdealOrder q (Lattice.scaleTruncation q L s) :=
  weightIdealOrder_eq_of_isometry (f.scaleTruncation s) hpos

/-- Being a scalar norm generator of an O'Meara scale truncation is invariant
under integral isometry. -/
theorem isNormGeneratorValue_scaleTruncation_iff_of_isometry
    (f : Isometry q r L M) (s : Int) (a : Kˣ) :
    IsNormGeneratorValue r (Lattice.scaleTruncation r M s) a ↔
      IsNormGeneratorValue q (Lattice.scaleTruncation q L s) a := by
  constructor
  · intro ha
    exact ha.mapLatticeIsometry (f.scaleTruncation s).symm
  · intro ha
    exact ha.mapLatticeIsometry (f.scaleTruncation s)

end Lattice

end Bong
