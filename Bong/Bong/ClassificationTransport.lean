/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Bong.GoodMap
import Bong.Lattice.ProjectionScaling

/-!
# Transport reduction for good-BONG classification

The classification conditions depend only on the quadratic values of the two
good BONGs.  This file proves their invariance under ambient isometry and
reduces the universe-polymorphic, two-carrier classification theorem to its
mathematical core: two lattices inside one quadratic space.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

@[simp]
theorem adjacentProduct_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (j : Fin n) :
    (b.map f).adjacentProduct j = b.adjacentProduct j := by
  unfold adjacentProduct
  rw [valueUnit_map, valueUnit_map]

@[simp]
theorem adjacentDefect_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (j : Fin n) :
    (b.map f).adjacentDefect j = b.adjacentDefect j := by
  simp [adjacentDefect]

@[simp]
theorem halfGapCandidate_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.map f).halfGapCandidate i = b.halfGapCandidate i := by
  simp [halfGapCandidate]

@[simp]
theorem leftDefectCandidate_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i j : Fin n) :
    (b.map f).leftDefectCandidate i j = b.leftDefectCandidate i j := by
  simp [leftDefectCandidate]

@[simp]
theorem rightDefectCandidate_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i j : Fin n) :
    (b.map f).rightDefectCandidate i j = b.rightDefectCandidate i j := by
  simp [rightDefectCandidate]

@[simp]
theorem alphaCandidates_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.map f).alphaCandidates i = b.alphaCandidates i := by
  have hleft : (b.map f).leftDefectCandidate i =
      b.leftDefectCandidate i := by
    funext j
    exact leftDefectCandidate_map f b i j
  have hright : (b.map f).rightDefectCandidate i =
      b.rightDefectCandidate i := by
    funext j
    exact rightDefectCandidate_map f b i j
  simp [alphaCandidates, hleft, hright]

@[simp]
theorem alpha_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.map f).alpha i = b.alpha i := by
  simp [alpha]

@[simp]
theorem alphaValue_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.map f).alphaValue i = b.alphaValue i := by
  apply WithTop.coe_injective
  simp

@[simp]
theorem prefixProduct_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L n) (i : Nat) :
    (b.map f).prefixProduct i = b.prefixProduct i := by
  unfold GoodBONG.prefixProduct BONG.prefixProduct
  apply Finset.prod_congr rfl
  intro j _
  exact valueUnit_map f b j

@[simp]
theorem prefixValues_map (f : QuadraticSpace.Isometry q r)
    (b : GoodBONG q L n) (m : Nat) (hm : m ≤ n) :
    (b.map f).prefixValues m hm = b.prefixValues m hm := by
  funext i
  exact BONG.value_map f b.toBONG ⟨i.1, i.2.trans_le hm⟩

end BONG.GoodBONG

theorem classificationConditions_map_right_iff
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (f : QuadraticSpace.Isometry r q)
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) :
    ClassificationConditions a (b.map f) ↔ ClassificationConditions a b := by
  constructor
  · rintro ⟨hord, halpha, hdefect, hrep⟩
    exact ⟨by simpa [BONG.GoodBONG.SameOrders] using hord,
      by simpa [BONG.GoodBONG.SameAlphas] using halpha,
      by simpa [BONG.GoodBONG.PrefixDefectBounds,
        BONG.GoodBONG.comparisonPrefixProduct] using hdefect,
      by simpa [BONG.GoodBONG.InternalRepresentationConditions] using hrep⟩
  · rintro ⟨hord, halpha, hdefect, hrep⟩
    exact ⟨by simpa [BONG.GoodBONG.SameOrders] using hord,
      by simpa [BONG.GoodBONG.SameAlphas] using halpha,
      by simpa [BONG.GoodBONG.PrefixDefectBounds,
        BONG.GoodBONG.comparisonPrefixProduct] using hdefect,
      by simpa [BONG.GoodBONG.InternalRepresentationConditions] using hrep⟩

/-- Same-ambient-space core of Beli's classification theorem. -/
class GoodBONGSameSpaceClassificationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  classify
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V}
    {L M : Lattice K V} {n : Nat}
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG q M (n + 1)) :
    Lattice.IsIsometric q q L M ↔ ClassificationConditions a b

noncomputable instance goodBONGClassificationLawsOfSameSpace
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [GoodBONGSameSpaceClassificationLaws.{u, v} K] :
    GoodBONGClassificationLaws.{u, v, w} K where
  classify := by
    intro V _ _ W _ _ q r L M n ambient a b
    rcases ambient with ⟨f⟩
    let back : BONG.GoodBONG q (Lattice.map f.symm.toLinearEquiv M) (n + 1) :=
      b.map f.symm
    have hclass := GoodBONGSameSpaceClassificationLaws.classify
      (K := K) a back
    have htransport :
        Lattice.IsIsometric q r L M ↔
          Lattice.IsIsometric q q L (Lattice.map f.symm.toLinearEquiv M) := by
      constructor
      · rintro ⟨g⟩
        exact ⟨g.trans (Lattice.Isometry.toMap r f.symm M)⟩
      · rintro ⟨g⟩
        exact ⟨g.trans (Lattice.Isometry.toMap r f.symm M).symm⟩
    rw [htransport, hclass]
    exact classificationConditions_map_right_iff f.symm a b

end Bong
