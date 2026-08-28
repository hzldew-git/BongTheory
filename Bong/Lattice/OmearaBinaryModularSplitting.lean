/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaJordanTree
import Bong.Lattice.OmearaBinaryGeneralPlane
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.OrthogonalProductIsometry

/-!
# A binary modular summand at a common scale

The first step in O'Meara 93:18(ii) is to split a binary modular summand
from a modular lattice of rank at least two.  O'Meara 91C already supplies
a unary-or-binary summand at the ambient scale.  If it is unary, applying
91C once more to its positive-rank complement either supplies a binary
block, or supplies a second unary block; in the latter case the two unary
blocks are grouped together.

This file carries out that two-step construction and transports the
standard product decomposition back to the original lattice.  Both the
binary block and its complement remain modular at the original chosen
scale.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A two-block splitting whose first block has rank two and whose two
blocks are modular at the same chosen scale as the ambient lattice. -/
structure BinaryModularSplittingData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  decomposition : OrthogonalDecomposition q L 2
  first_rank : finrank K (decomposition.component 0).carrier = 2
  first_modular : IsModular
    (decomposition.component 0).space
    (decomposition.component 0).lattice a
  complement_modular : IsModular
    (decomposition.component 1).space
    (decomposition.component 1).lattice a

namespace BinaryModularSplittingData

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- Put the rank-two first summand into O'Meara's general-plane
coordinates. -/
noncomputable def firstGeneralPlane (D : BinaryModularSplittingData q L a) :
    BinaryModularGeneralPlaneData
      (D.decomposition.component 0).space
      (D.decomposition.component 0).lattice a :=
  BinaryModularGeneralPlaneData.ofModular
    (D.decomposition.component 0).space
    (D.decomposition.component 0).lattice a
    D.first_modular D.first_rank

/-- Display the complete splitting as a scaled general O'Meara plane and
an `a`-modular orthogonal complement. -/
noncomputable def generalPlaneDisplayedIsometry
    (D : BinaryModularSplittingData q L a) :
    Isometry q
      (((QuadraticSpace.omearaGeneralPlane
        D.firstGeneralPlane.leftCoefficient
        D.firstGeneralPlane.rightCoefficient
        D.firstGeneralPlane.nondegenerate).rescaleUnit a).orthogonalSum
          (D.decomposition.component 1).space)
      L
      (product (hyperbolicPlaneLattice (K := K))
        (D.decomposition.component 1).lattice) :=
  D.decomposition.pairProductLatticeIsometry.symm |>.trans
    (D.firstGeneralPlane.isometry.orthogonalProductBasic
      (Isometry.refl (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice))

/-- Transport a displayed product with a rank-two first factor back to an
ambient modular lattice. -/
noncomputable def ofDisplayedIsometry
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {X : Type x} [AddCommGroup X] [Module K X]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (p : QuadraticSpace K W) (A : Lattice K W)
    (r : QuadraticSpace K X) (M : Lattice K X)
    (hmodular : IsModular q L a)
    (hfirst : finrank K W = 2)
    (displayed : Isometry q (p.orthogonalSum r) L (product A M)) :
    BinaryModularSplittingData q L a := by
  let T : OrthogonalDecomposition (p.orthogonalSum r) (product A M) 2 :=
    orthogonalProductDecomposition p r A M
  let pulled : OrthogonalDecomposition q L 2 :=
    T.mapIsometry displayed.symm
  let standardToLeft : Isometry p (T.component 0).space A
      (T.component 0).lattice :=
    orthogonalProductLeftComponentIsometry p r A
  let leftToPulled := (T.component 0).mapLatticeIsometry displayed.symm
  have hrank : finrank K (pulled.component 0).carrier = 2 := by
    have h := (standardToLeft.trans leftToPulled).toLinearEquiv.finrank_eq
    change finrank K ((T.component 0).mapIsometry displayed.symm).carrier = 2
    simpa only [hfirst] using h.symm
  exact
    { decomposition := pulled
      first_rank := hrank
      first_modular := pulled.component_modular_of_ambient hmodular 0
      complement_modular := pulled.component_modular_of_ambient hmodular 1 }

end BinaryModularSplittingData

/-- Choose the O'Meara 91C minimal-scale component of a positive-rank
lattice. -/
noncomputable def chosenMinimalScaleComponent
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hpos : 0 < finrank K V) : MinimalScaleComponentData q L := by
  letI : Module.Finite K V := L.moduleFinite
  let hexists := exists_isScaleGenerator_of_finrank_pos q L hpos
  let x := Classical.choose hexists
  let y := Classical.choose (Classical.choose_spec hexists)
  have hgenerator : IsScaleGenerator q L x y :=
    (Classical.choose_spec (Classical.choose_spec hexists)).1
  have hxy : q.bilin x y ≠ 0 :=
    (Classical.choose_spec (Classical.choose_spec hexists)).2
  exact minimalScaleComponentDataOfScaleGenerator hgenerator hxy

/-- Every modular lattice of rank at least two has a binary modular direct
summand, and the orthogonal complement is modular at the same scale. -/
noncomputable def binaryModularSplittingData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a)
    (hrank : 2 ≤ finrank K V) : BinaryModularSplittingData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let D₁ := chosenMinimalScaleComponent q L (by omega)
  let S₁ := D₁.canonicalSplitting
  let H₁ := S₁.component 0
  let C := S₁.component 1
  letI : Module.Finite K H₁.carrier := H₁.lattice.moduleFinite
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  by_cases hD₁ : finrank K D₁.component.carrier = 1
  · have hH₁ : finrank K H₁.carrier = 1 := by
      rw [show H₁ = D₁.component by rfl]
      exact hD₁
    have htotal₁ := S₁.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
    have hCpos : 0 < finrank K C.carrier := by
      change finrank K (H₁.carrier × C.carrier) = finrank K V at htotal₁
      rw [Module.finrank_prod, hH₁] at htotal₁
      omega
    have hCmodular : IsModular C.space C.lattice a :=
      S₁.component_modular_of_ambient hmodular 1
    let D₂ := chosenMinimalScaleComponent C.space C.lattice hCpos
    let S₂ := D₂.canonicalSplitting
    let H₂ := S₂.component 0
    let R := S₂.component 1
    letI : Module.Finite K H₂.carrier := H₂.lattice.moduleFinite
    letI : Module.Finite K R.carrier := R.lattice.moduleFinite
    let expose₁ : Isometry q (H₁.space.orthogonalSum C.space) L
        (product H₁.lattice C.lattice) :=
      S₁.pairProductLatticeIsometry.symm
    let expose₂ : Isometry C.space (H₂.space.orthogonalSum R.space)
        C.lattice (product H₂.lattice R.lattice) :=
      S₂.pairProductLatticeIsometry.symm
    let nested : Isometry q
        (H₁.space.orthogonalSum (H₂.space.orthogonalSum R.space)) L
        (product H₁.lattice (product H₂.lattice R.lattice)) :=
      expose₁.trans
        ((Isometry.refl H₁.space H₁.lattice).orthogonalProductBasic expose₂)
    by_cases hD₂ : finrank K D₂.component.carrier = 1
    · have hH₂ : finrank K H₂.carrier = 1 := by
        rw [show H₂ = D₂.component by rfl]
        exact hD₂
      let regroup : Isometry
          (H₁.space.orthogonalSum (H₂.space.orthogonalSum R.space))
          ((H₁.space.orthogonalSum H₂.space).orthogonalSum R.space)
          (product H₁.lattice (product H₂.lattice R.lattice))
          (product (product H₁.lattice H₂.lattice) R.lattice) :=
        orthogonalProductAssoc.symm
      let displayed := nested.trans regroup
      have hfirst : finrank K (H₁.carrier × H₂.carrier) = 2 := by
        rw [Module.finrank_prod, hH₁, hH₂]
      exact BinaryModularSplittingData.ofDisplayedIsometry
        q L a (H₁.space.orthogonalSum H₂.space)
        (product H₁.lattice H₂.lattice) R.space R.lattice
        hmodular hfirst displayed
    · have hD₂two : finrank K D₂.component.carrier = 2 :=
        D₂.rank_one_or_two.resolve_left hD₂
      have hH₂ : finrank K H₂.carrier = 2 := by
        rw [show H₂ = D₂.component by rfl]
        exact hD₂two
      let rotate : Isometry
          (H₁.space.orthogonalSum (H₂.space.orthogonalSum R.space))
          ((H₂.space.orthogonalSum H₁.space).orthogonalSum R.space)
          (product H₁.lattice (product H₂.lattice R.lattice))
          (product (product H₂.lattice H₁.lattice) R.lattice) :=
        orthogonalProductRotateLeft
      let regroup : Isometry
          ((H₂.space.orthogonalSum H₁.space).orthogonalSum R.space)
          (H₂.space.orthogonalSum (H₁.space.orthogonalSum R.space))
          (product (product H₂.lattice H₁.lattice) R.lattice)
          (product H₂.lattice (product H₁.lattice R.lattice)) :=
        orthogonalProductAssoc
      let displayed := nested.trans (rotate.trans regroup)
      exact BinaryModularSplittingData.ofDisplayedIsometry
        q L a H₂.space H₂.lattice
        (H₁.space.orthogonalSum R.space)
        (product H₁.lattice R.lattice)
        hmodular hH₂ displayed
  · have hD₁two : finrank K D₁.component.carrier = 2 :=
      D₁.rank_one_or_two.resolve_left hD₁
    have hH₁ : finrank K H₁.carrier = 2 := by
      rw [show H₁ = D₁.component by rfl]
      exact hD₁two
    exact
      { decomposition := S₁
        first_rank := hH₁
        first_modular := S₁.component_modular_of_ambient hmodular 0
        complement_modular := S₁.component_modular_of_ambient hmodular 1 }

end Lattice

end Bong
