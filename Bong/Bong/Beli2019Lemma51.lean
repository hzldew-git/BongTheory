/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma51Component

/-!
# Beli (2019), Lemma 5.1

This file assembles the preceding constructive modules into the exact
unary-or-binary common-complement datum used throughout Section 5.  For an
index-`\mathfrak p` inclusion `N ≤ M`, the two lattices split as `J ⊥ K` and
`J' ⊥ K`; the selected blocks have common rank one or two, both are modular,
and `J ≤ J'` with `πJ' ≤ J`.  The volume-order difference records
`[J' : J] = \mathfrak p` without introducing a separate ideal-index API.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

variable {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The complete common-complement output of Beli (2019), Lemma 5.1. -/
structure Beli2019Lemma51Data
    (q : QuadraticSpace K V) (M N : Lattice K V) : Type (max u v) where
  /-- The adapted primitive vector and the selected block. -/
  input : Beli2019Lemma51InputData q M N
  /-- The selected block has rank one or two. -/
  rank_one_or_two :
    finrank K input.block.component.carrier = 1 ∨
      finrank K input.block.component.carrier = 2
  /-- The smaller selected block is modular. -/
  small_modular : IsModular input.block.component.space
    input.block.component.lattice input.block.scaleGenerator
  /-- The enlarged selected block is modular. -/
  large_modular : IsModular input.enlargedComponent.space
    input.enlargedComponent.lattice input.block.enlargedScaleGenerator
  /-- The selected block of `N` is contained in the selected block of `M`. -/
  small_le_large :
    input.block.component.lattice ≤ input.enlargedComponent.lattice
  /-- Multiplication by a uniformizer sends the enlarged block into the
  smaller block. -/
  uniformizer_large_le_small :
    rescale (uniformizerUnit K) input.enlargedComponent.lattice ≤
      input.block.component.lattice
  /-- Enlarging the selected block lowers its volume order by two. -/
  volumeOrder_eq :
    volumeOrder input.enlargedComponent.space
        input.enlargedComponent.lattice =
      volumeOrder input.block.component.space
        input.block.component.lattice - 2
  /-- The second components in the two splittings are literally identical. -/
  common_complement :
    input.largeSplitting.component 1 = input.smallSplitting.component 1

/-- Every literal index-`\mathfrak p` inclusion has the complete data of
Beli (2019), Lemma 5.1. -/
noncomputable def beli2019Lemma51Data
    (q : QuadraticSpace K V) (M N : Lattice K V)
    (inclusion : Beli2019IndexPInclusion q M N) :
    Beli2019Lemma51Data q M N := by
  let D := beli2019Lemma51InputData q M N inclusion
  exact {
    input := D
    rank_one_or_two := D.block.component_rank_one_or_two
    small_modular := D.block.component_modular
    large_modular := D.enlargedComponent_isModular
    small_le_large := D.component_lattice_le_enlargedComponent
    uniformizer_large_le_small :=
      D.rescale_uniformizer_enlargedComponent_le
    volumeOrder_eq := D.block.volumeOrder_enlargedLattice
    common_complement := D.largeSplitting_component_one
  }

namespace Beli2019Lemma51Data

/-- The smaller lattice is the orthogonal sum of the selected block and the
common complement. -/
theorem small_sum_eq (D : Beli2019Lemma51Data q M N) :
    (⨆ i, (D.input.smallSplitting.component i).ambientSubmodule) =
      N.toSubmodule :=
  D.input.smallSplitting.sum_eq

/-- The larger lattice is the orthogonal sum of the enlarged block and the
same common complement. -/
theorem large_sum_eq (D : Beli2019Lemma51Data q M N) :
    (⨆ i, (D.input.largeSplitting.component i).ambientSubmodule) =
      M.toSubmodule :=
  D.input.largeSplitting.sum_eq

end Beli2019Lemma51Data

end Lattice

end Bong
