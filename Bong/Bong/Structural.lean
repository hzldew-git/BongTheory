/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Prefix
import Bong.Bong.Dual
import Bong.Bong.SectionTwo
import Bong.Bong.Existence
import Bong.Lattice.Jordan

/-!
# Structural laws for BONGs

This file separates the elementary linear algebra already proved in M6 from
the deeper integral assertions in Beli (2003), Sections 2 and 4.  The latter
are exposed through `BONGStructuralLaws`; no global axiom or default instance
is introduced.

The reverse dual vectors are defined concretely and their quadratic values are
proved here.  Consecutive-segment realization is now constructive in
`Bong.Bong.Prefix`.  The remaining laws interface records good-BONG existence,
the reverse-dual good-BONG theorem, and the Jordan coordinate criterion.
Reconstruction and the refined determinant formula are unconditional in
`Bong.Bong.SectionTwo`.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The remaining arbitrary-rank existence theorem for good BONGs. -/
class BONGGoodExistenceLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_good_bong
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Nonempty (BONG.GoodBONG q L (finrank K V))

/-- The arbitrary-rank integral reverse-duality theorem of Beli (2003),
Lemma 4.8.  Its vector formula is already concrete in `Bong.Bong.Dual`; this
minimal interface contains only realization as a good BONG of the dual
lattice. -/
class BONGReverseDualLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  reverse_dual_good
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG.GoodBONG q L n) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) n,
      ∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i

/-- The remaining Jordan-coordinate characterization of property A. -/
class BONGJordanCoordinateLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  propertyA_coordinates
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) :
    Lattice.HasJordanPropertyA q L ↔ b.HasPropertyA

/-- Compatibility package retaining the original three structural inputs.
New developments should request the smallest parent class they actually use. -/
class BONGStructuralLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop
    extends BONGGoodExistenceLaws.{u, v} K,
      BONGReverseDualLaws.{u, v} K,
      BONGJordanCoordinateLaws.{u, v} K

/-- A lattice is uniquely determined by the vectors of one of its BONGs. -/
theorem BONG.lattice_eq_of_ambientVector_eq {M : Lattice K V}
    (b : BONG V q L n) (c : BONG V q M n)
    (vectors : ∀ i, b.ambientVector i = c.ambientVector i) : L = M :=
  b.lattice_eq_of_ambientVector_eq_from_projection c vectors

/-- Beli's refined determinant formula, now unconditional. -/
theorem Lattice.determinantClass_eq_bongValueProduct (b : BONG V q L n) :
    Lattice.determinantClass q L = unitSquareClass K b.valueProduct :=
  b.determinantClass_eq_valueProduct

/-- Every lattice admits a BONG of its ambient dimension. -/
theorem exists_bong (q : QuadraticSpace K V) (L : Lattice K V) :
    Nonempty (BONG V q L (finrank K V)) :=
  BONG.exists_ofLattice q L

/-- Every consecutive block of BONG vectors has its own BONG realization. -/
theorem BONG.exists_segmentWitness (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Nonempty (BONG.SegmentWitness b start length bound) :=
  b.exists_segmentWitness_unconditional start length bound

section GoodExistence

variable [BONGGoodExistenceLaws.{u, v} K]

/-- Every lattice admits a good BONG of its ambient dimension. -/
theorem exists_good_bong (q : QuadraticSpace K V) (L : Lattice K V) :
    Nonempty (BONG.GoodBONG q L (finrank K V)) :=
  BONGGoodExistenceLaws.exists_good_bong q L

end GoodExistence

section ReverseDual

variable [BONGReverseDualLaws.{u, v} K]

/-- The reversed dual vectors realize a good BONG of the dual lattice. -/
theorem BONG.GoodBONG.exists_reverseDual (b : BONG.GoodBONG q L n) :
    ∃ c : BONG.GoodBONG q (Lattice.dualLattice q L) n,
      ∀ i, c.toBONG.ambientVector i = b.toBONG.reverseDualVector i :=
  BONGReverseDualLaws.reverse_dual_good b

end ReverseDual

section JordanCoordinates

variable [BONGJordanCoordinateLaws.{u, v} K]

/-- Jordan property A is the strict two-step BONG order condition. -/
theorem Lattice.hasJordanPropertyA_iff_bongHasPropertyA
    (b : BONG V q L n) :
    Lattice.HasJordanPropertyA q L ↔ b.HasPropertyA :=
  BONGJordanCoordinateLaws.propertyA_coordinates b

end JordanCoordinates

end Bong
