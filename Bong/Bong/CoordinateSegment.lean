/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basis

/-!
# Coordinate subspaces of consecutive BONG vectors

Every consecutive family of ambient BONG vectors spans a nondegenerate
quadratic subspace.  This is the linear-algebraic component of Beli (2003),
Corollary 2.8.
-/

namespace Bong

open Dyadic
open Module

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The original BONG index represented by an index in a consecutive block. -/
def segmentIndex (start length : Nat) (bound : start + length ≤ n)
    (i : Fin length) : Fin n :=
  ⟨start + i.1, by omega⟩

@[simp]
theorem segmentIndex_val (start length : Nat)
    (bound : start + length ≤ n) (i : Fin length) :
    (segmentIndex (n := n) start length bound i).1 = start + i.1 :=
  rfl

/-- The consecutive family of ambient BONG vectors. -/
noncomputable def segmentVector (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Fin length → V :=
  fun i => b.ambientVector (segmentIndex start length bound i)

/-- Distinct segment indices remain distinct in the original BONG. -/
theorem segmentIndex_injective (start length : Nat)
    (bound : start + length ≤ n) :
    Function.Injective (segmentIndex (n := n) start length bound) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simpa using Nat.add_left_cancel this

/-- A consecutive family of BONG vectors is linearly independent. -/
theorem segmentVector_linearIndependent (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    LinearIndependent K (b.segmentVector start length bound) :=
  b.ambientVector_linearIndependent.comp _
    (segmentIndex_injective start length bound)

/-- The coordinate subspace spanned by a consecutive BONG block. -/
noncomputable def segmentCarrier (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Submodule K V :=
  Submodule.span K (Set.range (b.segmentVector start length bound))

/-- The segment vectors form their canonical basis in the coordinate space. -/
noncomputable def segmentBasis (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Basis (Fin length) K (b.segmentCarrier start length bound) :=
  Basis.span (b.segmentVector_linearIndependent start length bound)

@[simp]
theorem segmentBasis_coe (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n)
    (i : Fin length) :
    (b.segmentBasis start length bound i : V) =
      b.segmentVector start length bound i := by
  unfold segmentBasis segmentCarrier
  exact Basis.coe_span_apply
    (b.segmentVector_linearIndependent start length bound) i

/-- The canonical segment basis is orthogonal for the restricted form. -/
theorem segmentBasis_iIsOrtho (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    (q.bilin.restrict (b.segmentCarrier start length bound)).iIsOrtho
      (b.segmentBasis start length bound) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  change q.bilin (b.segmentBasis start length bound i : V)
      (b.segmentBasis start length bound j : V) = 0
  rw [segmentBasis_coe, segmentBasis_coe]
  apply (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
  intro hindex
  apply hij
  exact segmentIndex_injective start length bound hindex

/-- Every vector of the segment basis has nonzero quadratic value. -/
theorem segmentBasis_self_ne_zero (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n)
    (i : Fin length) :
    (q.bilin.restrict (b.segmentCarrier start length bound))
        (b.segmentBasis start length bound i)
        (b.segmentBasis start length bound i) ≠ 0 := by
  change q.quadratic (b.segmentBasis start length bound i : V) ≠ 0
  rw [segmentBasis_coe]
  rw [segmentVector, b.quadratic_ambientVector]
  exact b.value_ne_zero (segmentIndex start length bound i)

/-- A consecutive BONG coordinate subspace is nondegenerate. -/
theorem segmentCarrier_nondegenerate (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    (q.bilin.restrict
      (b.segmentCarrier start length bound)).Nondegenerate := by
  apply ((b.segmentBasis_iIsOrtho start length bound).nondegenerate_iff_not_isOrtho_basis_self
    (q.bilin.restrict (b.segmentCarrier start length bound))
    (b.segmentBasis start length bound)).2
  exact b.segmentBasis_self_ne_zero start length bound

/-- The dimension of a segment coordinate space is its block length. -/
theorem finrank_segmentCarrier (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n) :
    Module.finrank K (b.segmentCarrier start length bound) = length := by
  letI := (b.segmentBasis start length bound).finiteDimensional_of_finite
  rw [finrank_eq_card_basis (b.segmentBasis start length bound)]
  simp

/-- Quadratic values on the canonical segment basis are the selected values. -/
@[simp]
theorem quadratic_segmentBasis (b : BONG V q L n)
    (start length : Nat) (bound : start + length ≤ n)
    (i : Fin length) :
    (q.restrict (b.segmentCarrier start length bound)
      (b.segmentCarrier_nondegenerate start length bound)).quadratic
        (b.segmentBasis start length bound i) =
      b.value (segmentIndex start length bound i) := by
  change q.quadratic (b.segmentBasis start length bound i : V) = _
  rw [segmentBasis_coe, segmentVector, b.quadratic_ambientVector]

end BONG

end Bong
