/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.PairedHyperbolicRepresentation

/-!
# Transporting representations across orthogonal complements

If two total orthogonal sums are isometric and the second source summand is
represented by the second target summand with an auxiliary space adjoined,
then the first target summand is represented by the first source summand with
the same auxiliary space.  This is the representation form of the Witt
cancellation maneuver used in the necessity proof of O'Meara 93:28.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w x y z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {P : Type v} [AddCommGroup P] [Module K P]
  {S : Type w} [AddCommGroup S] [Module K S]
  {P' : Type x} [AddCommGroup P'] [Module K P']
  {S' : Type y} [AddCommGroup S'] [Module K S']
  {A : Type z} [AddCommGroup A] [Module K A]
  {p : QuadraticSpace K P} {s : QuadraticSpace K S}
  {p' : QuadraticSpace K P'} {s' : QuadraticSpace K S'}
  {a : QuadraticSpace K A}

/-- Exchange two factors of an orthogonal sum. -/
noncomputable def orthogonalSumSwap
    (q : QuadraticSpace K P) (r : QuadraticSpace K S) :
    Isometry (q.orthogonalSum r) (r.orthogonalSum q) where
  toLinearEquiv := LinearEquiv.prodComm K P S
  map_bilin := by
    intro x y
    simp only [orthogonalSum_bilin_apply, LinearEquiv.prodComm_apply]
    exact add_comm _ _

/-- Rotate three orthogonal factors from `p ⊥ (s ⊥ a)` to
`s ⊥ (p ⊥ a)`. -/
noncomputable def orthogonalSumRotateLeft
    (p : QuadraticSpace K P) (s : QuadraticSpace K S)
    (a : QuadraticSpace K A) :
    Isometry (p.orthogonalSum (s.orthogonalSum a))
      (s.orthogonalSum (p.orthogonalSum a)) where
  toLinearEquiv :=
    { toFun := fun x ↦ (x.2.1, (x.1, x.2.2))
      invFun := fun x ↦ (x.2.1, (x.1, x.2.2))
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  map_bilin := by
    intro x y
    change s.bilin x.2.1 y.2.1 +
        (p.bilin x.1 y.1 + a.bilin x.2.2 y.2.2) =
      p.bilin x.1 y.1 +
        (s.bilin x.2.1 y.2.1 + a.bilin x.2.2 y.2.2)
    ring

/-- Complementary-summand transport for a quadratic-space representation.

From `p ⊥ s ≃ p' ⊥ s'` and an embedding
`s' → s ⊥ a`, one obtains an embedding `p → p' ⊥ a` by
adjoining the untouched summand and cancelling the common copy of `s`. -/
theorem embedsInto_first_of_embedsInto_second
    [FiniteDimensional K P] [FiniteDimensional K S]
    [FiniteDimensional K P'] [FiniteDimensional K S']
    [FiniteDimensional K A]
    (total : Isometry (p.orthogonalSum s) (p'.orthogonalSum s'))
    (second : EmbedsInto s' (s.orthogonalSum a)) :
    EmbedsInto p (p'.orthogonalSum a) := by
  rcases second with ⟨f⟩
  let lifted : Representation (p'.orthogonalSum s')
      (p'.orthogonalSum (s.orthogonalSum a)) :=
    (Representation.refl p').orthogonalSum f
  let assembled : Representation (p.orthogonalSum s)
      (s.orthogonalSum (p'.orthogonalSum a)) :=
    (orthogonalSumRotateLeft p' s a).toRepresentation.trans
      (lifted.trans total.toRepresentation)
  have rotated :
      (s.orthogonalSum (p'.orthogonalSum a)).Represents
        (s.orthogonalSum p) :=
    ⟨assembled.trans (orthogonalSumSwap s p).toRepresentation⟩
  exact orthogonalSumLeftCancelRepresents s p (p'.orthogonalSum a) rotated

end QuadraticSpace

end Bong
