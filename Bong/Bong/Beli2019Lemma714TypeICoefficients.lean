/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714RescaledBinary
import Bong.Bong.GoodExistence

/-!
# Beli (2019), Lemma 7.14(ii.1): the complete replacement coefficients

In zero-based indexing the type-I coefficient sequence is

`x₃, ..., x_s, πx₁, πx₂, x_(s+1), ..., x_N`

at the vector level, hence

`a₃, ..., a_s, π²a₁, π²a₂, a_(s+1), ..., a_N`

at the quadratic-value level.  The definition below also covers the boundary
`s = 2`, when the first interval is empty.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

@[simp]
theorem lemma714TypeI_valueUnit_castLength
    {m length : Nat} {form : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG form M m) (h : m = length) (i : Fin length) :
    (a.castLength h).valueUnit i = a.valueUnit ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- The full coefficient list in the type-I branch of Lemma 7.14. -/
noncomputable def lemma714TypeITargetValues
    (b : GoodBONG q L (n + 3)) (s : Nat) (hsTwo : 2 ≤ s)
    (hsRank : s ≤ n + 3) :
    Fin (n + 3) → Kˣ := fun i =>
  if hprefix : i.val < s - 2 then
    b.valueUnit ⟨i.val + 2, by omega⟩
  else if hzero : i.val = s - 2 then
    uniformizerUnit K ^ 2 * b.valueUnit 0
  else if hone : i.val = s - 1 then
    uniformizerUnit K ^ 2 * b.valueUnit 1
  else
    b.valueUnit i

@[simp]
theorem lemma714TypeITargetValues_prefix
    (b : GoodBONG q L (n + 3)) (s : Nat) (hsTwo : 2 ≤ s)
    (hsRank : s ≤ n + 3)
    (i : Fin (n + 3)) (hi : i.val < s - 2) :
    lemma714TypeITargetValues b s hsTwo hsRank i =
      b.valueUnit ⟨i.val + 2, by omega⟩ := by
  simp [lemma714TypeITargetValues, hi]

@[simp]
theorem lemma714TypeITargetValues_zero
    (b : GoodBONG q L (n + 3)) (s : Nat) (hsTwo : 2 ≤ s)
    (hsRank : s ≤ n + 3) :
    lemma714TypeITargetValues b s hsTwo hsRank ⟨s - 2, by omega⟩ =
      uniformizerUnit K ^ 2 * b.valueUnit 0 := by
  simp [lemma714TypeITargetValues]

@[simp]
theorem lemma714TypeITargetValues_one
    (b : GoodBONG q L (n + 3)) (s : Nat) (hsTwo : 2 ≤ s)
    (hsRank : s ≤ n + 3) :
    lemma714TypeITargetValues b s hsTwo hsRank ⟨s - 1, by omega⟩ =
      uniformizerUnit K ^ 2 * b.valueUnit 1 := by
  have hnotPrefix : ¬s - 1 < s - 2 := by omega
  have hnotZero : s - 1 ≠ s - 2 := by omega
  simp [lemma714TypeITargetValues, hnotPrefix, hnotZero]

@[simp]
theorem lemma714TypeITargetValues_suffix
    (b : GoodBONG q L (n + 3)) (s : Nat) (hsTwo : 2 ≤ s)
    (hsRank : s ≤ n + 3)
    (i : Fin (n + 3)) (hi : s ≤ i.val) :
    lemma714TypeITargetValues b s hsTwo hsRank i = b.valueUnit i := by
  have hnotPrefix : ¬i.val < s - 2 := by omega
  have hnotZero : i.val ≠ s - 2 := by omega
  have hnotOne : i.val ≠ s - 1 := by omega
  simp [lemma714TypeITargetValues, hnotPrefix, hnotZero, hnotOne]

end BONG.GoodBONG

end Bong
