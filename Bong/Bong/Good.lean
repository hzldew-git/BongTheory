/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Binary
import Lean.Elab.Tactic.Omega

/-!
# Good BONGs

A BONG with orders `R_i` is good when `R_i ≤ R_{i+2}` whenever both sides are
defined.  We also formalize Beli's equivalent formulation: the adjacent sums
`R_i + R_{i+1}` form an increasing sequence.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Beli's condition `R_i ≤ R_{i+2}` for a good BONG. -/
def IsGood (b : BONG V q L n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 2 < n), b.order i ≤ b.order ⟨i.1 + 2, hi⟩

/-- The equivalent condition that adjacent order sums are increasing. -/
def AdjacentSumsIncreasing (b : BONG V q L n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 2 < n),
    b.order i + b.order ⟨i.1 + 1, by omega⟩ ≤ b.order ⟨i.1 + 1, by omega⟩ +
      b.order ⟨i.1 + 2, hi⟩

theorem isGood_iff_adjacentSumsIncreasing (b : BONG V q L n) :
    b.IsGood ↔ b.AdjacentSumsIncreasing := by
  constructor
  · intro h i hi
    have h' := h i hi
    omega
  · intro h i hi
    have h' := h i hi
    omega

/-- Every BONG of length at most two is automatically good. -/
theorem isGood_of_length_le_two (b : BONG V q L n) (hn : n ≤ 2) : b.IsGood := by
  intro i hi
  omega

@[simp]
theorem isGood_binary (b : BONG V q L 2) : b.IsGood :=
  b.isGood_of_length_le_two (by omega)

theorem isGood_ternary_iff (b : BONG V q L 3) :
    b.IsGood ↔ b.order 0 ≤ b.order 2 := by
  constructor
  · intro h
    exact h 0 (by omega)
  · intro h i hi
    have hi0 : i = 0 := by
      apply Fin.ext
      omega
    subst i
    simpa using h

/-- Removing the first vector of a good BONG leaves a good BONG. -/
theorem IsGood.tail {b : BONG V q L (n + 1)} (hb : b.IsGood) : b.tail.IsGood := by
  intro i hi
  have hi' : i.succ.1 + 2 < n + 1 := by
    simp only [Fin.val_succ]
    omega
  have h := hb i.succ hi'
  have hind :
      (⟨i.1 + 2, hi⟩ : Fin n).succ =
        (⟨i.succ.1 + 2, hi'⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
  rw [order_tail, order_tail, hind]
  exact h

/-- A BONG together with the proof that its order sequence is good. -/
structure GoodBONG (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) where
  toBONG : BONG V q L n
  good : toBONG.IsGood

namespace GoodBONG

instance : Coe (GoodBONG q L n) (BONG V q L n) :=
  ⟨GoodBONG.toBONG⟩

/-- The quadratic values of a good BONG. -/
noncomputable def value (b : GoodBONG q L n) (i : Fin n) : K :=
  b.toBONG.value i

/-- The nonzero quadratic values of a good BONG. -/
noncomputable def valueUnit (b : GoodBONG q L n) (i : Fin n) : Kˣ :=
  b.toBONG.valueUnit i

/-- The orders of a good BONG. -/
noncomputable def order (b : GoodBONG q L n) (i : Fin n) : Int :=
  b.toBONG.order i

@[simp]
theorem coe_valueUnit (b : GoodBONG q L n) (i : Fin n) :
    (b.valueUnit i : K) = b.value i :=
  rfl

/-- The tail of a nonempty good BONG, in the projected orthogonal complement. -/
noncomputable def tail (b : GoodBONG q L (n + 1)) :
    GoodBONG (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (L.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic) n where
  toBONG := b.toBONG.tail
  good := b.good.tail

end GoodBONG

end BONG

end Bong
