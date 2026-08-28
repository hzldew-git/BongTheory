/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Good
import Mathlib.Data.Finset.Max

/-!
# Invariants of a good BONG

This file formalizes Definition 1 of Beli (2009).  For a good BONG with values
`a_i` and orders `R_i`, the invariant `α_i` is the minimum of

* `(R_{i+1} - R_i) / 2 + e`;
* `R_{i+1} - R_j + d(-a_j a_{j+1})` for `j ≤ i`;
* `R_{j+1} - R_i + d(-a_j a_{j+1})` for `i ≤ j`.

The codomain is `WithTop ℚ`: half-integral terms are represented exactly, and
an infinite quadratic defect remains infinite.  Since the first candidate is
finite, the resulting minimum is proved finite and is also exposed as a
rational number through `alphaValue`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The defect order embedded from `ℕ∞` into `ℚ ∪ {∞}`. -/
noncomputable def defectOrder (a : Kˣ) : WithTop ℚ :=
  WithTop.map (fun m : Nat => (m : ℚ)) (quadraticDefect K a)

/-- The unit `-a_j a_{j+1}` occurring in Beli's definition of `α_i`. -/
noncomputable def adjacentProduct (b : GoodBONG q L (n + 1)) (j : Fin n) : Kˣ :=
  -(b.valueUnit j.castSucc * b.valueUnit j.succ)

/-- The relative quadratic defect `d(-a_j a_{j+1})`. -/
noncomputable def adjacentDefect (b : GoodBONG q L (n + 1)) (j : Fin n) :
    WithTop ℚ :=
  defectOrder (K := K) (b.adjacentProduct j)

/-- The half-gap candidate `(R_{i+1} - R_i) / 2 + e`. -/
noncomputable def halfGapCandidate (b : GoodBONG q L (n + 1)) (i : Fin n) :
    WithTop ℚ :=
  ((((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2 +
    (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)

/-- A candidate `R_{i+1} - R_j + d(-a_j a_{j+1})` with `j ≤ i`. -/
noncomputable def leftDefectCandidate (b : GoodBONG q L (n + 1))
    (i j : Fin n) : WithTop ℚ :=
  (((b.order i.succ - b.order j.castSucc : Int) : ℚ) : WithTop ℚ) +
    b.adjacentDefect j

/-- A candidate `R_{j+1} - R_i + d(-a_j a_{j+1})` with `i ≤ j`. -/
noncomputable def rightDefectCandidate (b : GoodBONG q L (n + 1))
    (i j : Fin n) : WithTop ℚ :=
  (((b.order j.succ - b.order i.castSucc : Int) : ℚ) : WithTop ℚ) +
    b.adjacentDefect j

/-- The finite nonempty set whose minimum is Beli's `α_i`. -/
noncomputable def alphaCandidates (b : GoodBONG q L (n + 1)) (i : Fin n) :
    Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate i)
    (((Finset.univ.filter fun j : Fin n => j ≤ i).image
        (b.leftDefectCandidate i)) ∪
      ((Finset.univ.filter fun j : Fin n => i ≤ j).image
        (b.rightDefectCandidate i)))

theorem halfGapCandidate_mem_alphaCandidates (b : GoodBONG q L (n + 1))
    (i : Fin n) : b.halfGapCandidate i ∈ b.alphaCandidates i :=
  Finset.mem_insert_self _ _

theorem alphaCandidates_nonempty (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.alphaCandidates i).Nonempty :=
  ⟨b.halfGapCandidate i, b.halfGapCandidate_mem_alphaCandidates i⟩

/-- Beli's invariant `α_i`, initially valued in `ℚ ∪ {∞}`. -/
noncomputable def alpha (b : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  (b.alphaCandidates i).min' (b.alphaCandidates_nonempty i)

theorem alpha_le_halfGapCandidate (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.alpha i ≤ b.halfGapCandidate i :=
  Finset.min'_le _ _ (b.halfGapCandidate_mem_alphaCandidates i)

theorem leftDefectCandidate_mem_alphaCandidates (b : GoodBONG q L (n + 1))
    {i j : Fin n} (hji : j ≤ i) :
    b.leftDefectCandidate i j ∈ b.alphaCandidates i := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨j, by simp [hji], rfl⟩

theorem rightDefectCandidate_mem_alphaCandidates (b : GoodBONG q L (n + 1))
    {i j : Fin n} (hij : i ≤ j) :
    b.rightDefectCandidate i j ∈ b.alphaCandidates i := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨j, by simp [hij], rfl⟩

theorem alpha_le_leftDefectCandidate (b : GoodBONG q L (n + 1))
    {i j : Fin n} (hji : j ≤ i) : b.alpha i ≤ b.leftDefectCandidate i j :=
  Finset.min'_le _ _ (b.leftDefectCandidate_mem_alphaCandidates hji)

theorem alpha_le_rightDefectCandidate (b : GoodBONG q L (n + 1))
    {i j : Fin n} (hij : i ≤ j) : b.alpha i ≤ b.rightDefectCandidate i j :=
  Finset.min'_le _ _ (b.rightDefectCandidate_mem_alphaCandidates hij)

/-- `α_i` is finite because the half-gap candidate is finite. -/
theorem alpha_ne_top (b : GoodBONG q L (n + 1)) (i : Fin n) : b.alpha i ≠ ⊤ := by
  intro htop
  have hle := b.alpha_le_halfGapCandidate i
  rw [htop] at hle
  simp [halfGapCandidate] at hle

/-- The finite rational value of Beli's `α_i`. -/
noncomputable def alphaValue (b : GoodBONG q L (n + 1)) (i : Fin n) : ℚ :=
  (b.alpha i).untop (b.alpha_ne_top i)

@[simp]
theorem coe_alphaValue (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.alphaValue i : WithTop ℚ) = b.alpha i :=
  WithTop.coe_untop _ _

/-- Product of the first `i` values of a good BONG. -/
noncomputable def prefixProduct (b : GoodBONG q L n) (i : Nat) : Kˣ :=
  b.toBONG.prefixProduct i

end BONG.GoodBONG

end Bong
