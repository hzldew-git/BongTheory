/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SpaceApproximation

/-!
# Beli (2019), Section 3 approximation formulas for `A_i`

Every capped defect in Definition 4 is rewritten using arbitrary scalar
approximations `X_i` and `Y_i`.  This includes the exceptional terminal
quantity and gives the exact equivalence between conditions (ii) and (ii')
in Lemma 3.10.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The primary candidate for `A_i`, computed from scalar approximations. -/
noncomputable def representationApproximationPrimary
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    a.truncatedApproximationDefect b (-1) (i.val + 1) (i.val - 1)
      (X (i.val + 1)) (Y (i.val - 1))

/-- The optional secondary candidate for `A_i`, computed from scalar
approximations. -/
noncomputable def representationApproximationSecondary
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (X Y : Nat → Kˣ) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    a.truncatedApproximationDefect b 1 (i.val + 2) (i.val - 2)
      (X (i.val + 2)) (Y (i.val - 2))

/-- The candidate set for `A_i`, with every defect computed from
approximations. -/
noncomputable def representationApproximationCandidates
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ) : Finset (WithTop ℚ) :=
  insert (a.representationHalfGap b i)
    (insert (a.representationApproximationPrimary b i X Y)
      (if h : 1 < i.val ∧ i.val + 1 < m + 1 then
        {a.representationApproximationSecondary b i h X Y}
      else ∅))

theorem representationApproximationCandidates_nonempty
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (X Y : Nat → Kˣ) :
    (a.representationApproximationCandidates b i X Y).Nonempty :=
  ⟨a.representationHalfGap b i, Finset.mem_insert_self _ _⟩

/-- `A_i` computed entirely from the chosen scalar approximations. -/
noncomputable def representationApproximationAlpha
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ) : WithTop ℚ :=
  (a.representationApproximationCandidates b i X Y).min'
    (a.representationApproximationCandidates_nonempty b i X Y)

theorem representationApproximationPrimary_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.representationApproximationPrimary b i X Y =
      a.representationPrimaryDefect b i := by
  unfold representationApproximationPrimary representationPrimaryDefect
  rw [← a.truncatedPrefixDefect_eq_of_approximations b (-1)
    (i.val + 1) (i.val - 1) (X (i.val + 1)) (Y (i.val - 1))
    (hX _) (hY _)]

theorem representationApproximationSecondary_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.representationApproximationSecondary b i hi X Y =
      a.representationSecondaryDefect b i hi := by
  unfold representationApproximationSecondary representationSecondaryDefect
  rw [← a.truncatedPrefixDefect_eq_of_approximations b 1
    (i.val + 2) (i.val - 2) (X (i.val + 2)) (Y (i.val - 2))
    (hX _) (hY _)]

theorem representationApproximationCandidates_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.representationApproximationCandidates b i X Y =
      a.representationAlphaCandidates b i := by
  unfold representationApproximationCandidates representationAlphaCandidates
  rw [a.representationApproximationPrimary_eq b i X Y hX hY]
  split_ifs with hi
  · rw [a.representationApproximationSecondary_eq b i hi X Y hX hY]
  · rfl

/-- The approximation formula computes the original invariant `A_i`. -/
theorem representationApproximationAlpha_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.representationApproximationAlpha b i X Y =
      a.representationAlpha b i := by
  unfold representationApproximationAlpha representationAlpha
  have hsets := a.representationApproximationCandidates_eq b i X Y hX hY
  simp only [hsets]

/-- The first candidate in the exceptional terminal value, computed from
approximations. -/
noncomputable def terminalApproximationPrimary
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ) : WithTop ℚ :=
  ((a.order ⟨n + 2, hgap⟩ : Int) : ℚ) +
    a.truncatedApproximationDefect b (-1) (n + 3) (n + 1)
      (X (n + 3)) (Y (n + 1))

/-- The optional second candidate in the exceptional terminal value,
computed from approximations. -/
noncomputable def terminalApproximationSecondary
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hinner : n + 3 < m + 1) (X Y : Nat → Kˣ) : WithTop ℚ :=
  (((a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 3, hinner⟩ -
      b.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
    a.truncatedApproximationDefect b 1 (n + 4) n
      (X (n + 4)) (Y n)

noncomputable def terminalApproximationCandidates
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ) : Finset (WithTop ℚ) :=
  insert (a.terminalApproximationPrimary b hgap X Y)
    (if hinner : n + 3 < m + 1 then
      {a.terminalApproximationSecondary b hinner X Y}
    else ∅)

theorem terminalApproximationCandidates_nonempty
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ) :
    (a.terminalApproximationCandidates b hgap X Y).Nonempty :=
  ⟨a.terminalApproximationPrimary b hgap X Y,
    Finset.mem_insert_self _ _⟩

noncomputable def terminalApproximationAlpha
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ) : WithTop ℚ :=
  (a.terminalApproximationCandidates b hgap X Y).min'
    (a.terminalApproximationCandidates_nonempty b hgap X Y)

theorem terminalApproximationPrimary_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.terminalApproximationPrimary b hgap X Y =
      a.terminalAdjustedPrimary b hgap := by
  unfold terminalApproximationPrimary terminalAdjustedPrimary
  rw [← a.truncatedPrefixDefect_eq_of_approximations b (-1)
    (n + 3) (n + 1) (X (n + 3)) (Y (n + 1)) (hX _) (hY _)]

theorem terminalApproximationSecondary_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hinner : n + 3 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.terminalApproximationSecondary b hinner X Y =
      a.terminalAdjustedSecondary b hinner := by
  unfold terminalApproximationSecondary terminalAdjustedSecondary
  rw [← a.truncatedPrefixDefect_eq_of_approximations b 1
    (n + 4) n (X (n + 4)) (Y n) (hX _) (hY _)]

theorem terminalApproximationCandidates_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.terminalApproximationCandidates b hgap X Y =
      a.terminalAdjustedCandidates b hgap := by
  unfold terminalApproximationCandidates terminalAdjustedCandidates
  rw [a.terminalApproximationPrimary_eq b hgap X Y hX hY]
  split_ifs with hinner
  · rw [a.terminalApproximationSecondary_eq b hinner X Y hX hY]
  · rfl

theorem terminalApproximationAlpha_eq
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.terminalApproximationAlpha b hgap X Y =
      a.terminalAdjustedAlpha b hgap := by
  unfold terminalApproximationAlpha terminalAdjustedAlpha
  have hsets := a.terminalApproximationCandidates_eq b hgap X Y hX hY
  simp only [hsets]

/-- Condition (ii') of Lemma 3.10. -/
noncomputable def ApproximationDefectCondition
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (X Y : Nat → Kˣ) : Prop :=
  ∀ i : RepresentationIndex (m + 1) (n + 1),
    a.representationApproximationAlpha b i X Y ≤
      a.truncatedApproximationDefect b 1 i.val i.val
        (X i.val) (Y i.val)

/-- Lemma 3.10(ii): condition (ii) is unchanged when all prefix products
are replaced by arbitrary scalar approximations. -/
theorem representationDefectCondition_iff_approximation
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.RepresentationDefectCondition b ↔
      a.ApproximationDefectCondition b X Y := by
  unfold RepresentationDefectCondition ApproximationDefectCondition
  constructor <;> intro h i
  · rw [a.representationApproximationAlpha_eq b i X Y hX hY,
      ← a.coe_representationAlphaValue b i,
      ← a.truncatedPrefixDefect_eq_of_approximations b 1 i.val i.val
        (X i.val) (Y i.val) (hX _) (hY _)]
    exact h i
  · rw [a.coe_representationAlphaValue b i,
      ← a.representationApproximationAlpha_eq b i X Y hX hY,
      a.truncatedPrefixDefect_eq_of_approximations b 1 i.val i.val
        (X i.val) (Y i.val) (hX _) (hY _)]
    exact h i

end BONG.GoodBONG

end Bong
