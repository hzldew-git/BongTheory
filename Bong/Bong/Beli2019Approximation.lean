/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationParity
import Bong.Bong.Beli2009ClassificationPropagation

/-!
# Beli (2019), Section 3 approximation objects

This file formalizes Definitions 9-10 using representatives in `Kˣ`.
Square-class equality is expressed by infinite quadratic defect, so the same
definition covers the empty and complete prefix conventions.
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

/-- Definition 9: `X` approximates the square class of the prefix product at
the boundary `i`.  Internal boundaries use `alpha_i`; endpoints use `top`. -/
noncomputable def IsPrefixApproximation
    (b : GoodBONG q L (n + 1)) (i : Nat) (X : Kˣ) : Prop :=
  b.prefixAlphaCap i ≤
    defectOrder (K := K) (X * b.prefixProduct i)

/-- The prefix product itself is a canonical approximation, since its square
has infinite defect. -/
theorem isPrefixApproximation_prefixProduct
    (b : GoodBONG q L (n + 1)) (i : Nat) :
    b.IsPrefixApproximation i (b.prefixProduct i) := by
  unfold IsPrefixApproximation
  rw [defectOrder_eq_top_of_isSquare]
  · exact le_top
  · refine ⟨b.prefixProduct i, ?_⟩
    rfl

/-- Multiplying an approximation representative by a square does not change
whether it approximates the prefix square class.  This is the explicit
`Kˣ` replacement for the paper's use of representatives in `Fˣ/Fˣ²`. -/
theorem isPrefixApproximation_mul_square_iff
    (b : GoodBONG q L (n + 1)) (i : Nat) (X s : Kˣ) :
    b.IsPrefixApproximation i (X * s ^ 2) ↔
      b.IsPrefixApproximation i X := by
  unfold IsPrefixApproximation
  have hproduct :
      (X * s ^ 2) * b.prefixProduct i =
        (X * b.prefixProduct i) * s ^ 2 := by
    ac_rfl
  rw [hproduct, defectOrder_mul_square]

/-- An approximation may be replaced by another representative whenever
their product has defect at least the relevant prefix cap.  This is the
one-sided domination step used repeatedly in Beli's Section 3 and in the
collision case of Lemma 5.13. -/
theorem isPrefixApproximation_of_defect_mul
    (b : GoodBONG q L (n + 1)) (i : Nat) (X Y : Kˣ)
    (hX : b.IsPrefixApproximation i X)
    (hXY : b.prefixAlphaCap i ≤ defectOrder (K := K) (X * Y)) :
    b.IsPrefixApproximation i Y := by
  unfold IsPrefixApproximation at hX ⊢
  exact (le_min hX hXY).trans (by
    simpa only [one_mul] using
      defectOrder_replace_left (K := K) 1 X Y (b.prefixProduct i))

/-- Definition 9 is independent of the chosen good BONG. -/
theorem isPrefixApproximation_changeBONG_iff
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (n + 1)) (i : Nat) (X : Kˣ) :
    a.IsPrefixApproximation i X ↔ a'.IsPrefixApproximation i X := by
  constructor
  · intro h
    unfold IsPrefixApproximation at h ⊢
    rw [← a.prefixAlphaCap_invariant a' i]
    calc
      a.prefixAlphaCap i ≤
          min
            (defectOrder (K := K) (X * a.prefixProduct i))
            (defectOrder (K := K)
              (a.prefixProduct i * a'.prefixProduct i)) :=
        le_min h (a.prefixChangeDefectBound_of_classification a' i)
      _ ≤ defectOrder (K := K) (X * a'.prefixProduct i) := by
        simpa only [mul_one] using
          defectOrder_replace_left X (a.prefixProduct i)
            (a'.prefixProduct i) 1
  · intro h
    unfold IsPrefixApproximation at h ⊢
    rw [← a'.prefixAlphaCap_invariant a i]
    calc
      a'.prefixAlphaCap i ≤
          min
            (defectOrder (K := K) (X * a'.prefixProduct i))
            (defectOrder (K := K)
              (a'.prefixProduct i * a.prefixProduct i)) :=
        le_min h (a'.prefixChangeDefectBound_of_classification a i)
      _ ≤ defectOrder (K := K) (X * a.prefixProduct i) := by
        simpa only [mul_one] using
          defectOrder_replace_left X (a'.prefixProduct i)
            (a.prefixProduct i) 1

/-- The capped defect computed from arbitrary prefix approximations. -/
noncomputable def truncatedApproximationDefect
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon : Kˣ) (i j : Nat) (X Y : Kˣ) : WithTop ℚ :=
  min (defectOrder (K := K) (epsilon * X * Y))
    (min (a.prefixAlphaCap i) (b.prefixAlphaCap j))

/-- Section 3's replacement formula
`d[epsilon a_(1,i)b_(1,j)] = d[epsilon X_i Y_j]`. -/
theorem truncatedPrefixDefect_eq_of_approximations
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (epsilon : Kˣ) (i j : Nat) (X Y : Kˣ)
    (hX : a.IsPrefixApproximation i X)
    (hY : b.IsPrefixApproximation j Y) :
    a.truncatedPrefixDefect b epsilon i j =
      a.truncatedApproximationDefect b epsilon i j X Y := by
  unfold IsPrefixApproximation at hX hY
  apply le_antisymm
  · have hdefect := a.truncatedPrefixDefect_le_defect b epsilon i j
    have hleftCap := a.truncatedPrefixDefect_le_leftCap b epsilon i j
    have hrightCap := a.truncatedPrefixDefect_le_rightCap b epsilon i j
    have hX' : a.prefixAlphaCap i ≤
        defectOrder (K := K) (a.prefixProduct i * X) := by
      simpa only [mul_comm] using hX
    have hY' : b.prefixAlphaCap j ≤
        defectOrder (K := K) (b.prefixProduct j * Y) := by
      simpa only [mul_comm] using hY
    have hleft : a.truncatedPrefixDefect b epsilon i j ≤
        defectOrder (K := K) (epsilon * X * b.prefixProduct j) :=
      (le_min hdefect (hleftCap.trans hX')).trans
        (defectOrder_replace_left epsilon (a.prefixProduct i) X
          (b.prefixProduct j))
    have hright : a.truncatedPrefixDefect b epsilon i j ≤
        defectOrder (K := K) (epsilon * X * Y) :=
      (le_min hleft (hrightCap.trans hY')).trans
        (defectOrder_replace_right epsilon X (b.prefixProduct j) Y)
    exact le_min hright (le_min hleftCap hrightCap)
  · have hdefect : a.truncatedApproximationDefect b epsilon i j X Y ≤
        defectOrder (K := K) (epsilon * X * Y) :=
      min_le_left _ _
    have hleftCap :
        a.truncatedApproximationDefect b epsilon i j X Y ≤
          a.prefixAlphaCap i :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hrightCap :
        a.truncatedApproximationDefect b epsilon i j X Y ≤
          b.prefixAlphaCap j :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hleft : a.truncatedApproximationDefect b epsilon i j X Y ≤
        defectOrder (K := K) (epsilon * a.prefixProduct i * Y) :=
      (le_min hdefect (hleftCap.trans hX)).trans
        (defectOrder_replace_left epsilon X (a.prefixProduct i) Y)
    have hright : a.truncatedApproximationDefect b epsilon i j X Y ≤
        defectOrder (K := K)
          (epsilon * a.prefixProduct i * b.prefixProduct j) :=
      (le_min hleft (hrightCap.trans hY)).trans
        (defectOrder_replace_right epsilon (a.prefixProduct i) Y
          (b.prefixProduct j))
    exact le_min hright (le_min hleftCap hrightCap)

/-- Exact two-step recurrence used to propagate scalar approximations inside
one Jordan component. -/
theorem prefixProduct_add_two
    (b : GoodBONG q L (n + 1)) (i : Nat) (hi : i + 1 < n + 1) :
    b.prefixProduct (i + 2) =
      b.prefixProduct i * b.valueUnit ⟨i, by omega⟩ *
        b.valueUnit ⟨i + 1, hi⟩ := by
  unfold GoodBONG.prefixProduct
  rw [b.toBONG.prefixProduct_succ (i + 1) hi,
    b.toBONG.prefixProduct_succ i (by omega)]
  rfl

/-- The raw induction step in Lemma 3.2. -/
theorem isPrefixApproximation_neg_add_two_of_baseDefect
    (b : GoodBONG q L (n + 1)) (i : Nat) (X : Kˣ)
    (hi : i + 2 < n + 1)
    (hbase : (b.alphaValue ⟨i + 1, by omega⟩ : WithTop ℚ) ≤
      defectOrder (K := K) (X * b.prefixProduct i))
    (hAdjacent : (b.alphaValue ⟨i + 1, by omega⟩ : WithTop ℚ) ≤
      b.adjacentDefect ⟨i, by omega⟩) :
    b.IsPrefixApproximation (i + 2) (-X) := by
  unfold IsPrefixApproximation
  rw [b.prefixAlphaCap_of_internal (by omega) hi]
  have hunit :
      (X * b.prefixProduct i) * b.adjacentProduct ⟨i, by omega⟩ =
        (-X) * b.prefixProduct (i + 2) := by
    rw [b.prefixProduct_add_two i (by omega)]
    have hzero : (⟨i, by omega⟩ : Fin (n + 1)) =
        (⟨i, by omega⟩ : Fin n).castSucc := by
      apply Fin.ext
      rfl
    have hone : (⟨i + 1, by omega⟩ : Fin (n + 1)) =
        (⟨i, by omega⟩ : Fin n).succ := by
      apply Fin.ext
      rfl
    rw [hzero, hone]
    apply Units.ext
    simp only [adjacentProduct, GoodBONG.valueUnit, Units.val_mul,
      Units.val_neg]
    ring
  calc
    (b.alphaValue ⟨i + 1, by omega⟩ : WithTop ℚ) ≤
        min (defectOrder (K := K) (X * b.prefixProduct i))
          (b.adjacentDefect ⟨i, by omega⟩) :=
      le_min hbase hAdjacent
    _ ≤ defectOrder (K := K)
        ((X * b.prefixProduct i) * b.adjacentProduct ⟨i, by omega⟩) :=
      defectOrder_mul_ge_min _ _
    _ = defectOrder (K := K) ((-X) * b.prefixProduct (i + 2)) := by
      rw [hunit]

/-- If the next alpha is controlled by the current alpha and the intervening
adjacent defect, negation propagates a prefix approximation two places to the
right. -/
theorem isPrefixApproximation_neg_add_two
    (b : GoodBONG q L (n + 1)) (i : Nat) (X : Kˣ)
    (hi0 : 0 < i) (hi : i + 2 < n + 1)
    (hAlpha : b.alphaValue ⟨i + 1, by omega⟩ ≤
      b.alphaValue ⟨i - 1, by omega⟩)
    (hAdjacent : (b.alphaValue ⟨i + 1, by omega⟩ : WithTop ℚ) ≤
      b.adjacentDefect ⟨i, by omega⟩)
    (hX : b.IsPrefixApproximation i X) :
    b.IsPrefixApproximation (i + 2) (-X) := by
  unfold IsPrefixApproximation at hX
  rw [b.prefixAlphaCap_of_internal hi0 (by omega)] at hX
  have hAlpha' : (b.alphaValue ⟨i + 1, by omega⟩ : WithTop ℚ) ≤
      (b.alphaValue ⟨i - 1, by omega⟩ : WithTop ℚ) := by
    exact_mod_cast hAlpha
  exact b.isPrefixApproximation_neg_add_two_of_baseDefect i X hi
    (hAlpha'.trans hX) hAdjacent

/-- Lemma 3.2's two-step propagation criterion in the form used inside a
Jordan block.  The alpha comparisons are derived from the displayed equality
of the two outer orders. -/
theorem isPrefixApproximation_neg_add_two_of_outerOrders_eq
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Nat) (X : Kˣ)
    (hi0 : 0 < i) (hi : i + 2 < n + 2)
    (houter : b.order ⟨i, by omega⟩ = b.order ⟨i + 2, hi⟩)
    (hX : b.IsPrefixApproximation i X) :
    b.IsPrefixApproximation (i + 2) (-X) := by
  have hAlpha : b.alphaValue ⟨i + 1, by omega⟩ ≤
      b.alphaValue ⟨i - 1, by omega⟩ := by
    apply b.alphaValue_le_of_rightEndpoint_orders_eq
      (i := ⟨i - 1, by omega⟩) (j := ⟨i + 1, by omega⟩) (by
        change i - 1 ≤ i + 1
        omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using houter
  have hAdjacent := (b.alpha_pair_le_adjacentDefects i hi houter).1
  exact b.isPrefixApproximation_neg_add_two i X hi0 hi hAlpha hAdjacent hX

/-- The same order-equality propagation including the empty-prefix base
case `i = 0`. -/
theorem isPrefixApproximation_neg_add_two_of_outerOrders_eq_any
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Nat) (X : Kˣ)
    (hi : i + 2 < n + 2)
    (houter : b.order ⟨i, by omega⟩ = b.order ⟨i + 2, hi⟩)
    (hX : b.IsPrefixApproximation i X) :
    b.IsPrefixApproximation (i + 2) (-X) := by
  by_cases hi0 : i = 0
  · subst i
    unfold IsPrefixApproximation at hX
    rw [b.prefixAlphaCap_zero] at hX
    have htop : defectOrder (K := K) (X * b.prefixProduct 0) = ⊤ :=
      top_unique hX
    have hbase : (b.alphaValue ⟨1, by omega⟩ : WithTop ℚ) ≤
        defectOrder (K := K) (X * b.prefixProduct 0) := by
      rw [htop]
      exact le_top
    have hAdjacent := (b.alpha_pair_le_adjacentDefects 0 hi houter).1
    exact b.isPrefixApproximation_neg_add_two_of_baseDefect 0 X hi
      hbase hAdjacent
  · exact b.isPrefixApproximation_neg_add_two_of_outerOrders_eq i X
      (Nat.pos_of_ne_zero hi0) hi houter hX

/-- The left-hand trigger in Definition 10. -/
noncomputable def leftApproximationTrigger
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  i.1 = 0 ∨
    ∃ hi : 0 < i.1,
      (2 * ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.1 - 1, by omega⟩ + b.alphaValue i

/-- The right-hand trigger in Definition 10. -/
noncomputable def rightApproximationTrigger
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  i.1 + 1 = n ∨
    ∃ hi : i.1 + 1 < n,
      (2 * ramificationIndex K : ℚ) <
        b.alphaValue i + b.alphaValue ⟨i.1 + 1, hi⟩

/-- A lower bound on the two adjacent prefix caps activates the left clause
of Definition 10. -/
theorem leftApproximationTrigger_of_prefixCaps
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (h : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1)) :
    b.leftApproximationTrigger i := by
  by_cases hi0 : i.val = 0
  · exact Or.inl hi0
  · refine Or.inr ⟨Nat.pos_of_ne_zero hi0, ?_⟩
    rw [b.prefixAlphaCap_of_internal (Nat.pos_of_ne_zero hi0) (by omega),
      b.prefixAlphaCap_of_internal (by omega) (by omega)] at h
    exact_mod_cast h

/-- A lower bound on the two adjacent prefix caps activates the right clause
of Definition 10. -/
theorem rightApproximationTrigger_of_prefixCaps
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (h : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      b.prefixAlphaCap (i.val + 1) + b.prefixAlphaCap (i.val + 2)) :
    b.rightApproximationTrigger i := by
  by_cases hilast : i.val + 1 = n
  · exact Or.inl hilast
  · have hinternal : i.val + 1 < n := by omega
    refine Or.inr ⟨hinternal, ?_⟩
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega),
      b.prefixAlphaCap_of_internal (by omega) (by omega)] at h
    exact_mod_cast h

/-- Definition 10, approximation to the left, for a diagonal presentation
of the approximating quadratic space. -/
noncomputable def IsLeftSpaceApproximation
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ) : Prop :=
  b.IsPrefixApproximation (i.1 + 1) (diagonalUnitDeterminant c) ∧
    (b.leftApproximationTrigger i →
      DiagonalRepresents
        (b.prefixValues i.1 (by omega)) (diagonalUnitCoefficients c))

/-- Definition 10, approximation to the right. -/
noncomputable def IsRightSpaceApproximation
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ) : Prop :=
  b.IsPrefixApproximation (i.1 + 1) (diagonalUnitDeterminant c) ∧
    (b.rightApproximationTrigger i →
      DiagonalRepresents (diagonalUnitCoefficients c)
        (b.prefixValues (i.1 + 2) (by omega)))

/-- Definition 10, a two-sided approximation. -/
noncomputable def IsSpaceApproximation
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ) : Prop :=
  b.IsLeftSpaceApproximation i c ∧ b.IsRightSpaceApproximation i c

/-- Remark 3.1: away from both alpha-sum triggers, determinant
approximation is the only condition. -/
theorem isSpaceApproximation_of_vacuous
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (c : Fin (i.1 + 1) → Kˣ)
    (hdet : b.IsPrefixApproximation (i.1 + 1)
      (diagonalUnitDeterminant c))
    (hleftIndex : 0 < i.1)
    (hleftSum : b.alphaValue ⟨i.1 - 1, by omega⟩ +
      b.alphaValue i ≤ (2 * ramificationIndex K : ℚ))
    (hrightIndex : i.1 + 1 < n)
    (hrightSum : b.alphaValue i + b.alphaValue ⟨i.1 + 1, by omega⟩ ≤
      (2 * ramificationIndex K : ℚ)) :
    b.IsSpaceApproximation i c := by
  constructor
  · refine ⟨hdet, ?_⟩
    rintro (hzero | ⟨_, hsum⟩)
    · omega
    · exact False.elim ((not_lt_of_ge hleftSum) hsum)
  · refine ⟨hdet, ?_⟩
    rintro (hlast | ⟨_, hsum⟩)
    · omega
    · exact False.elim ((not_lt_of_ge hrightSum) hsum)

end BONG.GoodBONG

end Bong
