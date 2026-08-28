/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanCoordinates
import Bong.Bong.Classification
import Bong.Bong.DefectArithmetic

/-!
# Beli (2009/2010), Lemmas 3.2--3.4

This file proves the two-step propagation of prefix defect bounds from the
exact prefix-product recurrence and quadratic-defect domination.  It also
packages the Jordan-chain reduction of Lemma 3.3 and derives Lemma 3.4
directly from property P6.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

namespace BONG.GoodBONG

noncomputable def comparisonPrefixUnit
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) : Kˣ :=
  a.prefixProduct m * b.prefixProduct m

theorem comparisonPrefixUnit_add_two
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    comparisonPrefixUnit a b (m + 2) =
      comparisonPrefixUnit a b m *
        a.adjacentProduct ⟨m, by omega⟩ *
          b.adjacentProduct ⟨m, by omega⟩ := by
  unfold comparisonPrefixUnit GoodBONG.prefixProduct adjacentProduct
    GoodBONG.valueUnit
  rw [a.toBONG.prefixProduct_succ (m + 1) hm,
    a.toBONG.prefixProduct_succ m (by omega),
    b.toBONG.prefixProduct_succ (m + 1) hm,
    b.toBONG.prefixProduct_succ m (by omega)]
  have hzero :
      (⟨m, by omega⟩ : Fin (N + 1)) =
        (⟨m, by omega⟩ : Fin N).castSucc := by
    apply Fin.ext
    rfl
  have hone :
      (⟨m + 1, hm⟩ : Fin (N + 1)) =
        (⟨m, by omega⟩ : Fin N).succ := by
    apply Fin.ext
    rfl
  rw [hzero, hone]
  apply Units.ext
  simp only [Units.val_mul, Units.val_neg]
  ring

noncomputable def comparisonPrefixDefect
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) : WithTop Rat :=
  defectOrder (K := K) (comparisonPrefixUnit a b m)

theorem comparisonPrefixDefect_add_two
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    min (comparisonPrefixDefect a b m)
        (min (a.adjacentDefect ⟨m, by omega⟩)
          (b.adjacentDefect ⟨m, by omega⟩)) <=
      comparisonPrefixDefect a b (m + 2) := by
  let x := comparisonPrefixUnit a b m
  let y := a.adjacentProduct ⟨m, by omega⟩
  let z := b.adjacentProduct ⟨m, by omega⟩
  have hxy := defectOrder_mul_ge_min (K := K) x y
  have hxyz := defectOrder_mul_ge_min (K := K) (x * y) z
  have hbound :
      min (defectOrder (K := K) x)
          (min (defectOrder (K := K) y) (defectOrder (K := K) z)) <=
        defectOrder (K := K) ((x * y) * z) := by
    rw [← min_assoc]
    exact (min_le_min hxy le_rfl).trans hxyz
  rw [comparisonPrefixDefect, comparisonPrefixDefect,
    comparisonPrefixUnit_add_two a b m hm]
  simpa [x, y, z, adjacentDefect] using hbound

theorem comparisonPrefixDefect_reverse_add_two
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 1)) (b : GoodBONG r M (N + 1))
    (m : Nat) (hm : m + 1 < N + 1) :
    min (comparisonPrefixDefect a b (m + 2))
        (min (a.adjacentDefect ⟨m, by omega⟩)
          (b.adjacentDefect ⟨m, by omega⟩)) <=
      comparisonPrefixDefect a b m := by
  let x := comparisonPrefixUnit a b m
  let y := a.adjacentProduct ⟨m, by omega⟩
  let z := b.adjacentProduct ⟨m, by omega⟩
  have hxy := defectOrder_mul_ge_min (K := K) (x * y * z) y
  have hxyz := defectOrder_mul_ge_min (K := K) ((x * y * z) * y) z
  have hbound :
      min (defectOrder (K := K) (x * y * z))
          (min (defectOrder (K := K) y) (defectOrder (K := K) z)) <=
        defectOrder (K := K) (((x * y * z) * y) * z) := by
    rw [← min_assoc]
    exact (min_le_min hxy le_rfl).trans hxyz
  have hsquare :
      defectOrder (K := K) (((x * y * z) * y) * z) =
        defectOrder (K := K) x := by
    rw [show ((x * y * z) * y) * z = x * (y * z) ^ 2 by
      simp only [pow_two]
      ac_rfl]
    exact defectOrder_mul_square x (y * z)
  rw [hsquare] at hbound
  rw [comparisonPrefixDefect, comparisonPrefixDefect,
    comparisonPrefixUnit_add_two a b m hm]
  simpa [x, y, z, adjacentDefect] using hbound

/-- Equal orders two places apart turn the adjacent alpha candidates into
plain adjacent-defect bounds. -/
theorem alpha_pair_le_adjacentDefects
    (a : GoodBONG q L (N + 1)) (j : Nat) (hj : j + 2 < N + 1)
    (houter : a.order ⟨j, by omega⟩ = a.order ⟨j + 2, hj⟩) :
    ((a.alphaValue ⟨j + 1, by omega⟩ : WithTop ℚ) <=
        a.adjacentDefect ⟨j, by omega⟩) ∧
      ((a.alphaValue ⟨j, by omega⟩ : WithTop ℚ) <=
        a.adjacentDefect ⟨j + 1, by omega⟩) := by
  constructor
  · have h := a.alpha_le_leftDefectCandidate
        (i := ⟨j + 1, by omega⟩) (j := ⟨j, by omega⟩) (by
          change j <= j + 1
          omega)
    rw [← a.coe_alphaValue] at h
    unfold leftDefectCandidate at h
    have hright :
        a.order (⟨j + 1, by omega⟩ : Fin N).succ =
          a.order ⟨j + 2, hj⟩ := by
      congr 2
    have hleft :
        a.order (⟨j, by omega⟩ : Fin N).castSucc =
          a.order ⟨j, by omega⟩ := by
      congr 2
    rw [hright, hleft, ← houter] at h
    simpa using h
  · have h := a.alpha_le_rightDefectCandidate
        (i := ⟨j, by omega⟩) (j := ⟨j + 1, by omega⟩) (by
          change j <= j + 1
          omega)
    rw [← a.coe_alphaValue] at h
    unfold rightDefectCandidate at h
    have hright :
        a.order (⟨j + 1, by omega⟩ : Fin N).succ =
          a.order ⟨j + 2, hj⟩ := by
      congr 2
    have hleft :
        a.order (⟨j, by omega⟩ : Fin N).castSucc =
          a.order ⟨j, by omega⟩ := by
      congr 2
    rw [hright, hleft, ← houter] at h
    simpa using h

theorem alphaValue_le_of_rightEndpoint_orders_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) {i j : Fin (N + 1)} (hij : i <= j)
    (horder : a.order i.succ = a.order j.succ) :
    a.alphaValue j <= a.alphaValue i := by
  have h := a.alphaRightEndpoint_antitone hij
  unfold alphaRightEndpoint at h
  rw [← horder] at h
  linarith

theorem alphaValue_le_of_leftEndpoint_orders_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) {i j : Fin (N + 1)} (hij : i <= j)
    (horder : a.order i.castSucc = a.order j.castSucc) :
    a.alphaValue i <= a.alphaValue j := by
  have h := a.alphaLeftEndpoint_monotone hij
  unfold alphaLeftEndpoint at h
  rw [horder] at h
  linarith

end BONG.GoodBONG

/-- Ambient isometry preserves the determinant square class of full BONGs.
This is the determinant input at the right endpoint of Lemma 3.2. -/
class Beli2009AmbientDeterminantLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  fullComparison_isSquare
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {s : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {N : Nat}
    (ambient : q.IsIsometric s)
    (a : BONG.GoodBONG q L (N + 1))
    (b : BONG.GoodBONG s M (N + 1)) :
    IsSquare (a.comparisonPrefixUnit b (N + 1))

namespace BONG.GoodBONG

variable {W : Type w} [AddCommGroup W] [Module K W]
  {s : QuadraticSpace K W} {M : Lattice K W}

theorem comparisonPrefixDefect_zero
    (a : GoodBONG q L (N + 1)) (b : GoodBONG s M (N + 1)) :
    comparisonPrefixDefect a b 0 = ⊤ := by
  unfold comparisonPrefixDefect comparisonPrefixUnit GoodBONG.prefixProduct
  rw [BONG.prefixProduct_zero, BONG.prefixProduct_zero]
  simpa using defectOrder_one (K := K)

theorem comparisonPrefixDefect_full_eq_top
    [Beli2009AmbientDeterminantLaws.{u, v, w} K]
    (ambient : q.IsIsometric s)
    (a : GoodBONG q L (N + 1)) (b : GoodBONG s M (N + 1)) :
    comparisonPrefixDefect a b (N + 1) = ⊤ := by
  unfold comparisonPrefixDefect defectOrder
  rw [quadraticDefect_eq_top_of_isSquare (K := K)
    (Beli2009AmbientDeterminantLaws.fullComparison_isSquare ambient a b)]
  rfl

/-- The forward half of Beli's Lemma 3.2 in a fixed ambient dimension.
If the prefix condition immediately to the left of a triple is available
(or the triple begins at the first coordinate), then the condition at the
right-hand interior index propagates across two equal-order endpoints. -/
theorem beli2009Lemma32_forward
    [Beli2006AlphaLaws.{u, v} K]
    {N : Nat} (a : GoodBONG q L (N + 2)) (b : GoodBONG s M (N + 2))
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (l : Nat) (hfit : l + 2 < N + 2)
    (houter : a.order ⟨l, by omega⟩ = a.order ⟨l + 2, by omega⟩)
    (hleft : l = 0 ∨ ∃ hl : 0 < l,
      (a.alphaValue ⟨l - 1, by omega⟩ : WithTop ℚ) ≤
        comparisonPrefixDefect a b l) :
    (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) ≤
      comparisonPrefixDefect a b (l + 2) := by
  have houterB :
      b.order ⟨l, by omega⟩ = b.order ⟨l + 2, by omega⟩ := by
    calc
      b.order ⟨l, by omega⟩ = a.order ⟨l, by omega⟩ :=
        (horders _).symm
      _ = a.order ⟨l + 2, by omega⟩ := houter
      _ = b.order ⟨l + 2, by omega⟩ := horders _
  have hbase :
      (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) ≤
        comparisonPrefixDefect a b l := by
    rcases hleft with hzero | ⟨hl, hbound⟩
    · subst l
      rw [comparisonPrefixDefect_zero]
      exact le_top
    · let i : Fin (N + 1) := ⟨l - 1, by omega⟩
      let j : Fin (N + 1) := ⟨l + 1, by omega⟩
      have hmono := a.alphaValue_le_of_rightEndpoint_orders_eq
          (i := i) (j := j)
          (by
            change l - 1 ≤ l + 1
            omega)
          (by
            have hli :
                i.succ = (⟨l, by omega⟩ : Fin (N + 2)) := by
              apply Fin.ext
              dsimp only [i]
              simp
              omega
            have hri :
                j.succ = (⟨l + 2, by omega⟩ : Fin (N + 2)) := by
              apply Fin.ext
              dsimp only [j]
              rfl
            rw [hli, hri]
            exact houter)
      have hmonoTop :
          (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) ≤
            (a.alphaValue ⟨l - 1, by omega⟩ : WithTop ℚ) := by
        simpa only [i, j] using (show
          (a.alphaValue j : WithTop ℚ) ≤ (a.alphaValue i : WithTop ℚ) by
            exact_mod_cast hmono)
      exact hmonoTop.trans hbound
  have hlocalA :=
    (a.alpha_pair_le_adjacentDefects l (by omega) houter).1
  have hlocalBRaw :=
    (b.alpha_pair_le_adjacentDefects l (by omega) houterB).1
  have hlocalB :
      (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) ≤
        b.adjacentDefect ⟨l, by omega⟩ := by
    rw [halphas ⟨l + 1, by omega⟩]
    exact hlocalBRaw
  have hdom := comparisonPrefixDefect_add_two a b l (by omega)
  exact (le_min hbase (le_min hlocalA hlocalB)).trans hdom

/-- Beli (2009/2010), Lemma 3.2.  The natural numbers `l` and `r`
count the coordinates strictly before and after the displayed triple. -/
theorem beli2009Lemma32
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AmbientDeterminantLaws.{u, v, w} K]
    {l r : Nat} (ambient : q.IsIsometric s)
    (a : GoodBONG q L ((l + r + 1) + 2))
    (b : GoodBONG s M ((l + r + 1) + 2))
    (horders : a.SameOrders b) (halphas : a.SameAlphas b)
    (houter : a.order ⟨l, by omega⟩ = a.order ⟨l + 2, by omega⟩)
    (hleft : l = 0 ∨ ∃ hl : 0 < l,
      (a.alphaValue ⟨l - 1, by omega⟩ : WithTop ℚ) <=
        comparisonPrefixDefect a b l)
    (hright : r = 0 ∨ ∃ hr : 0 < r,
      (a.alphaValue ⟨l + 2, by omega⟩ : WithTop ℚ) <=
        comparisonPrefixDefect a b (l + 3)) :
    ((a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) <=
        comparisonPrefixDefect a b (l + 2)) ∧
      ((a.alphaValue ⟨l, by omega⟩ : WithTop ℚ) <=
        comparisonPrefixDefect a b (l + 1)) := by
  have houterB :
      b.order ⟨l, by omega⟩ = b.order ⟨l + 2, by omega⟩ := by
    calc
      b.order ⟨l, by omega⟩ = a.order ⟨l, by omega⟩ :=
        (horders _).symm
      _ = a.order ⟨l + 2, by omega⟩ := houter
      _ = b.order ⟨l + 2, by omega⟩ := horders _
  constructor
  · have hbase :
        (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) <=
          comparisonPrefixDefect a b l := by
      rcases hleft with hzero | ⟨hl, hbound⟩
      · subst l
        rw [comparisonPrefixDefect_zero]
        exact le_top
      · have hmono := a.alphaValue_le_of_rightEndpoint_orders_eq
            (i := ⟨l - 1, by omega⟩) (j := ⟨l + 1, by omega⟩)
            (by
              change l - 1 <= l + 1
              omega)
            (by
              have hli :
                  (⟨l - 1, by omega⟩ : Fin (l + r + 2)).succ =
                    (⟨l, by omega⟩ : Fin (l + r + 3)) := by
                apply Fin.ext
                simp
                omega
              have hri :
                  (⟨l + 1, by omega⟩ : Fin (l + r + 2)).succ =
                    (⟨l + 2, by omega⟩ : Fin (l + r + 3)) := by
                apply Fin.ext
                rfl
              rw [hli, hri]
              exact houter)
        have hmonoTop :
            (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) <=
              (a.alphaValue ⟨l - 1, by omega⟩ : WithTop ℚ) := by
          exact_mod_cast hmono
        exact hmonoTop.trans hbound
    have hlocalA :=
      (a.alpha_pair_le_adjacentDefects l (by omega) houter).1
    have hlocalBRaw :=
      (b.alpha_pair_le_adjacentDefects l (by omega) houterB).1
    have hlocalB :
        (a.alphaValue ⟨l + 1, by omega⟩ : WithTop ℚ) <=
          b.adjacentDefect ⟨l, by omega⟩ := by
      rw [halphas ⟨l + 1, by omega⟩]
      exact hlocalBRaw
    have hdom := comparisonPrefixDefect_add_two a b l (by omega)
    exact (le_min hbase (le_min hlocalA hlocalB)).trans hdom
  · have hbase :
        (a.alphaValue ⟨l, by omega⟩ : WithTop ℚ) <=
          comparisonPrefixDefect a b (l + 3) := by
      rcases hright with hzero | ⟨hr, hbound⟩
      · subst r
        rw [comparisonPrefixDefect_full_eq_top ambient]
        exact le_top
      · have hmono := a.alphaValue_le_of_leftEndpoint_orders_eq
            (i := ⟨l, by omega⟩) (j := ⟨l + 2, by omega⟩)
            (by
              change l <= l + 2
              omega)
            (by
              have hli :
                  (⟨l, by omega⟩ : Fin (l + r + 2)).castSucc =
                    (⟨l, by omega⟩ : Fin (l + r + 3)) := by
                apply Fin.ext
                rfl
              have hri :
                  (⟨l + 2, by omega⟩ : Fin (l + r + 2)).castSucc =
                    (⟨l + 2, by omega⟩ : Fin (l + r + 3)) := by
                apply Fin.ext
                rfl
              rw [hli, hri]
              exact houter)
        have hmonoTop :
            (a.alphaValue ⟨l, by omega⟩ : WithTop ℚ) <=
              (a.alphaValue ⟨l + 2, by omega⟩ : WithTop ℚ) := by
          exact_mod_cast hmono
        exact hmonoTop.trans hbound
    have hlocalA :=
      (a.alpha_pair_le_adjacentDefects l (by omega) houter).2
    have hlocalBRaw :=
      (b.alpha_pair_le_adjacentDefects l (by omega) houterB).2
    have hlocalB :
        (a.alphaValue ⟨l, by omega⟩ : WithTop ℚ) <=
          b.adjacentDefect ⟨l + 1, by omega⟩ := by
      rw [halphas ⟨l, by omega⟩]
      exact hlocalBRaw
    have hdom := comparisonPrefixDefect_reverse_add_two
      a b (l + 1) (by omega)
    exact (le_min hbase (le_min hlocalA hlocalB)).trans hdom

/-- Beli (2009/2010), Lemma 3.4. -/
theorem beli2009Lemma34
    [Beli2006AlphaLaws.{u, v} K]
    {l r : Nat} (a : GoodBONG q L ((l + r + 1) + 2))
    (houter : a.order ⟨l, by omega⟩ = a.order ⟨l + 2, by omega⟩) :
    a.alphaValue ⟨l, by omega⟩ +
        a.alphaValue ⟨l + 1, by omega⟩ <=
      2 * (ramificationIndex K : ℚ) := by
  have hp6 : a.SatisfiesAlphaP6 := a.alpha_p6
  unfold SatisfiesAlphaP6 at hp6
  apply hp6 (⟨l, by omega⟩ : Fin (l + r + 2)) (by
    change l + 1 < l + r + 2
    omega)
  have hleft :
      a.order (⟨l, by omega⟩ : Fin (l + r + 2)).castSucc =
        a.order ⟨l, by omega⟩ := by
    congr 2
  have hright :
      a.order
          (⟨l + 1, by omega⟩ : Fin (l + r + 2)).succ =
        a.order ⟨l + 2, by omega⟩ := by
    congr 2
  rw [hleft, hright]
  exact houter

/-- Square-class congruence of two nonzero scalars modulo a fractional ideal.
This is Beli's notation `x ≅ y (mod I)`: the quotient `y / x` belongs to
`(1 + I) Kˣ²`.  The square multiplier is essential because determinants and
norm generators are only defined up to square. -/
def UnitsCongruentModulo (x y : Kˣ) (I : Lattice.CoefficientIdeal (K := K)) :
    Prop :=
  ∃ s : Kˣ, (y : K) / (x : K) / (s : K) ^ 2 - 1 ∈ I

/-- The scalar consequence of O'Meara's determinant congruence 93:28(i).
If two nonzero determinants have the same valuation and their ratio is
congruent to one modulo `𝔭^r`, then their product has relative quadratic
defect at least `r`.  The product, rather than the ratio, is the form used by
Beli's prefix-approximation convention; the two differ by a square. -/
theorem natCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
    (x y : Kˣ) (r : Nat) (horder : ordUnit K x = ordUnit K y)
    (hcongruent : UnitsCongruentModulo x y
      (Lattice.powerIdeal (K := K) (r : Int))) :
    ((((r : Nat) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (x * y)) := by
  rcases hcongruent with ⟨s, hcongruent⟩
  let ratio : Kˣ := y / x
  have hratioOrder : ordUnit K ratio = 0 := by
    dsimp only [ratio]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, horder]
    omega
  let adjusted : K := (ratio : K) / (s : K) ^ 2
  have hadjustedCongruent :
      adjusted - 1 ∈ Lattice.powerIdeal (K := K) (r : Int) := by
    simpa only [adjusted, ratio, Units.val_div_eq_div_val] using hcongruent
  have hadjustedBound :
      ((r : Int) : WithTop Int) ≤ ord K (adjusted - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (r : Int) (adjusted - 1)).1
      hadjustedCongruent
  have happroximation : IsQuadraticApproximation K ratio r := by
    by_cases hr : r = 0
    · subst r
      exact isQuadraticApproximation_zero K ratio
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have herrorPos : (0 : WithTop Int) < ord K (adjusted - 1) := by
      have hrposInt : (0 : Int) < (r : Int) := by exact_mod_cast hrpos
      exact (show (0 : WithTop Int) < (r : Int) by exact_mod_cast hrposInt).trans_le
        hadjustedBound
    have hadjustedOrder : ord K adjusted = 0 := by
      have hadd := (ord K).map_add_eq_of_lt_left (show
        ord K (1 : K) < ord K (adjusted - 1) by
          simpa only [ord_one] using herrorPos)
      have honeAdd : (1 : K) + (adjusted - 1) = adjusted := by ring
      rw [honeAdd] at hadd
      simpa only [ord_one] using hadd
    have hadjustedNe : adjusted ≠ 0 := by
      dsimp only [adjusted, ratio]
      exact div_ne_zero (Units.ne_zero (y / x))
        (pow_ne_zero 2 (Units.ne_zero s))
    refine ⟨(s : K), ?_⟩
    have hnormalized :
        1 - (s : K) ^ 2 / (ratio : K) =
          (adjusted - 1) / adjusted := by
      dsimp only [adjusted]
      field_simp [Units.ne_zero ratio, Units.ne_zero s]
    rw [hnormalized, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hadjustedOrder]
    simpa using hadjustedBound
  have hratioDefect :=
    natCast_le_defectOrder_of_isQuadraticApproximation ratio r happroximation
  calc
    (((r : Nat) : ℚ) : WithTop ℚ) ≤ defectOrder (K := K) ratio :=
      hratioDefect
    _ = defectOrder (K := K) (ratio * x ^ 2) :=
      (defectOrder_mul_square ratio x).symm
    _ = defectOrder (K := K) (x * y) := by
      congr 1
      dsimp only [ratio]
      rw [div_eq_mul_inv]
      group
      exact mul_comm y x

/-- For two scalars of the same valuation, Beli's square-class congruence
modulo `𝔭^r` is exactly the relative-defect bound used in condition 3.1(iii).
This is the converse as well as the forward implication above. -/
theorem unitsCongruentModulo_powerIdeal_iff_natCast_le_defectOrder_mul
    (x y : Kˣ) (r : Nat) (horder : ordUnit K x = ordUnit K y) :
    UnitsCongruentModulo x y
        (Lattice.powerIdeal (K := K) (r : Int)) ↔
      ((((r : Nat) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (x * y)) := by
  constructor
  · exact natCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      x y r horder
  · intro hdefect
    let ratio : Kˣ := y / x
    have hratioOrder : ordUnit K ratio = 0 := by
      dsimp only [ratio]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, horder]
      omega
    have hproduct : ratio * x ^ 2 = x * y := by
      dsimp only [ratio]
      rw [div_eq_mul_inv]
      group
      exact mul_comm y x
    have hratioDefect :
        ((((r : Nat) : ℚ) : WithTop ℚ) ≤ defectOrder (K := K) ratio) := by
      rw [← defectOrder_mul_square ratio x, hproduct]
      exact hdefect
    have happroximation : IsQuadraticApproximation K ratio r :=
      (isQuadraticApproximation_iff_le_defect K).2
        ((natCast_le_defectOrder_iff ratio r).1 hratioDefect)
    by_cases hr : r = 0
    · subst r
      refine ⟨1, ?_⟩
      have hmem : (ratio : K) - 1 ∈
          Lattice.powerIdeal (K := K) (0 : Int) := by
        rw [Lattice.mem_powerIdeal_iff]
        have hsum := min_ord_le_ord_add K (ratio : K) (-1 : K)
        rw [← coe_ordUnit, hratioOrder, ord_neg, ord_one] at hsum
        simpa [sub_eq_add_neg] using hsum
      simpa only [ratio, Units.val_div_eq_div_val, Units.val_one,
        one_pow, div_one, Nat.cast_zero, Int.ofNat_eq_natCast] using hmem
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      rcases happroximation with ⟨z, hz⟩
      let t : K := z ^ 2 / (ratio : K)
      have hzNe : z ≠ 0 := by
        intro hzZero
        subst z
        have hzero : ((r : Int) : WithTop Int) ≤ 0 := by
          simpa [t] using hz
        have hpos : (0 : WithTop Int) < (r : Int) := by
          exact_mod_cast hrpos
        exact (not_lt_of_ge hzero) hpos
      have herrorPos : (0 : WithTop Int) < ord K (1 - t) := by
        have hpos : (0 : WithTop Int) < (r : Nat) := by
          exact_mod_cast hrpos
        exact hpos.trans_le (by simpa only [t] using hz)
      have htOrder : ord K t = 0 := by
        have hlt : ord K (1 : K) < ord K (1 - t) := by
          simpa only [ord_one] using herrorPos
        have hsub := (ord K).map_sub_eq_of_lt_left hlt
        have honeSub : (1 : K) - (1 - t) = t := by ring
        rw [honeSub] at hsub
        simpa only [ord_one] using hsub
      have htNe : t ≠ 0 := by
        dsimp only [t]
        exact div_ne_zero (pow_ne_zero 2 hzNe) (Units.ne_zero ratio)
      let s : Kˣ := Units.mk0 z hzNe
      refine ⟨s, ?_⟩
      rw [Lattice.mem_powerIdeal_iff]
      have hnormalized :
          (ratio : K) / (s : K) ^ 2 - 1 = (1 - t) / t := by
        change (ratio : K) / z ^ 2 - 1 =
          (1 - z ^ 2 / (ratio : K)) / (z ^ 2 / (ratio : K))
        field_simp [Units.ne_zero ratio, hzNe]
      have hzInt : ((r : Int) : WithTop Int) ≤ ord K (1 - t) := by
        exact_mod_cast (by simpa only [t] using hz)
      have hgoal : ((r : Int) : WithTop Int) ≤
          ord K ((ratio : K) / (s : K) ^ 2 - 1) := by
        rw [hnormalized, div_eq_mul_inv, ord_mul,
          AddValuation.map_inv, htOrder]
        simpa using hzInt
      simpa only [ratio, Units.val_div_eq_div_val] using hgoal

/-- Integral-exponent form of
`natCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal`. -/
theorem intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
    (x y : Kˣ) (r : Int) (hr : 0 ≤ r)
    (horder : ordUnit K x = ordUnit K y)
    (hcongruent : UnitsCongruentModulo x y
      (Lattice.powerIdeal (K := K) r)) :
    ((((r : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (x * y)) := by
  have hnat :=
    natCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      x y r.toNat horder (by
        simpa only [Int.toNat_of_nonneg hr] using hcongruent)
  convert hnat using 1
  norm_cast
  exact (Int.toNat_of_nonneg hr).symm

/-- Integral-exponent equivalence between square-class congruence and the
relative quadratic-defect bound. -/
theorem unitsCongruentModulo_powerIdeal_iff_intCast_le_defectOrder_mul
    (x y : Kˣ) (r : Int) (hr : 0 ≤ r)
    (horder : ordUnit K x = ordUnit K y) :
    UnitsCongruentModulo x y (Lattice.powerIdeal (K := K) r) ↔
      ((((r : Int) : ℚ) : WithTop ℚ) ≤
        defectOrder (K := K) (x * y)) := by
  have hnat :=
    unitsCongruentModulo_powerIdeal_iff_natCast_le_defectOrder_mul
      x y r.toNat horder
  have hpow : (r.toNat : Int) = r := Int.toNat_of_nonneg hr
  have hcast : (r.toNat : ℚ) = (r : ℚ) := by exact_mod_cast hpow
  rw [hpow, hcast] at hnat
  exact hnat

/-- Checked Jordan-chain data used in the reduction of Lemma 3.3.  There
are `t + 1` Jordan components and `t` boundaries. -/
structure JordanClassificationReduction
    (a : GoodBONG q L (N + 1)) (b : GoodBONG s M (N + 1))
    (t : Nat) where
  componentA : Fin (t + 1) → Kˣ
  componentB : Fin (t + 1) → Kˣ
  componentWeight : Fin (t + 1) → Lattice.OrderedFractionalIdeal K
  isUnary : Fin (t + 1) → Prop
  boundaryIndex : Fin t → Fin N
  boundaryIdeal : Fin t → Lattice.OrderedFractionalIdeal K
  headIndex : (k : Fin (t + 1)) → ¬isUnary k → Fin N

namespace JordanClassificationReduction

variable {a : GoodBONG q L (N + 1)} {b : GoodBONG s M (N + 1)}
  {t : Nat}

def prefixCondition (_J : JordanClassificationReduction a b t)
    (i : Fin N) : Prop :=
  (a.alphaValue i : WithTop ℚ) <=
    comparisonPrefixDefect a b (i.1 + 1)

def componentCongruence (J : JordanClassificationReduction a b t)
    (k : Fin (t + 1)) : Prop :=
  UnitsCongruentModulo (J.componentA k) (J.componentB k)
    (J.componentWeight k).carrier

def boundaryCongruence (J : JordanClassificationReduction a b t)
    (k : Fin t) : Prop :=
  UnitsCongruentModulo
    (a.prefixProduct ((J.boundaryIndex k).1 + 1))
    (b.prefixProduct ((J.boundaryIndex k).1 + 1))
    (J.boundaryIdeal k).carrier

theorem allPrefixConditions_iff
    (J : JordanClassificationReduction a b t) :
    (∀ i, J.prefixCondition i) ↔ a.PrefixDefectBounds b := by
  rfl

end JordanClassificationReduction

/-- The local Jordan-chain reductions in the proof of Lemma 3.3.  This
interface has no default instance. -/
class Beli2009JordanReductionLaws
    {a : GoodBONG q L (N + 1)} {b : GoodBONG s M (N + 1)} {t : Nat}
    (J : JordanClassificationReduction a b t) : Prop where
  boundary_iff (k : Fin t) :
    J.prefixCondition (J.boundaryIndex k) ↔ J.boundaryCongruence k
  /-- After the boundary instances of O'Meara 93:28(i) have been fixed, the
  non-unary component congruence is equivalent to the prefix condition at
  its first BONG coordinate. -/
  nonUnary_iff
    (hboundaries : ∀ j, J.prefixCondition (J.boundaryIndex j))
    (k : Fin (t + 1)) (hk : ¬J.isUnary k) :
    J.prefixCondition (J.headIndex k hk) ↔ J.componentCongruence k
  /-- In the unary case the component congruence is obtained from the
  adjacent prefix conditions (and, at the terminal endpoint, from the full
  determinant square class).  It is not an assumption-free local fact. -/
  unary_component
    (hall : ∀ i, J.prefixCondition i) (k : Fin (t + 1)) :
    J.isUnary k → J.componentCongruence k
  covers :
    (∀ k, J.prefixCondition (J.boundaryIndex k)) →
      (∀ (k : Fin (t + 1)) (hk : ¬J.isUnary k),
        J.prefixCondition (J.headIndex k hk)) →
      ∀ i, J.prefixCondition i

namespace JordanClassificationReduction

variable {a : GoodBONG q L (N + 1)} {b : GoodBONG s M (N + 1)}
  {t : Nat} (J : JordanClassificationReduction a b t)
  [Beli2009JordanReductionLaws J]

/-- Beli (2009/2010), Lemma 3.3. -/
theorem beli2009Lemma33 :
    a.PrefixDefectBounds b ↔
      (∀ k, J.componentCongruence k) ∧
        (∀ k, J.boundaryCongruence k) := by
  rw [← J.allPrefixConditions_iff]
  constructor
  · intro hall
    have hboundarySeeds : ∀ j, J.prefixCondition (J.boundaryIndex j) :=
      fun j ↦ hall (J.boundaryIndex j)
    constructor
    · intro k
      by_cases hk : J.isUnary k
      · exact Beli2009JordanReductionLaws.unary_component hall k hk
      · exact (Beli2009JordanReductionLaws.nonUnary_iff
          hboundarySeeds k hk).1
          (hall (J.headIndex k hk))
    · intro k
      exact (Beli2009JordanReductionLaws.boundary_iff k).1
        (hall (J.boundaryIndex k))
  · rintro ⟨hcomponents, hboundaries⟩
    have hboundarySeeds : ∀ j, J.prefixCondition (J.boundaryIndex j) :=
      fun j ↦ (Beli2009JordanReductionLaws.boundary_iff j).2
        (hboundaries j)
    apply Beli2009JordanReductionLaws.covers
    · exact hboundarySeeds
    · intro k hk
      exact (Beli2009JordanReductionLaws.nonUnary_iff
        hboundarySeeds k hk).2
        (hcomponents k)

end JordanClassificationReduction

end BONG.GoodBONG

end Bong
