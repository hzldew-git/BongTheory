/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma27

/-!
# Beli (2019), Lemma 2.9: the source-alpha reduction branch

For a positive secondary order shift, a secondary-current candidate below
the comparison defect forces the source-adjacent defect below it.  Remark
1.1 then replaces that adjacent defect by the source alpha.  This is the
branch of Lemma 2.9 used in the type-III proof of Lemma 7.9(i).
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

/-- The source-alpha candidate
`2R_(i+1) - S_(i-1) - S_i + alpha_(i+1)` in `overline A'_i`. -/
noncomputable def representationSecondarySourceAlpha
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) : WithTop ℚ :=
  (((2 * a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    (a.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ)

set_option maxHeartbeats 400000 in
-- The nested `WithTop` normalization and four prefix indices need extra elaboration time.
/-- Special source-alpha branch of Lemma 2.9.  The comparison defect is
finite and equal to `C`; positivity of the secondary order coefficient
makes the secondary-current defect strictly smaller than it. -/
theorem representationSecondarySourceAlpha_le_of_current_le_comparison
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) (C : ℚ)
    (hcurrent : a.representationSecondaryCurrentDefect b i hi ≤
      (C : WithTop ℚ))
    (hcomparison : a.truncatedPrefixDefect b 1 i.val i.val =
      (C : WithTop ℚ))
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    a.representationSecondarySourceAlpha b i hi ≤ (C : WithTop ℚ) := by
  let p : Fin m := ⟨i.val, by omega⟩
  let currentShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ :=
    ((2 * a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let gap : ℚ :=
    ((a.order ⟨i.val + 1, hi.2⟩ -
      a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)
  let D := a.truncatedPrefixDefect b (-1) (i.val + 2) i.val
  let A := a.truncatedPrefixDefect b 1 i.val i.val
  let X := a.truncatedPrefixDefect a (-1) i.val (i.val + 2)
  change (currentShift : WithTop ℚ) + D ≤ (C : WithTop ℚ)
    at hcurrent
  have hshiftQ : (0 : ℚ) < currentShift := by
    dsimp only [currentShift]
    exact_mod_cast hshift
  have hDne : D ≠ ⊤ := by
    intro htop
    rw [htop] at hcurrent
    simp at hcurrent
  have hDltC : D < (C : WithTop ℚ) := by
    rw [← WithTop.coe_untop D hDne] at hcurrent ⊢
    norm_cast at hcurrent ⊢
    linarith
  have hDltA : D < A := by
    dsimp only [A]
    rw [hcomparison]
    exact hDltC
  have hdom := a.truncatedPrefixDefect_domination a b
    (-1) 1 (i.val + 2) i.val i.val
  rw [a.truncatedPrefixDefect_comm a (-1) (i.val + 2) i.val] at hdom
  simp only [mul_one] at hdom
  have hmin : min X A ≤ D := by simpa only [X, A, D] using hdom
  have hXleD : X ≤ D := by
    by_cases hXA : X ≤ A
    · simpa only [min_eq_left hXA] using hmin
    · have hAX : A ≤ X := le_of_not_ge hXA
      have hAleD : A ≤ D := by
        simpa only [min_eq_right hAX] using hmin
      exact False.elim ((not_le_of_gt hDltA) hAleD)
  have halphaRaw := a.alpha_le_orderGap_add_cappedAdjacent p
  have hpSucc : p.succ =
      (⟨i.val + 1, hi.2⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hpCast : p.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [hpSucc, hpCast] at halphaRaw
  have halpha : (a.alphaValue p : WithTop ℚ) ≤
      (gap : WithTop ℚ) + X := by
    simpa only [gap, X] using halphaRaw
  have hshifts : sourceShift + gap = currentShift := by
    dsimp only [sourceShift, gap, currentShift]
    push_cast
    ring
  change (sourceShift : WithTop ℚ) +
      (a.alphaValue p : WithTop ℚ) ≤ (C : WithTop ℚ)
  calc
    (sourceShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) ≤
        (sourceShift : WithTop ℚ) + ((gap : WithTop ℚ) + X) :=
      add_le_add_right halpha _
    _ = ((sourceShift + gap : ℚ) : WithTop ℚ) + X := by
      norm_num [add_assoc]
    _ = (currentShift : WithTop ℚ) + X := by rw [hshifts]
    _ ≤ (currentShift : WithTop ℚ) + D := add_le_add_right hXleD _
    _ ≤ (C : WithTop ℚ) := hcurrent

end BONG.GoodBONG

end Bong
