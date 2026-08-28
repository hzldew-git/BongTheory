/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29SourceReduction

/-!
# Beli (2019), Lemma 2.9: the target-alpha reduction branch

For a positive secondary order shift, a secondary-previous candidate below
the comparison defect forces the target-adjacent defect below it.  Remark
1.1 then replaces that adjacent defect by the preceding target alpha.  This
is the target-side counterpart of `representationSecondarySourceAlpha`.
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

/-- The target-alpha candidate
`R_(i+1) + R_(i+2) - 2S_i + beta_(i-1)` in `overline A'_i`. -/
noncomputable def representationSecondaryTargetAlpha
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hi.2⟩ -
      2 * b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
    (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ)

set_option maxHeartbeats 400000 in
-- The proof mirrors the source branch with all three capped-prefix indices reversed.
/-- Target-alpha branch of Lemma 2.9.  The comparison defect is finite and
equal to `C`; positivity of the secondary coefficient makes the
secondary-previous defect strictly smaller than it. -/
theorem representationSecondaryTargetAlpha_le_of_previous_le_comparison
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hsmall : i.val < n + 1) (C : ℚ)
    (hprevious : a.representationSecondaryPreviousDefect b i hi ≤
      (C : WithTop ℚ))
    (hcomparison : (C : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    a.representationSecondaryTargetAlpha b i hi hsmall ≤
      (C : WithTop ℚ) := by
  let p : Fin n := ⟨i.val - 2, by omega⟩
  let currentShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      2 * b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ)
  let gap : ℚ :=
    ((b.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ : Int) : ℚ)
  let D := a.truncatedPrefixDefect b (-1) i.val (i.val - 2)
  let A := a.truncatedPrefixDefect b 1 i.val i.val
  let X := b.truncatedPrefixDefect b (-1) i.val (i.val - 2)
  change (currentShift : WithTop ℚ) + D ≤ (C : WithTop ℚ) at hprevious
  have hshiftQ : (0 : ℚ) < currentShift := by
    dsimp only [currentShift]
    exact_mod_cast hshift
  have hDne : D ≠ ⊤ := by
    intro htop
    rw [htop] at hprevious
    simp at hprevious
  have hDltC : D < (C : WithTop ℚ) := by
    rw [← WithTop.coe_untop D hDne] at hprevious ⊢
    norm_cast at hprevious ⊢
    linarith
  have hDltA : D < A := by
    exact hDltC.trans_le hcomparison
  have hdom := a.truncatedPrefixDefect_domination b b
    1 (-1) i.val i.val (i.val - 2)
  simp only [one_mul] at hdom
  have hmin : min A X ≤ D := by
    simpa only [A, X, D] using hdom
  have hXleD : X ≤ D := by
    by_cases hAX : A ≤ X
    · have hAleD : A ≤ D := by
        simpa only [min_eq_left hAX] using hmin
      exact False.elim ((not_le_of_gt hDltA) hAleD)
    · have hXA : X ≤ A := le_of_not_ge hAX
      simpa only [min_eq_right hXA] using hmin
  have halphaRaw := b.alpha_le_orderGap_add_cappedAdjacent p
  have hpSucc : p.succ =
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 2, by have := i.le_small; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hpSucc, hpCast] at halphaRaw
  have halpha : (b.alphaValue p : WithTop ℚ) ≤
      (gap : WithTop ℚ) + X := by
    calc
      (b.alphaValue p : WithTop ℚ) ≤
          (gap : WithTop ℚ) +
            b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
        simpa only [p, gap, show i.val - 2 + 2 = i.val by omega]
          using halphaRaw
      _ = (gap : WithTop ℚ) + X := by
        rw [b.truncatedPrefixDefect_comm b (-1) (i.val - 2) i.val]
  have hshifts : targetShift + gap = currentShift := by
    dsimp only [targetShift, gap, currentShift]
    push_cast
    ring
  change (targetShift : WithTop ℚ) +
      (b.alphaValue p : WithTop ℚ) ≤ (C : WithTop ℚ)
  calc
    (targetShift : WithTop ℚ) + (b.alphaValue p : WithTop ℚ) ≤
        (targetShift : WithTop ℚ) + ((gap : WithTop ℚ) + X) :=
      add_le_add_right halpha _
    _ = ((targetShift + gap : ℚ) : WithTop ℚ) + X := by
      norm_num [add_assoc]
    _ = (currentShift : WithTop ℚ) + X := by rw [hshifts]
    _ ≤ (currentShift : WithTop ℚ) + D := add_le_add_right hXleD _
    _ ≤ (C : WithTop ℚ) := hprevious

end BONG.GoodBONG

end Bong
