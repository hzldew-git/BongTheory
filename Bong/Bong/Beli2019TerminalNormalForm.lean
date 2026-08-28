/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Ordinary

/-!
# Beli (2019), terminal form of Lemma 2.7(i)

Definition 4 replaces the nonexistent last target order by the combined
quantity `S_(n+2) + A_(n+2)`.  Its optional second candidate admits the same
prefix-defect replacement as Lemma 2.7(i).
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

/-- The replacement form of Definition 4's optional terminal candidate. -/
noncomputable def terminalAdjustedSecondaryPrevious
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hinner : n + 3 < m + 1) : WithTop ℚ :=
  (((a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 3, hinner⟩ -
      b.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
    a.truncatedPrefixDefect b (-1) (n + 2) n

/-- With the terminal cross inequality, the primary candidate lies below
the shifted adjacent source defect used for replacement. -/
theorem terminalAdjustedPrimary_le_secondaryAdjacentCut
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (hinner : n + 3 < m + 1)
    (hcross : b.order ⟨n, by omega⟩ ≤ a.order ⟨n + 2, hgap⟩) :
    a.terminalAdjustedPrimary b hgap ≤
      (((a.order ⟨n + 2, hgap⟩ + a.order ⟨n + 3, hinner⟩ -
        b.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (n + 2) (n + 4) := by
  let p : Fin m := ⟨n + 2, by omega⟩
  let primaryShift : ℚ := (a.order ⟨n + 2, hgap⟩ : ℚ)
  let adjacentShift : ℚ :=
    ((a.order ⟨n + 3, hinner⟩ - a.order ⟨n + 2, hgap⟩ : Int) : ℚ)
  let secondaryShift : ℚ :=
    ((a.order ⟨n + 2, hgap⟩ + a.order ⟨n + 3, hinner⟩ -
      b.order ⟨n, by omega⟩ : Int) : ℚ)
  have hcap : a.truncatedPrefixDefect b (-1) (n + 3) (n + 1) ≤
      (a.alphaValue p : WithTop ℚ) := by
    have h := a.truncatedPrefixDefect_le_leftCap b (-1) (n + 3) (n + 1)
    rw [a.prefixAlphaCap_of_internal (by omega) hinner] at h
    have hindex : (⟨n + 3 - 1, by omega⟩ : Fin m) = p := by
      apply Fin.ext
      change n + 3 - 1 = n + 2
      omega
    rw [hindex] at h
    exact h
  have hprimary : a.terminalAdjustedPrimary b hgap ≤
      (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := by
    unfold terminalAdjustedPrimary
    simpa only [primaryShift] using
      (add_le_add_right hcap (primaryShift : WithTop ℚ))
  have hadjacent : (a.alphaValue p : WithTop ℚ) ≤
      (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (n + 2) (n + 4) := by
    have h := a.alpha_le_orderGap_add_cappedAdjacent p
    have hsucc : p.succ = (⟨n + 3, hinner⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    have hcast : p.castSucc = (⟨n + 2, hgap⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at h
    simpa only [adjacentShift, p, Fin.val_mk] using h
  have hshifts : primaryShift + adjacentShift ≤ secondaryShift := by
    dsimp only [primaryShift, adjacentShift, secondaryShift]
    push_cast
    norm_cast at hcross ⊢
    linarith
  have hshiftsTop : ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) ≤
      (secondaryShift : WithTop ℚ) := by
    exact_mod_cast hshifts
  calc
    a.terminalAdjustedPrimary b hgap ≤
        (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) :=
      hprimary
    _ ≤ (primaryShift : WithTop ℚ) +
        ((adjacentShift : WithTop ℚ) +
          a.truncatedPrefixDefect a (-1) (n + 2) (n + 4)) :=
      add_le_add_right hadjacent _
    _ = ((primaryShift + adjacentShift : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (n + 2) (n + 4) := by
      norm_num [add_assoc]
    _ ≤ (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (n + 2) (n + 4) :=
      add_le_add_left hshiftsTop _

/-- The optional terminal candidate can be replaced by the preceding central
defect inside the minimum with the primary candidate. -/
theorem terminalAdjustedSecondary_replace_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (hinner : n + 3 < m + 1)
    (hcross : b.order ⟨n, by omega⟩ ≤ a.order ⟨n + 2, hgap⟩) :
    min (a.terminalAdjustedSecondary b hinner)
        (a.terminalAdjustedPrimary b hgap) =
      min (a.terminalAdjustedSecondaryPrevious b hinner)
        (a.terminalAdjustedPrimary b hgap) := by
  let shift : ℚ :=
    ((a.order ⟨n + 2, hgap⟩ + a.order ⟨n + 3, hinner⟩ -
      b.order ⟨n, by omega⟩ : Int) : ℚ)
  have hcut := a.terminalAdjustedPrimary_le_secondaryAdjacentCut
    b hgap hinner hcross
  have hreplace := a.shiftedTruncatedPrefixDefect_add_two_replace_of_cut_le
    b (n + 2) n shift (a.terminalAdjustedPrimary b hgap)
      (by simpa only [shift] using hcut)
  simpa only [terminalAdjustedSecondary,
    terminalAdjustedSecondaryPrevious, shift] using hreplace

/-- With its optional candidate present, the exceptional terminal value is
the minimum of the primary and preceding-defect forms. -/
theorem terminalAdjustedAlpha_eq_min_primary_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (hinner : n + 3 < m + 1)
    (hcross : b.order ⟨n, by omega⟩ ≤ a.order ⟨n + 2, hgap⟩) :
    a.terminalAdjustedAlpha b hgap =
      min (a.terminalAdjustedPrimary b hgap)
        (a.terminalAdjustedSecondaryPrevious b hinner) := by
  have hnormal : a.terminalAdjustedAlpha b hgap =
      min (a.terminalAdjustedPrimary b hgap)
        (a.terminalAdjustedSecondary b hinner) := by
    unfold terminalAdjustedAlpha
    apply le_antisymm
    · apply le_min
      · exact a.terminalAdjustedAlpha_le_primary b hgap
      · exact a.terminalAdjustedAlpha_le_secondary b hgap hinner
    · apply Finset.le_min'
      intro x hx
      simp [terminalAdjustedCandidates, hinner] at hx
      rcases hx with rfl | rfl
      · exact min_le_left _ _
      · exact min_le_right _ _
  rw [hnormal, min_comm (a.terminalAdjustedPrimary b hgap),
    a.terminalAdjustedSecondary_replace_previous b hgap hinner hcross,
    min_comm (a.terminalAdjustedSecondaryPrevious b hinner)]

/-- If the optional source term is absent, Definition 4 has only its primary
terminal candidate. -/
theorem terminalAdjustedAlpha_eq_primary_of_not_inner
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (hinner : ¬n + 3 < m + 1) :
    a.terminalAdjustedAlpha b hgap =
      a.terminalAdjustedPrimary b hgap := by
  unfold terminalAdjustedAlpha
  apply le_antisymm
  · exact a.terminalAdjustedAlpha_le_primary b hgap
  · apply Finset.le_min'
    intro x hx
    simp [terminalAdjustedCandidates, hinner] at hx
    simp [hx]

end BONG.GoodBONG

end Bong
