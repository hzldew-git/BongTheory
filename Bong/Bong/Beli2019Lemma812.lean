/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlphaLocalFormula
import Bong.Bong.Beli2019Lemma27
import Bong.Bong.Beli2019TerminalNormalForm

/-!
# Beli (2019), Lemma 8.12

When the first target and source orders agree, the first two representation
invariants have especially simple formulas.  This file records the paper's
auxiliary invariant `α'_i`, proves the first-boundary identities, and removes
the optional secondary term at the second boundary (including the rank-one
terminal case).
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

/-- Beli (2019), Definition 5: the lattice invariant
`α'_i = R_(i+1) - R_i + d[-a_(1,i)a_(1,i+1)]`.

The index convention in Lean is zero-based, so the two prefix lengths in the
bracketed defect are `i` and `i + 2`. -/
noncomputable def alphaPrime (a : GoodBONG q L (n + 1)) (i : Fin n) :
    WithTop ℚ :=
  (((((a.order i.succ - a.order i.castSucc : Int) : ℚ)) :
      WithTop ℚ) +
    a.truncatedPrefixDefect a (-1) i.val (i.val + 2))

/-- Remark 1.1 rewritten with the named invariant `α'_i`. -/
theorem alpha_eq_min_halfGap_alphaPrime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    (a.alphaValue i : WithTop ℚ) =
      min (a.halfGapCandidate i) (a.alphaPrime i) := by
  simpa only [alphaPrime] using
    a.alpha_eq_min_halfGap_add_cappedAdjacent i

/-- The first ordinary representation index. -/
def firstRepresentationIndex (largeTail smallTail : Nat) :
    RepresentationIndex (largeTail + 2) (smallTail + 1) where
  val := 1
  pos := by omega
  lt_large := by omega
  le_small := by omega

/-- At the first boundary the cross-lattice capped defect is the target's
first adjacent capped defect: the source contributes only its empty prefix. -/
theorem firstRepresentationDefect_eq_adjacent
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 1)) :
    a.truncatedPrefixDefect b (-1) 2 0 =
      a.truncatedPrefixDefect a (-1) 0 2 := by
  unfold truncatedPrefixDefect
  rw [show a.prefixProduct 0 = 1 by
        exact a.toBONG.prefixProduct_zero,
    show b.prefixProduct 0 = 1 by
        exact b.toBONG.prefixProduct_zero,
    a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
  simp only [mul_one]
  simp [min_comm]

/-- Lemma 8.12(i), the auxiliary identity `A'_1 = α'_1`. -/
theorem beli2019Lemma812_i_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 1))
    (hfirst : a.order (0 : Fin (m + 2)) =
      b.order (0 : Fin (n + 1))) :
    a.representationAlphaPrime b (firstRepresentationIndex m n) =
      a.alphaPrime (0 : Fin (m + 1)) := by
  rw [a.representationAlphaPrime_eq_primary_of_not_interior b
    (firstRepresentationIndex m n) (by
      simp [firstRepresentationIndex])]
  unfold representationPrimaryDefect alphaPrime
  change
    (((((a.order (1 : Fin (m + 2)) - b.order (0 : Fin (n + 1)) : Int) : ℚ)) :
        WithTop ℚ) + a.truncatedPrefixDefect b (-1) 2 0) =
      (((((a.order (1 : Fin (m + 2)) - a.order (0 : Fin (m + 2)) : Int) : ℚ)) :
        WithTop ℚ) + a.truncatedPrefixDefect a (-1) 0 2)
  rw [a.firstRepresentationDefect_eq_adjacent b]
  rw [← hfirst]

/-- Lemma 8.12(i), the identity `A_1 = α_1`. -/
theorem beli2019Lemma812_i
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 1))
    (hfirst : a.order (0 : Fin (m + 2)) =
      b.order (0 : Fin (n + 1))) :
    a.representationAlpha b (firstRepresentationIndex m n) =
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) := by
  rw [a.representationAlpha_eq_min_halfGap_prime b
    (firstRepresentationIndex m n),
    a.beli2019Lemma812_i_prime b hfirst,
    a.alpha_eq_min_halfGap_alphaPrime (0 : Fin (m + 1))]
  unfold representationHalfGap halfGapCandidate
  simp [firstRepresentationIndex, ← hfirst]

/-- The second ordinary representation index. -/
def secondRepresentationIndex (largeTail smallTail : Nat) :
    RepresentationIndex (largeTail + 3) (smallTail + 2) where
  val := 2
  pos := by omega
  lt_large := by omega
  le_small := by omega

/-- Goodness gives the endpoint comparison `R_1 ≤ R_3`. -/
theorem order_zero_le_two (a : GoodBONG q L (m + 3)) :
    a.order (⟨0, by omega⟩ : Fin (m + 3)) ≤
      a.order (⟨2, by omega⟩ : Fin (m + 3)) := by
  let first : Fin (m + 3) := ⟨0, by omega⟩
  have hgood := a.good first (by simp [first])
  change a.order first ≤
    a.order (⟨first.val + 2, by simp [first]⟩ : Fin (m + 3)) at hgood
  simpa only [first, Nat.zero_add] using hgood

set_option maxHeartbeats 600000 in
/-- The inequality in the middle of the proof of Lemma 8.12(ii):
`S_1 - R_4 + d[-a_(1,3)b_1] ≤ d[-a_(1,2)]`.

This target-order form becomes the paper's `S_1 - R_4` form after applying
the hypothesis `S_1 = R_1`.  The proof is exactly the paper's chain: cap the first defect by `α_3`, use
the antitonicity of `-R_(i+1) + α_i`, and finish with Remark 1.1. -/
theorem firstThirdCappedDefect_shift_le_firstAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 4)) (b : GoodBONG r M (n + 1)) :
    (((((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ)) :
        WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1) ≤
      a.truncatedPrefixDefect b (-1) 2 0 := by
  let first : Fin (m + 3) := ⟨0, by omega⟩
  let third : Fin (m + 3) := ⟨2, by omega⟩
  have hthird : a.truncatedPrefixDefect b (-1) 3 1 ≤
      (a.alphaValue third : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1) 3 1
    rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
    simpa only [third] using hcap
  let shift03 : WithTop ℚ :=
    (((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ) :
      WithTop ℚ)
  have hthirdShift :
      shift03 + a.truncatedPrefixDefect b (-1) 3 1 ≤
        shift03 + (a.alphaValue third : WithTop ℚ) := by
    simpa only [add_comm] using add_le_add_right hthird shift03
  have hendpointRaw := a.alphaRightEndpoint_antitone
    (show first ≤ third by simp [first, third])
  have hfirstSucc : first.succ = (1 : Fin (m + 4)) := by
    apply Fin.ext
    rfl
  have hthirdSucc : third.succ = (3 : Fin (m + 4)) := by
    apply Fin.ext
    rfl
  unfold alphaRightEndpoint at hendpointRaw
  rw [hfirstSucc, hthirdSucc] at hendpointRaw
  have hendpoint :
      (((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ) +
          a.alphaValue third) ≤
        (((a.order (0 : Fin (m + 4)) - a.order (1 : Fin (m + 4)) : Int) : ℚ) +
          a.alphaValue first) := by
    dsimp only [first, third] at hendpointRaw ⊢
    push_cast at hendpointRaw ⊢
    linarith
  have hendpointTop :
      (((((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + (a.alphaValue third : WithTop ℚ)) ≤
        (((((a.order (0 : Fin (m + 4)) - a.order (1 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + (a.alphaValue first : WithTop ℚ)) := by
    exact_mod_cast hendpoint
  have hadjacent := a.order_sub_add_alpha_le_cappedAdjacent first
  have hadjacent' :
      (((((a.order (0 : Fin (m + 4)) - a.order (1 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + (a.alphaValue first : WithTop ℚ)) ≤
        a.truncatedPrefixDefect b (-1) 2 0 := by
    rw [a.firstRepresentationDefect_eq_adjacent b]
    simpa [first] using hadjacent
  calc
    (((((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1) ≤
        (((((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + (a.alphaValue third : WithTop ℚ)) :=
      by simpa only [shift03] using hthirdShift
    _ ≤ (((((a.order (0 : Fin (m + 4)) - a.order (1 : Fin (m + 4)) : Int) : ℚ)) :
          WithTop ℚ) + (a.alphaValue first : WithTop ℚ)) := hendpointTop
    _ ≤ a.truncatedPrefixDefect b (-1) 2 0 := hadjacent'

/-- The explicit primary term in Lemma 8.12(ii):
`R_3 - S_2 + d[-a_(1,3)b_1]`. -/
noncomputable def secondRepresentationPrimaryFormula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2)) :
    WithTop ℚ :=
  (((((a.order (2 : Fin (m + 3)) - b.order (1 : Fin (n + 2)) : Int) : ℚ)) :
      WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1)

/-- The explicit half-gap term in Lemma 8.12(ii):
`(R_3 - S_2) / 2 + e`. -/
noncomputable def secondRepresentationHalfGapFormula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2)) :
    WithTop ℚ :=
  (((a.order (2 : Fin (m + 3)) - b.order (1 : Fin (n + 2)) : Int) : ℚ) /
      2 + (ramificationIndex K : ℚ) : ℚ)

set_option maxHeartbeats 600000 in
/-- After the Lemma 2.7(i) replacement, the primary second-boundary term is
no larger than the optional secondary term. -/
theorem secondRepresentationPrimary_le_secondaryPrevious
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 4)) (b : GoodBONG r M (n + 2))
    (hfirst : a.order (0 : Fin (m + 4)) =
      b.order (0 : Fin (n + 2))) :
    a.representationPrimaryDefect b (secondRepresentationIndex (m + 1) n) ≤
      a.representationSecondaryPreviousDefect b
        (secondRepresentationIndex (m + 1) n) (by
          simp [secondRepresentationIndex]) := by
  let i := secondRepresentationIndex (m + 1) n
  let secondaryShift : WithTop ℚ :=
    (((a.order (2 : Fin (m + 4)) + a.order (3 : Fin (m + 4)) -
      b.order (0 : Fin (n + 2)) - b.order (1 : Fin (n + 2)) : Int) : ℚ) :
        WithTop ℚ)
  let firstShift : WithTop ℚ :=
    (((a.order (0 : Fin (m + 4)) - a.order (3 : Fin (m + 4)) : Int) : ℚ) :
      WithTop ℚ)
  let primaryShift : WithTop ℚ :=
    (((a.order (2 : Fin (m + 4)) - b.order (1 : Fin (n + 2)) : Int) : ℚ) :
      WithTop ℚ)
  have hdefect := a.firstThirdCappedDefect_shift_le_firstAdjacent b
  have hshifted :
      secondaryShift + (firstShift + a.truncatedPrefixDefect b (-1) 3 1) ≤
        secondaryShift + a.truncatedPrefixDefect b (-1) 2 0 :=
    by
      dsimp only [firstShift]
      simpa only [add_comm] using add_le_add_left hdefect secondaryShift
  have hshiftEq : secondaryShift + firstShift = primaryShift := by
    dsimp only [secondaryShift, firstShift, primaryShift]
    norm_cast
    rw [← hfirst]
    ring
  change primaryShift + a.truncatedPrefixDefect b (-1) 3 1 ≤
    secondaryShift + a.truncatedPrefixDefect b (-1) 2 0
  calc
    primaryShift + a.truncatedPrefixDefect b (-1) 3 1 =
        (secondaryShift + firstShift) +
          a.truncatedPrefixDefect b (-1) 3 1 := by rw [hshiftEq]
    _ = secondaryShift +
        (firstShift + a.truncatedPrefixDefect b (-1) 3 1) := add_assoc _ _ _
    _ ≤ secondaryShift + a.truncatedPrefixDefect b (-1) 2 0 := hshifted

@[simp]
theorem representationPrimaryDefect_second_eq_formula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2)) :
    a.representationPrimaryDefect b (secondRepresentationIndex m n) =
      a.secondRepresentationPrimaryFormula b := by
  rfl

@[simp]
theorem representationHalfGap_second_eq_formula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2)) :
    a.representationHalfGap b (secondRepresentationIndex m n) =
      a.secondRepresentationHalfGapFormula b := by
  rfl

set_option maxHeartbeats 600000 in
/-- Lemma 8.12(ii), for a source of rank at least two:
`A'_2 = R_3 - S_2 + d[-a_(1,3)b_1]`. -/
theorem beli2019Lemma812_ii_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hfirst : a.order (0 : Fin (m + 3)) =
      b.order (0 : Fin (n + 2))) :
    a.representationAlphaPrime b (secondRepresentationIndex m n) =
      a.secondRepresentationPrimaryFormula b := by
  cases m with
  | zero =>
      rw [a.representationAlphaPrime_eq_primary_of_not_interior b
        (secondRepresentationIndex 0 n) (by
          simp [secondRepresentationIndex])]
      rfl
  | succ k =>
      have hi :
          1 < (secondRepresentationIndex (k + 1) n).val ∧
            (secondRepresentationIndex (k + 1) n).val + 1 < k + 1 + 3 := by
        simp [secondRepresentationIndex]
      have hcross :
          b.order ⟨(secondRepresentationIndex (k + 1) n).val - 2,
            by have := (secondRepresentationIndex (k + 1) n).le_small; omega⟩ ≤
            a.order ⟨(secondRepresentationIndex (k + 1) n).val,
              (secondRepresentationIndex (k + 1) n).lt_large⟩ := by
        have hsource :
            (⟨(secondRepresentationIndex (k + 1) n).val - 2,
              by have := (secondRepresentationIndex (k + 1) n).le_small; omega⟩ :
                Fin (n + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          rfl
        have htarget :
            (⟨(secondRepresentationIndex (k + 1) n).val,
              (secondRepresentationIndex (k + 1) n).lt_large⟩ :
                Fin (k + 1 + 3)) = ⟨2, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hsource, htarget]
        exact hfirst ▸ a.order_zero_le_two
      rw [a.representationAlphaPrime_eq_min_primary_previous b
          (secondRepresentationIndex (k + 1) n) hi hcross,
        min_eq_left]
      · rfl
      · exact a.secondRepresentationPrimary_le_secondaryPrevious b hfirst

/-- Lemma 8.12(ii), for a source of rank at least two:
`A_2` is the minimum of the stated half-gap and primary terms. -/
theorem beli2019Lemma812_ii
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hfirst : a.order (0 : Fin (m + 3)) =
      b.order (0 : Fin (n + 2))) :
    a.representationAlpha b (secondRepresentationIndex m n) =
      min (a.secondRepresentationHalfGapFormula b)
        (a.secondRepresentationPrimaryFormula b) := by
  rw [a.representationAlpha_eq_min_halfGap_prime b
      (secondRepresentationIndex m n),
    a.beli2019Lemma812_ii_prime b hfirst,
    a.representationHalfGap_second_eq_formula b]

/-- The explicit terminal quantity in the rank-one part of Lemma 8.12(ii):
`R_3 + d[-a_(1,3)b_1]`. -/
noncomputable def terminalSecondPrimaryFormula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M 1) : WithTop ℚ :=
  (((a.order (⟨2, by omega⟩ : Fin (m + 3)) : Int) : ℚ) : WithTop ℚ) +
    a.truncatedPrefixDefect b (-1) 3 1

@[simp]
theorem terminalAdjustedPrimary_zero_eq_formula
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M 1)
    (hgap : 0 + 2 < m + 3) :
    a.terminalAdjustedPrimary b hgap = a.terminalSecondPrimaryFormula b := by
  rfl

set_option maxHeartbeats 600000 in
/-- In the rank-one terminal case, the primary term is no larger than the
optional preceding-defect term. -/
theorem terminalSecondPrimary_le_secondaryPrevious
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 4)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 4)) = b.order (0 : Fin 1))
    (hgap : 0 + 2 < m + 4) (hinner : 0 + 3 < m + 4) :
    a.terminalAdjustedPrimary b hgap ≤
      a.terminalAdjustedSecondaryPrevious b hinner := by
  let secondaryShift : WithTop ℚ :=
    (((a.order (⟨2, by omega⟩ : Fin (m + 4)) +
      a.order (⟨3, by omega⟩ : Fin (m + 4)) -
      b.order (0 : Fin 1) : Int) : ℚ) : WithTop ℚ)
  let firstShift : WithTop ℚ :=
    (((a.order (0 : Fin (m + 4)) -
      a.order (⟨3, by omega⟩ : Fin (m + 4)) : Int) : ℚ) : WithTop ℚ)
  let primaryShift : WithTop ℚ :=
    ((a.order (⟨2, by omega⟩ : Fin (m + 4)) : Int) : ℚ)
  have hdefect := a.firstThirdCappedDefect_shift_le_firstAdjacent b
  have hthree : (3 : Fin (m + 4)) = ⟨3, hinner⟩ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt hinner]
  rw [hthree] at hdefect
  have hshifted :
      secondaryShift + (firstShift + a.truncatedPrefixDefect b (-1) 3 1) ≤
        secondaryShift + a.truncatedPrefixDefect b (-1) 2 0 := by
    dsimp only [firstShift]
    simpa only [add_comm] using add_le_add_left hdefect secondaryShift
  have hshiftEq : secondaryShift + firstShift = primaryShift := by
    dsimp only [secondaryShift, firstShift, primaryShift]
    norm_cast
    rw [← hfirst]
    ring
  change primaryShift + a.truncatedPrefixDefect b (-1) 3 1 ≤
    secondaryShift + a.truncatedPrefixDefect b (-1) 2 0
  calc
    primaryShift + a.truncatedPrefixDefect b (-1) 3 1 =
        (secondaryShift + firstShift) +
          a.truncatedPrefixDefect b (-1) 3 1 := by rw [hshiftEq]
    _ = secondaryShift +
        (firstShift + a.truncatedPrefixDefect b (-1) 3 1) := add_assoc _ _ _
    _ ≤ secondaryShift + a.truncatedPrefixDefect b (-1) 2 0 := hshifted

set_option maxHeartbeats 600000 in
/-- Lemma 8.12(ii), rank-one source case:
`S_2 + A_2 = R_3 + d[-a_(1,3)b_1]`.

`terminalAdjustedAlpha` is Definition 4's Lean representation of the left
side `S_2 + A_2`. -/
theorem beli2019Lemma812_ii_rankOne
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 3)) = b.order (0 : Fin 1)) :
    a.terminalAdjustedAlpha b (by omega) =
      a.terminalSecondPrimaryFormula b := by
  cases m with
  | zero =>
      rw [a.terminalAdjustedAlpha_eq_primary_of_not_inner b
        (by omega) (by omega)]
      rfl
  | succ k =>
      have hgap : 0 + 2 < k + 1 + 3 := by omega
      have hinner : 0 + 3 < k + 1 + 3 := by omega
      have hcross :
          b.order (0 : Fin 1) ≤
            a.order (⟨2, hgap⟩ : Fin (k + 1 + 3)) := by
        exact hfirst ▸ a.order_zero_le_two
      rw [a.terminalAdjustedAlpha_eq_min_primary_previous b
          hgap hinner hcross,
        min_eq_left]
      · rfl
      · exact a.terminalSecondPrimary_le_secondaryPrevious b hfirst hgap hinner

end BONG.GoodBONG

end Bong
