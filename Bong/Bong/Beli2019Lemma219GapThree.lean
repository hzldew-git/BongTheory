/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.Beli2019Corollary217
import Bong.Bong.DiagonalCodimensionTwoRepresentation

/-!
# Beli (2019), Lemma 2.19: the gap-three case

This is the nontrivial `l - j = 3` case of Lemma 2.19.  It is precisely the
form used throughout Sections 7 and 9: a source prefix of length `i - 1` is
represented by a target prefix of length `i + 1` as soon as
`R_(i+2) - S_(i-1) > 2e`.

If condition (iv) does not apply directly, the proof follows the two cases in
the paper.  In the exceptional negative-square determinant class, the common
capped defect is bounded below by the minimum of the two adjacent order gaps
and `2e`; Corollary 2.17 then activates condition (iii) at `i` or `i + 1`.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Every alpha invariant dominates the minimum of its order gap and `2e`.
This is the common numerical estimate used in Lemma 2.19. -/
theorem min_orderGap_twoE_le_alphaValue
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    min (a.orderGap i : ℚ) (2 * (ramificationIndex K : ℚ)) ≤
      a.alphaValue i := by
  rcases le_or_gt (a.orderGap i)
      (2 * (ramificationIndex K : Int)) with hle | hgt
  · rw [min_eq_left]
    · exact (a.alpha_p3 i hle).1
    · exact_mod_cast hle
  · rw [min_eq_right]
    · exact ((a.alpha_p5 i).2.2.mpr hgt).le
    · exact_mod_cast hgt.le

/-- The negative-square mixed prefix defect in Lemma 2.19 dominates the
minimum of the two adjacent gaps and the dyadic endpoint. -/
theorem lemma219_mixedDefect_lowerBound
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * b.prefixProduct (i.val - 1))) :
    ((min
        (min
          (a.orderGap ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ : ℚ)
          (b.orderGap ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩ : ℚ))
        (2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) := by
  have hraw : IsSquare
      ((-1 : Kˣ) * a.prefixProduct (i.val + 1) *
        b.prefixProduct (i.val - 1)) := by
    simpa only [neg_one_mul] using hsquare
  unfold truncatedPrefixDefect
  rw [defectOrder_eq_top_of_isSquare hraw,
    min_eq_right (show min (a.prefixAlphaCap (i.val + 1))
      (b.prefixAlphaCap (i.val - 1)) ≤ (⊤ : WithTop ℚ) from le_top)]
  rw [a.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.succ_lt_large,
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) (by
      have := i.succ_lt_large
      omega)]
  apply le_min
  · have hlow :
        min
            (min
              (a.orderGap ⟨i.val, by
                have := i.succ_lt_large
                omega⟩ : ℚ)
              (b.orderGap ⟨i.val - 2, by
                have := i.succ_lt_large
                omega⟩ : ℚ))
            (2 * (ramificationIndex K : ℚ)) ≤
          min (a.orderGap ⟨i.val, by
              have := i.succ_lt_large
              omega⟩ : ℚ)
            (2 * (ramificationIndex K : ℚ)) := by
      apply le_min
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact min_le_right _ _
    exact_mod_cast hlow.trans
      (a.min_orderGap_twoE_le_alphaValue (alpha := alphaV) ⟨i.val, by
        have := i.succ_lt_large
        omega⟩)
  · have hlow :
        min
            (min
              (a.orderGap ⟨i.val, by
                have := i.succ_lt_large
                omega⟩ : ℚ)
              (b.orderGap ⟨i.val - 2, by
                have := i.succ_lt_large
                omega⟩ : ℚ))
            (2 * (ramificationIndex K : ℚ)) ≤
          min (b.orderGap ⟨i.val - 2, by
              have := i.succ_lt_large
              omega⟩ : ℚ)
            (2 * (ramificationIndex K : ℚ)) := by
      apply le_min
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact min_le_right _ _
    exact_mod_cast hlow.trans
      (b.min_orderGap_twoE_le_alphaValue (alpha := alphaW) ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩)

/-- Beli (2019), Lemma 2.19 in its nontrivial `l - j = 3` form. -/
theorem beli2019Lemma219_gapThree
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [DyadicDiagonalCodimensionTwoLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hconditions : RepresentationConditions a b le_rfl)
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hstrict :
      b.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.succ_lt_large
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
  have hiOne := i.one_lt
  have hiLarge := i.succ_lt_large
  have hiSmall := i.le_small_succ
  by_cases hlong :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
          b.order ⟨i.val - 1, by
            have := i.succ_lt_large
            omega⟩ ∧
        a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ ≤
          b.order ⟨i.val - 2, by
            have := i.succ_lt_large
            omega⟩
  · apply hconditions.longRepresentations i
    refine ⟨?_, hstrict, ?_⟩
    · rw [dif_pos (show i.val ≤ n + 1 by omega)]
      exact hlong.1
    omega
  have hnotLong := hlong
  by_cases hsquare : IsSquare
      (-a.prefixProduct (i.val + 1) * b.prefixProduct (i.val - 1))
  · have hmixed := a.lemma219_mixedDefect_lowerBound
      (alphaV := alphaV) (alphaW := alphaW) b i hsquare
    have haGapDef : a.orderGap ⟨i.val, by omega⟩ =
        a.order ⟨i.val + 1, by omega⟩ - a.order ⟨i.val, by omega⟩ := by
      unfold orderGap
      have hsucc : (⟨i.val, by omega⟩ : Fin n).succ =
          ⟨i.val + 1, by omega⟩ := by
        ext
        rfl
      have hcast : (⟨i.val, by omega⟩ : Fin n).castSucc =
          ⟨i.val, by omega⟩ := by
        ext
        rfl
      rw [hsucc, hcast]
    have hbGapDef : b.orderGap ⟨i.val - 2, by omega⟩ =
        b.order ⟨i.val - 1, by omega⟩ -
          b.order ⟨i.val - 2, by omega⟩ := by
      unfold orderGap
      have hsucc : (⟨i.val - 2, by omega⟩ : Fin n).succ =
          ⟨i.val - 1, by omega⟩ := by
        ext
        simp only [Fin.val_succ]
        omega
      have hcast : (⟨i.val - 2, by omega⟩ : Fin n).castSucc =
          ⟨i.val - 2, by omega⟩ := by
        ext
        rfl
      rw [hsucc, hcast]
    rcases le_total
        (a.orderGap ⟨i.val, by omega⟩)
        (b.orderGap ⟨i.val - 2, by omega⟩) with hgap | hgap
    · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
        { val := i.val
          one_lt := i.one_lt
          lt_large := by omega
          le_small_succ := i.le_small_succ }
      have hgapExpanded :
          a.order ⟨i.val + 1, by omega⟩ - a.order ⟨i.val, by omega⟩ ≤
            b.order ⟨i.val - 1, by omega⟩ -
              b.order ⟨i.val - 2, by omega⟩ := by
        have hgapExpanded := hgap
        unfold orderGap at hgapExpanded
        have haSucc : (⟨i.val, by omega⟩ : Fin n).succ =
            ⟨i.val + 1, by omega⟩ := by
          ext
          rfl
        have haCast : (⟨i.val, by omega⟩ : Fin n).castSucc =
            ⟨i.val, by omega⟩ := by
          ext
          rfl
        have hbSucc : (⟨i.val - 2, by omega⟩ : Fin n).succ =
            ⟨i.val - 1, by omega⟩ := by
          ext
          simp only [Fin.val_succ]
          omega
        have hbCast : (⟨i.val - 2, by omega⟩ : Fin n).castSucc =
            ⟨i.val - 2, by omega⟩ := by
          ext
          rfl
        rw [haSucc, haCast, hbSucc, hbCast] at hgapExpanded
        exact hgapExpanded
      have hcross : b.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, by omega⟩ := by
        by_contra hnot
        apply hnotLong
        constructor
        · omega
        · omega
      have hlarge :
          (((2 * (ramificationIndex K : ℚ) +
              (b.order ⟨j.val - 2, by
                have := j.one_lt
                have := j.le_small_succ
                omega⟩ : ℚ) -
              (a.order ⟨j.val, j.lt_large⟩ : ℚ) : ℚ)) :
              WithTop ℚ) < a.centralCurrentDefect b j := by
        apply lt_of_lt_of_le _ hmixed
        norm_cast
        dsimp only [j]
        have hstrictQ :
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) +
                2 * (ramificationIndex K : ℚ) <
              (a.order ⟨i.val + 1, by omega⟩ : ℚ) := by
          exact_mod_cast hstrict
        have hcrossQ :
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) <
              (a.order ⟨i.val, by omega⟩ : ℚ) := by
          exact_mod_cast hcross
        have hgapQ :
            (a.orderGap ⟨i.val, by omega⟩ : ℚ) ≤
              (b.orderGap ⟨i.val - 2, by omega⟩ : ℚ) := by
          exact_mod_cast hgap
        have hgapExpandedQ :
            (a.order ⟨i.val + 1, by omega⟩ : ℚ) -
                (a.order ⟨i.val, by omega⟩ : ℚ) ≤
              (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
                (b.order ⟨i.val - 2, by omega⟩ : ℚ) := by
          exact_mod_cast hgapExpanded
        rw [haGapDef, hbGapDef]
        push_cast
        apply lt_min
        · apply lt_min <;> linarith
        · linarith
      have htrigger := a.beli2019Corollary217_of_currentDefect
        (sourceLaws := alphaV) (targetLaws := alphaW) b le_rfl
        hconditions.orderCondition hconditions.defectCondition j
          (by simpa only [j] using hcross) hlarge
      have hcentral := hconditions.centralRepresentations j htrigger
      have htail := a.prefixValues_represents_of_le
        i.val (i.val + 1) (by omega) (by omega)
      exact hcentral.trans htail
    · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
        { val := i.val + 1
          one_lt := by omega
          lt_large := i.succ_lt_large
          le_small_succ := by omega }
      have hgapExpanded :
          b.order ⟨i.val - 1, by omega⟩ -
              b.order ⟨i.val - 2, by omega⟩ ≤
            a.order ⟨i.val + 1, by omega⟩ - a.order ⟨i.val, by omega⟩ := by
        have hgapExpanded := hgap
        unfold orderGap at hgapExpanded
        have haSucc : (⟨i.val, by omega⟩ : Fin n).succ =
            ⟨i.val + 1, by omega⟩ := by
          ext
          rfl
        have haCast : (⟨i.val, by omega⟩ : Fin n).castSucc =
            ⟨i.val, by omega⟩ := by
          ext
          rfl
        have hbSucc : (⟨i.val - 2, by omega⟩ : Fin n).succ =
            ⟨i.val - 1, by omega⟩ := by
          ext
          simp only [Fin.val_succ]
          omega
        have hbCast : (⟨i.val - 2, by omega⟩ : Fin n).castSucc =
            ⟨i.val - 2, by omega⟩ := by
          ext
          rfl
        rw [haSucc, haCast, hbSucc, hbCast] at hgapExpanded
        exact hgapExpanded
      have hcross : b.order ⟨i.val - 1, by omega⟩ <
          a.order ⟨i.val + 1, by omega⟩ := by
        by_contra hnot
        apply hnotLong
        constructor
        · omega
        · omega
      have hlarge :
          (((2 * (ramificationIndex K : ℚ) +
              (b.order ⟨j.val - 2, by
                have := j.one_lt
                have := j.le_small_succ
                omega⟩ : ℚ) -
              (a.order ⟨j.val, j.lt_large⟩ : ℚ) : ℚ)) :
              WithTop ℚ) < a.centralPreviousDefect b j := by
        apply lt_of_lt_of_le _ hmixed
        norm_cast
        dsimp only [j]
        have hstrictQ :
            (b.order ⟨i.val - 2, by omega⟩ : ℚ) +
                2 * (ramificationIndex K : ℚ) <
              (a.order ⟨i.val + 1, by omega⟩ : ℚ) := by
          exact_mod_cast hstrict
        have hcrossQ :
            (b.order ⟨i.val - 1, by omega⟩ : ℚ) <
              (a.order ⟨i.val + 1, by omega⟩ : ℚ) := by
          exact_mod_cast hcross
        have hgapQ :
            (b.orderGap ⟨i.val - 2, by omega⟩ : ℚ) ≤
              (a.orderGap ⟨i.val, by omega⟩ : ℚ) := by
          exact_mod_cast hgap
        have hgapExpandedQ :
            (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
                (b.order ⟨i.val - 2, by omega⟩ : ℚ) ≤
              (a.order ⟨i.val + 1, by omega⟩ : ℚ) -
                (a.order ⟨i.val, by omega⟩ : ℚ) := by
          exact_mod_cast hgapExpanded
        rw [haGapDef, hbGapDef]
        push_cast
        apply lt_min
        · apply lt_min <;> linarith
        · linarith
      have htrigger := a.beli2019Corollary217_of_previousDefect
        (sourceLaws := alphaV) (targetLaws := alphaW) b le_rfl
        hconditions.orderCondition hconditions.defectCondition j
          (by
            convert hcross using 1 <;> congr 1 <;> ext <;>
              dsimp only [j] <;> omega) hlarge
      have hcentral := hconditions.centralRepresentations j htrigger
      have hhead := b.prefixValues_represents_of_le
        (i.val - 1) i.val (by omega) (by omega)
      exact hhead.trans hcentral
  · let source := b.prefixValueUnits (i.val - 1) (by omega)
    let target := a.prefixValueUnits (i.val + 1) (by omega)
    have hdet : ¬ IsSquare
        (-diagonalUnitDeterminant target *
          diagonalUnitDeterminant source) := by
      simpa only [source, target,
        diagonalUnitDeterminant_prefixValueUnits] using hsquare
    have hrep := diagonalRepresents_of_not_negative_determinant_square
      source target (show i.val + 1 = (i.val - 1) + 2 by omega) hdet
    simpa only [source, target,
      diagonalUnitCoefficients_prefixValueUnits] using hrep

end BONG.GoodBONG

end Bong
