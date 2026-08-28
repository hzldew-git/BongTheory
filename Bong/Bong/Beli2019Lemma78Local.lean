/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78SourcePropagation

/-!
# Beli (2019), Lemma 7.8: local type-III prefix form

The proof of the source-prefix part of Lemma 7.8 only uses the type-III
center and the interval ending at the last unequal coordinate.  The earlier
API imposed the stronger equation saying that this coordinate was the final
coordinate of the entire BONG.  This file records the local form needed in
Lemma 7.9 case 8 and removes that artificial full-span hypothesis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The central representation invariant vanishes without requiring the
last unequal coordinate to be the full-rank endpoint. -/
theorem beli2019Lemma78_representationAlpha_eq_zero_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.representationAlphaValue b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } = 0 := by
  let left := D.outer.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let idx : RepresentationIndex (n + 2) (n + 2) := {
    val := left + 1
    pos := by omega
    lt_large := by
      dsimp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    le_small := by
      dsimp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega }
  have hsourceData := a.beli2019Lemma78_sourceAlpha_and_gap
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap hinitial
  have hsourceAlpha : a.alphaValue center = 1 := by
    simpa only [center, left] using hsourceData.1
  have hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 := by
    simpa only [center, left] using hsourceData.2
  have hHalf : 0 ≤ a.representationHalfGap b idx := by
    have hpositive := a.lemma78_typeIII_representationHalfGap_pos b D
      (by simpa only [center, left] using hgap)
    simpa only [idx, left] using hpositive.le
  have hPrimary : 0 ≤ a.representationPrimaryDefect b idx := by
    have hnonneg := a.lemma69_typeIII_primaryDefect_nonneg
      (alphaV := alpha) (alphaW := alpha) b D hfirst
      (by simpa only [center, left] using hsourceAlpha)
    simpa only [idx, left] using hnonneg
  have hSecondary : ∀ hi : 1 < idx.val ∧ idx.val + 1 < n + 2,
      0 ≤ a.representationSecondaryDefect b idx hi := by
    intro hi
    have hcoefficient := a.lemma69_typeIII_secondaryCoefficient_pos
      b D hfirst (by simpa only [idx, left] using hi)
    have hpositive := a.representationSecondaryDefect_pos_of_orderCoefficient_pos
      (alphaV := alpha) (alphaW := alpha) b idx hi
      (by simpa only [idx, left] using hcoefficient)
    exact hpositive.le
  have hnonnegative : 0 ≤ a.representationAlpha b idx :=
    a.representationAlpha_nonneg_of_candidates b idx
      hHalf hPrimary hSecondary
  have hprefixGap :
      a.orderSequence.prefixGap b.orderSequence idx.val = 1 := by
    have hbetween := D.outer.transition.gap_between (left + 1)
      (by omega) (by have hadjacent := D.adjacent; omega)
    simpa only [idx] using hbetween
  have hsum : b.orderSequence.prefixSum idx.val =
      a.orderSequence.prefixSum idx.val + 1 := by
    unfold BeliOrderSequence.prefixGap at hprefixGap
    omega
  have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    (alphaV := alpha) (alphaW := alpha) b idx.val
    idx.lt_large.le idx.le_small hsum
  have hupper := hdefect idx
  rw [hzeroDefect] at hupper
  have hlower : (0 : WithTop Rat) ≤
      (a.representationAlphaValue b idx : WithTop Rat) := by
    rw [a.coe_representationAlphaValue b idx]
    exact hnonnegative
  have htop : (a.representationAlphaValue b idx : WithTop Rat) = 0 :=
    le_antisymm hupper hlower
  have hvalue : a.representationAlphaValue b idx = 0 := by
    exact_mod_cast htop
  simpa only [idx, left] using hvalue

/-- The exact central mixed defect in local form. -/
theorem beli2019Lemma78_centralMixedDefect_exact_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.truncatedPrefixDefect b (-1)
        (D.outer.transition.lastZero + 2)
        D.outer.transition.lastZero =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  have hsourceData := a.beli2019Lemma78_sourceAlpha_and_gap
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap hinitial
  have hAlpha := a.beli2019Lemma78_representationAlpha_eq_zero_local
    b D hfirst hdefect hnotOverlap hinitial
  apply a.beli2019Lemma78_centralMixedDefect_of_alpha_zero
    b D hfirst hAlpha
  exact hsourceData.2

/-- The first even source prefix after the type-III center, locally. -/
theorem beli2019Lemma78_firstSourcePrefixDefect_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.outer.transition.lastZero + 2) / 2)) 0
        (D.outer.transition.lastZero + 2) =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  let left := D.outer.transition.lastZero
  let eta : Kˣ := (-1) ^ (left / 2)
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hmixed := a.beli2019Lemma78_centralMixedDefect_exact_local
    b D hfirst hdefect hnotOverlap hinitial
  have htarget := a.lemma78_typeIII_targetPrefix_gt_mixedShift
    b D hfirst
  have htargetTransfer :
      b.truncatedPrefixDefect a eta left 0 =
        b.truncatedPrefixDefect b eta left 0 :=
    b.truncatedPrefixDefect_zero_right_eq_self a eta left
  have htargetComm : b.truncatedPrefixDefect b eta left 0 =
      b.truncatedPrefixDefect b eta 0 left :=
    b.truncatedPrefixDefect_comm b eta left 0
  have hseparation :
      a.truncatedPrefixDefect b (-1) (left + 2) left <
        b.truncatedPrefixDefect a eta left 0 := by
    rw [htargetTransfer, htargetComm]
    rw [hmixed]
    simpa only [eta, left] using htarget
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b a (-1) eta (left + 2) left 0 hseparation
  have hsign : (-1 : Kˣ) * eta = (-1) ^ ((left + 2) / 2) := by
    rcases hleftEven with ⟨d, hd⟩
    have hhalf : left / 2 = d := by omega
    have hhalfNext : (left + 2) / 2 = d + 1 := by omega
    dsimp only [eta]
    rw [hhalf, hhalfNext, pow_succ]
    ac_rfl
  calc
    a.truncatedPrefixDefect a ((-1) ^ ((left + 2) / 2)) 0
        (left + 2) =
      a.truncatedPrefixDefect a ((-1) ^ ((left + 2) / 2))
        (left + 2) 0 :=
      a.truncatedPrefixDefect_comm a
        ((-1) ^ ((left + 2) / 2)) 0 (left + 2)
    _ = a.truncatedPrefixDefect a ((-1) * eta) (left + 2) 0 := by
      rw [hsign]
    _ = a.truncatedPrefixDefect b (-1) (left + 2) left := hsharp
    _ = _ := by simpa only [left] using hmixed

/-- Every even source prefix through the last unequal coordinate has the
central type-III defect, with no full-span assumption. -/
theorem beli2019Lemma78_sourcePrefixDefect_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiLast : i ≤ D.outer.last + 1) (hiEven : Even i) :
    a.truncatedPrefixDefect a ((-1) ^ (i / 2)) 0 i =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  let left := D.outer.transition.lastZero
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hfirstDefect := a.beli2019Lemma78_firstSourcePrefixDefect_local
    b D hfirst hdefect hnotOverlap hinitial
  by_cases hiFirst : i = left + 2
  · subst i
    simpa only [left] using hfirstDefect
  · have hiTail : left + 4 ≤ i := by
      rcases hleftEven with ⟨d, hd⟩
      rcases hiEven with ⟨e, he⟩
      omega
    have hleftRank : left < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      simp only [left]
      rw [D.adjacent] at hbound
      omega
    have hrightRank : left + 1 < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      simp only [left]
      rw [D.adjacent] at hbound
      omega
    let firstSign : Kˣ := (-1) ^ ((left + 2) / 2)
    let tailSign : Kˣ := (-1) ^ ((i - (left + 2)) / 2)
    have htail := a.lemma78_typeIII_sourceTail_gt_mixedShift
      b D hfirst i (by simpa only [left] using hiTail) hiLast hiEven
    have hseparation :
        a.truncatedPrefixDefect a firstSign 0 (left + 2) <
          a.truncatedPrefixDefect a tailSign (left + 2) i := by
      rw [show a.truncatedPrefixDefect a firstSign 0 (left + 2) =
          (((b.order ⟨left, hleftRank⟩ -
            a.order ⟨left + 1, hrightRank⟩ : Int) : Rat) : WithTop Rat) by
        simpa only [firstSign, left] using hfirstDefect]
      simpa only [tailSign, left] using htail
    have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
      a a firstSign tailSign 0 (left + 2) i hseparation
    have hsign : firstSign * tailSign = (-1 : Kˣ) ^ (i / 2) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases hiEven with ⟨e, he⟩
      have hsum : (left + 2) / 2 + (i - (left + 2)) / 2 = i / 2 := by
        omega
      dsimp only [firstSign, tailSign]
      rw [← pow_add, hsum]
    calc
      a.truncatedPrefixDefect a ((-1) ^ (i / 2)) 0 i =
          a.truncatedPrefixDefect a (firstSign * tailSign) 0 i := by
        rw [hsign]
      _ = a.truncatedPrefixDefect a firstSign 0 (left + 2) := hsharp
      _ = _ := by simpa only [firstSign, left] using hfirstDefect

end BONG.GoodBONG

end Bong
