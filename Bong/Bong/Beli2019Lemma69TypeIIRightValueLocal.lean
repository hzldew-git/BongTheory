/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark613TypeIIRightAlphaLocal
import Bong.Bong.Beli2019Lemma69TypeIRightTargetSecondary
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 6.9(ii): local type-II right values

The half-gap and primary candidates are bounded from the local right-order
profile and the local form of Remark 6.13.  The secondary candidate is then
propagated backwards by two positions, with Lemma 6.3 supplying the first
value in the common suffix.  No full-span normalization is used.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target alpha is below the representation half-gap candidate on
the odd-distance type-II right branch. -/
theorem lemma69_typeII_right_beta_le_halfGap_local
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hlast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤ a.representationHalfGap b i := by
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hi := i.lt_large
    omega⟩
  have hentry := D.outer.source_rightOdd_eq_target_add_one
    D.no_gap_two i.val (by omega) hlast.le hodd
  have hiPos : 0 < i.val := by
    have hseparated := D.outer.transition.separated
    omega
  have hsourceCurrent : a.order ⟨i.val, i.lt_large⟩ =
      b.order p.succ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    simpa only [p, Fin.val_succ,
      show i.val - 1 + 1 = i.val by omega] using hentry
  have htargetPrevious :
      b.order ⟨i.val - 1, by have hi := i.lt_large; omega⟩ =
        b.order p.castSucc := by
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hbeta := b.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at hbeta
  have hfinite : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [hsourceCurrent, htargetPrevious]
    push_cast at hbeta ⊢
    linarith
  unfold representationHalfGap
  exact_mod_cast hfinite

/-- The target alpha is below the primary mixed-defect candidate on the
odd-distance type-II right branch. -/
theorem lemma69_typeII_right_beta_le_primary_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hlast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hi := i.lt_large
    omega⟩
  let next : Fin (n + 1) := ⟨i.val, by
    have hlastBound := D.outer.lastDifference.bound
    omega⟩
  have hentry := D.outer.source_rightOdd_eq_target_add_one
    D.no_gap_two i.val (by omega) hlast.le hodd
  have hsourceCurrent : a.order ⟨i.val, i.lt_large⟩ =
      b.order next.castSucc + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    simpa only [next, Fin.val_castSucc] using hentry
  have htargetPrevious :
      b.order ⟨i.val - 1, by have hi := i.lt_large; omega⟩ =
        b.order p.castSucc := by
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hnextAlpha :=
    a.beli2019Remark613_typeII_targetRightAlpha_eq_one_local
      b D horder hdefect htotal i.val hright hlast hodd
  have hendpoint := b.alphaLeftEndpoint_monotone
    (show p ≤ next by
      change p.val ≤ next.val
      simp only [p, next]
      omega)
  have hrecurrence : b.alphaValue p ≤
      ((b.order next.castSucc - b.order p.castSucc : Int) : ℚ) + 1 := by
    unfold alphaLeftEndpoint at hendpoint
    have hnextAlpha' : b.alphaValue next ≤ 1 := by
      simpa only [next] using hnextAlpha.le
    push_cast at hendpoint ⊢
    linarith
  have hcoefficient : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) := by
    rw [hsourceCurrent, htargetPrevious]
    push_cast at hrecurrence ⊢
    linarith
  have hcoefficientTop : (b.alphaValue p : WithTop ℚ) ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficient
  have hdefectNonneg := a.truncatedPrefixDefect_nonneg
    b (-1) (i.val + 1) (i.val - 1)
  unfold representationPrimaryDefect
  exact hcoefficientTop.trans (le_add_of_nonneg_right hdefectNonneg)

set_option maxHeartbeats 5000000 in
-- Reverse strong induction transports the dependent representation index.
/-- On every odd-distance boundary strictly before the last unequal order,
the representation invariant is the target alpha. -/
theorem lemma69_typeII_right_beta_eq_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hlast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hlastDistance := D.outer.right_even_distance
  have hmain : ∀ (distance t : Nat),
      distance = D.outer.last - t →
      D.outer.transition.firstTwo ≤ t →
      t < D.outer.last →
      Odd (t - (D.outer.transition.firstTwo - 1)) →
      ∀ j : RepresentationIndex (n + 2) (n + 2), j.val = t →
        a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hb := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
        intro t hd hright hlast hodd j hj
        subst t
        have hhalf := lemma69_typeII_right_beta_le_halfGap_local
          a b D j hright hlast hodd
        have hprimary := lemma69_typeII_right_beta_le_primary_local
          a b D horder hdefect htotal j hright hlast hodd
        have hupper := a.representationAlpha_le_rightAlpha b hdefect j
        have hlower :
            (b.alphaValue ⟨j.val - 1, by
              have hb := j.lt_large
              omega⟩ : WithTop ℚ) ≤
              a.representationAlpha b j := by
          rw [a.representationAlpha_eq_min_halfGap_prime b j]
          apply le_min hhalf
          by_cases hinterior : 1 < j.val ∧ j.val + 1 < n + 2
          · rw [a.representationAlphaPrime_eq_min_primary_secondary
                b j hinterior]
            apply le_min hprimary
            have hpair := D.outer.rightOdd_pair_eq j.val
              (by omega) hlast.le hodd
            have hpairsum :
                a.order ⟨j.val, j.lt_large⟩ +
                    a.order ⟨j.val + 1, hinterior.2⟩ =
                  b.order ⟨j.val, j.lt_large⟩ +
                    b.order ⟨j.val + 1, hinterior.2⟩ := by
              rw [← a.orderSequence_entryOrZero_eq_order,
                ← a.orderSequence_entryOrZero_eq_order,
                ← b.orderSequence_entryOrZero_eq_order,
                ← b.orderSequence_entryOrZero_eq_order]
              exact hpair
            have hlater : ∀ hbound : j.val + 2 < n + 2,
                a.representationAlpha b
                    (⟨j.val + 2, by omega, hbound, by omega⟩ :
                      RepresentationIndex (n + 2) (n + 2)) =
                  (b.alphaValue ⟨j.val + 1, by omega⟩ : WithTop ℚ) := by
              intro hbound
              let laterIdx : RepresentationIndex (n + 2) (n + 2) :=
                ⟨j.val + 2, by omega, hbound, by omega⟩
              by_cases hafter : D.outer.last < j.val + 2
              · have hsuffix : ∀ k, laterIdx.val ≤ k →
                    k < n + 2 →
                    a.orderSequence.entryOrZero k =
                      b.orderSequence.entryOrZero k := by
                  intro k hk hkn
                  exact D.outer.lastDifference.after k (by
                    simp only [laterIdx] at hk
                    omega) hkn
                have hvalue := a.beli2019Lemma63_sameRank_right
                  b hdefect laterIdx hsuffix
                simpa only [laterIdx,
                  show j.val + 2 - 1 = j.val + 1 by omega] using hvalue
              · have hlaterLast : j.val + 2 < D.outer.last := by
                  rcases hlastDistance with ⟨e, he⟩
                  rcases hodd with ⟨d, hdOdd⟩
                  omega
                have hlaterOdd : Odd
                    ((j.val + 2) -
                      (D.outer.transition.firstTwo - 1)) := by
                  rcases hodd with ⟨d, hdOdd⟩
                  exact ⟨d + 1, by omega⟩
                have hmeasure :
                    D.outer.last - (j.val + 2) < distance := by
                  omega
                have hvalue := ih
                  (D.outer.last - (j.val + 2)) hmeasure
                  (j.val + 2) rfl (by omega) hlaterLast hlaterOdd
                  laterIdx rfl
                simpa only [laterIdx,
                  show j.val + 2 - 1 = j.val + 1 by omega] using hvalue
            exact lemma69_typeI_right_beta_le_secondary_of_later
              a b hdefect j hinterior hpairsum hlater
          · rw [a.representationAlphaPrime_eq_primary_of_not_interior
                b j hinterior]
            exact hprimary
        exact le_antisymm hupper hlower
  exact hmain (D.outer.last - i.val) i.val rfl hright hlast hodd i rfl

/-- Rational-valued local form of Lemma 6.9(ii) on the type-II right
branch. -/
theorem beli2019Lemma69_ii_typeII_targetRightValue_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : Nat) (hiStart : D.outer.transition.firstTwo ≤ i)
    (hiParity : Odd (i - (D.outer.transition.firstTwo - 1)))
    (hiLast : i < D.outer.last) :
    a.representationAlphaValue b
        ⟨i, by
          have hlong := D.long
          omega, by
          have hlastBound := D.outer.lastDifference.bound
          omega, by
          have hlastBound := D.outer.lastDifference.bound
          omega⟩ =
      b.alphaValue ⟨i - 1, by
        have hlastBound := D.outer.lastDifference.bound
        omega⟩ := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by
      have hlong := D.long
      omega, by
      have hlastBound := D.outer.lastDifference.bound
      omega, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b idx]
  simpa only [idx] using a.lemma69_typeII_right_beta_eq_local
    b D horder hdefect htotal idx hiStart hiLast hiParity

end BONG.GoodBONG

end Bong
