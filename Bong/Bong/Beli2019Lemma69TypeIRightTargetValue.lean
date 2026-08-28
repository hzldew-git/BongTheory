/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightTargetSecondary
import Bong.Bong.Beli2019Lemma63Right
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 6.9(ii): type-I right target values

The first two representation candidates are bounded locally.  The secondary
candidate is propagated backwards by two positions, starting from Lemma 6.3
on the common suffix after the last unequal order.  This proves
`A_i = beta_i` on the complete odd right branch, including `i = t'`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- Reverse strong induction transports dependent representation indices.
/-- On every odd boundary strictly between the canonical right switch and
the last unequal order, the representation invariant is the target alpha. -/
theorem lemma69_typeI_right_beta_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    exact (D.profile.rightProfile (by
      have har := C.anchor_le_right
      omega)).1
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    exact ⟨d + e, by
      have hal := D.profile.anchor_le_last
      omega⟩
  have hmain : ∀ (distance t : Nat),
      distance = D.profile.last - t →
      C.rightSwitch < t → t < D.profile.last → Odd t →
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
        have hhalf := lemma69_typeI_right_beta_le_halfGap
          a b D C hfirst j hright hlast hodd
        have hprimary := lemma69_typeI_right_beta_le_primary
          a b D C hfirst hrightLast hdefect j hright hlast hodd
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
            have horders := lemma69_typeI_rightOdd_orders
              a b D C hfirst j.val hright hlast hodd
            have hcurrentOrder : a.order ⟨j.val, j.lt_large⟩ =
                b.order ⟨j.val, j.lt_large⟩ + 1 := by
              rw [← a.orderSequence_entryOrZero_eq_order,
                ← b.orderSequence_entryOrZero_eq_order]
              exact horders.1
            have hnextOrder :
                b.order ⟨j.val + 1, hinterior.2⟩ =
                  a.order ⟨j.val + 1, hinterior.2⟩ + 1 := by
              rw [← b.orderSequence_entryOrZero_eq_order,
                ← a.orderSequence_entryOrZero_eq_order]
              exact horders.2
            have hpairsum :
                a.order ⟨j.val, j.lt_large⟩ +
                    a.order ⟨j.val + 1, hinterior.2⟩ =
                  b.order ⟨j.val, j.lt_large⟩ +
                    b.order ⟨j.val + 1, hinterior.2⟩ := by
              omega
            have hlater : ∀ hbound : j.val + 2 < n + 2,
                a.representationAlpha b
                    (⟨j.val + 2, by omega, hbound, by omega⟩ :
                      RepresentationIndex (n + 2) (n + 2)) =
                  (b.alphaValue ⟨j.val + 1, by omega⟩ : WithTop ℚ) := by
              intro hbound
              let laterIdx : RepresentationIndex (n + 2) (n + 2) :=
                ⟨j.val + 2, by omega, hbound, by omega⟩
              by_cases hafter : D.profile.last < j.val + 2
              · have hsuffix : ∀ k, laterIdx.val ≤ k →
                    k < n + 2 →
                    a.orderSequence.entryOrZero k =
                      b.orderSequence.entryOrZero k := by
                  intro k hk hkn
                  exact D.profile.lastDifference.after k (by
                    simp only [laterIdx] at hk
                    omega) hkn
                have hvalue := a.beli2019Lemma63_sameRank_right
                  b hdefect laterIdx hsuffix
                simpa only [laterIdx,
                  show j.val + 2 - 1 = j.val + 1 by omega] using hvalue
              · have hlaterLast : j.val + 2 < D.profile.last := by
                  rcases hodd with ⟨d, hdOdd⟩
                  rcases hlastEven with ⟨e, heEven⟩
                  omega
                have hlaterOdd : Odd (j.val + 2) := by
                  rcases hodd with ⟨d, hdOdd⟩
                  exact ⟨d + 1, by omega⟩
                have hmeasure :
                    D.profile.last - (j.val + 2) < distance := by
                  omega
                have hvalue := ih
                  (D.profile.last - (j.val + 2)) hmeasure
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
  exact hmain (D.profile.last - i.val) i.val rfl hright hlast hodd i rfl

/-- Rational-valued form of the complete odd type-I right branch. -/
theorem beli2019Lemma69_ii_typeI_targetRightValue
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  apply WithTop.coe_injective
  rw [a.coe_representationAlphaValue b i]
  exact lemma69_typeI_right_beta_eq
    a b D C hfirst hrightLast hdefect i hright hlast hodd

end BONG.GoodBONG

end Bong
