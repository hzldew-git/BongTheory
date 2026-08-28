/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIRightSourcePrimary
import Bong.Bong.Beli2019Lemma69TypeIRightTargetValue
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii): right-tail secondary source candidate

The adjacent source and target order sums agree on the odd right tail. At a
nonterminal boundary, Remark 6.16 compares the remaining mixed prefixes;
at full rank the same comparison follows from square-equivalence of the two
complete value products.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Replacing a full left prefix by another BONG of the same quadratic
space does not change a capped mixed-prefix defect. -/
theorem truncatedPrefixDefect_fullLeft_change
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (epsilon : Kˣ) (j : Nat) :
    b.truncatedPrefixDefect c epsilon (n + 2) j =
      a.truncatedPrefixDefect c epsilon (n + 2) j := by
  rcases BONG.exists_valueProduct_eq_mul_square
    a.toBONG b.toBONG with ⟨p, hp⟩
  have hraw : epsilon * b.toBONG.valueProduct * c.prefixProduct j =
      (epsilon * a.toBONG.valueProduct * c.prefixProduct j) * p ^ 2 := by
    rw [hp]
    ac_rfl
  unfold truncatedPrefixDefect
  rw [a.prefixProduct_eq_valueProduct_of_rank_le (n + 2) le_rfl,
    b.prefixProduct_eq_valueProduct_of_rank_le (n + 2) le_rfl,
    hraw, defectOrder_mul_square, a.prefixAlphaCap_last,
    b.prefixAlphaCap_last]

set_option maxHeartbeats 3000000 in
-- The nonterminal branch transports a dependent index across the last
-- unequal order; the endpoint branch uses the full-prefix identity above.
/-- On the odd type-I right tail, the comparison secondary candidate is no
larger than the source secondary candidate. -/
theorem lemma79_typeI_right_secondary_le_sourceSecondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  rcases hodd with ⟨d, hd⟩
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst i.val hright hlast ⟨d, hd⟩
  have hsumOrders :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ := by
    have hcurrent : a.order ⟨i.val, i.lt_large⟩ =
        b.order ⟨i.val, i.lt_large⟩ + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact horders.1
    have hnext : b.order ⟨i.val + 1, hi.2⟩ =
        a.order ⟨i.val + 1, hi.2⟩ + 1 := by
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order]
      exact horders.2
    omega
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, by omega⟩
      have hfarOdd : Odd farIdx.val := by
        exact ⟨d + 1, by simp only [farIdx]; omega⟩
      have hfarRight : C.rightSwitch < farIdx.val := by
        simp only [farIdx]
        omega
      have hanchorEven : Even D.anchor := by
        by_cases heq : D.profile.first = D.anchor
        · rw [← heq, hfirst]
          exact ⟨0, by omega⟩
        · have hlt : D.profile.first < D.anchor :=
            lt_of_le_of_ne D.profile.first_le_anchor heq
          simpa only [hfirst, Nat.sub_zero] using
            (D.profile.leftProfile hlt).1
      have hlastDistance : Even (D.profile.last - D.anchor) :=
        (D.profile.rightProfile (by
          have har := C.anchor_le_right
          omega)).1
      have hlastEven : Even D.profile.last := by
        rcases hanchorEven with ⟨e, he⟩
        rcases hlastDistance with ⟨f, hf⟩
        exact ⟨e + f, by
          have hal := D.profile.anchor_le_last
          omega⟩
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            simp only [farIdx]
            omega⟩ := by
        by_cases hfarLast : farIdx.val < D.profile.last
        · exact beli2019Lemma69_ii_typeI_targetRightValue
            a b D C hfirst hrightLast hdefect farIdx hfarRight
              hfarLast hfarOdd
        · have hafterLast : D.profile.last < farIdx.val := by
            rcases hfarOdd with ⟨e, he⟩
            rcases hlastEven with ⟨f, hf⟩
            omega
          have hsuffix : ∀ k, farIdx.val ≤ k → k < n + 2 →
              a.orderSequence.entryOrZero k =
                b.orderSequence.entryOrZero k := by
            intro k hk hkn
            exact D.profile.lastDifference.after k (by omega) hkn
          apply WithTop.coe_injective
          rw [a.coe_representationAlphaValue b farIdx]
          exact a.beli2019Lemma63_sameRank_right b hdefect farIdx hsuffix
      have hformula := beli2019Remark616_rightMixedPrefix_at
        a b c hdefect farIdx hAlpha 1 (i.val - 2)
      calc
        b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
            min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
              (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
          simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
            using hformula
        _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
          min_le_left _ _
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [← hcoefficient]
  exact add_le_add_right hprefix _

end BONG.GoodBONG

end Bong
