/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79DefectOne
import Bong.Bong.Beli2019Lemma79MixedAssembly

/-!
# Beli (2019), Lemma 7.9(ii): the type-I target-alpha branch

This is the arithmetic part of case 4 when Remark 6.16 selects `beta_i`.
The two profile identities and the odd-order assertion are kept explicit;
the next files derive them from the canonical type-I profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- Several coercions through `WithTop` and four dependent indices elaborate here.
/-- The target-alpha estimate in Lemma 7.9(ii), case 4.  If the current
target order is no larger than the comparison order, the primary candidate
applies.  Otherwise condition 2.1(i) and the odd third prefix make the
secondary candidate nonpositive. -/
theorem lemma79_typeI_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hbetaNext : b.alphaValue ⟨i.val - 1, by omega⟩ =
      ((b.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨i.val, by omega⟩)
    (htwoStep : b.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val + 1, hi.2⟩)
    (hoddThird : Odd (ordUnit K
      ((1 : Kˣ) * b.prefixProduct (i.val + 2) *
        c.prefixProduct (i.val - 2)))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  by_cases hcurrent : b.order ⟨i.val - 1, by omega⟩ ≤
      c.order ⟨i.val - 1, by omega⟩
  · have hprimary := b.representationAlphaValue_le_primary_nextAlpha
      c i hi.2
    have hcurrentQ :
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
        ((b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) := by
      exact_mod_cast (show b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
          b.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, by omega⟩ by omega)
    have hbound : b.representationAlphaValue c i ≤
        b.alphaValue ⟨i.val - 1, by omega⟩ := by
      linarith [hprimary, hcurrentQ, hbetaNext]
    exact WithTop.coe_le_coe.mpr hbound
  · have hcurrentStrict : c.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ := lt_of_not_ge hcurrent
    rcases horder ⟨i.val - 1, by omega⟩ with hdirect | hpair
    · exact False.elim ((not_le_of_gt hcurrentStrict) hdirect)
    · rcases hpair with ⟨_, _, hpair⟩
      have hpair' : b.order ⟨i.val - 1, by omega⟩ +
            b.order ⟨i.val, i.lt_large⟩ ≤
          c.order ⟨i.val - 2, by omega⟩ +
            c.order ⟨i.val - 1, by omega⟩ := by
        simpa only [show i.val - 1 - 1 = i.val - 2 by omega,
          Nat.sub_add_cancel i.pos] using hpair
      have hpairShift : b.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val + 1, hi.2⟩ ≤
          c.order ⟨i.val - 2, by omega⟩ +
            c.order ⟨i.val - 1, by omega⟩ := by
        rw [← htwoStep]
        simpa only [add_comm] using hpair'
      have hdefectZero : defectOrder (K := K)
          ((1 : Kˣ) * b.prefixProduct (i.val + 2) *
            c.prefixProduct (i.val - 2)) = 0 := by
        unfold defectOrder
        rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hoddThird]
        rfl
      have htruncatedUpper := b.truncatedPrefixDefect_le_defect
        c 1 (i.val + 2) (i.val - 2)
      rw [hdefectZero] at htruncatedUpper
      have htruncatedZero :
          b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) = 0 :=
        le_antisymm htruncatedUpper
          (b.truncatedPrefixDefect_nonneg c 1 (i.val + 2) (i.val - 2))
      have hsecondary := b.representationAlpha_le_secondary c i hi
      rw [← b.coe_representationAlphaValue c i] at hsecondary
      unfold representationSecondaryDefect at hsecondary
      rw [htruncatedZero, add_zero] at hsecondary
      have hcoefficient :
          b.order ⟨i.val, i.lt_large⟩ +
              b.order ⟨i.val + 1, hi.2⟩ -
                c.order ⟨i.val - 2, by omega⟩ -
                  c.order ⟨i.val - 1, by omega⟩ ≤ 0 := by
        omega
      have hnonpositive :
          (b.representationAlphaValue c i : WithTop ℚ) ≤ 0 :=
        hsecondary.trans (by exact_mod_cast hcoefficient)
      have hbetaNonnegative : (0 : WithTop ℚ) ≤
          (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
        exact_mod_cast (b.alpha_p2 ⟨i.val - 1, by omega⟩).1
      exact hnonpositive.trans hbetaNonnegative

end BONG.GoodBONG

end Bong
