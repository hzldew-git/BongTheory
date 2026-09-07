/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma75Sufficiency
import Bong.Bong.He2023ADCLemma710
import Bong.Bong.He2023ADCLemma711
import Bong.Bong.He2023ADCLemma713
import Bong.Bong.Beli2019Lemma79TypeICaseOnePrefixDefect

/-!
# He (2025), necessity in Lemma 7.5

This file derives the four displayed numerical conditions from `n`-ADC.
The terminal alpha-one condition uses the corrected quantifier form of
Lemma 7.13: the source ambient row selects one column, and ADC would force
both targets in that column to satisfy Theorem 3.6.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Necessity of Lemma 7.5(iii).  Proposition 3.5(iv) leaves two endpoint
classes in the exceptional case `n=3`: the discriminant class supplies the
published `d(a_1...a_4)=2e` hypothesis, while the square class is excluded
by Lemma 7.11. -/
theorem heADC2025Lemma75iii (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hgap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) :
    a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) ∧
      a.order ⟨2 * k + 4, by omega⟩ = 1 := by
  have h710 := a.heADC2025Lemma710 k hADC
  have hlarge := h710.largeGapConclusion hgap
  refine ⟨hlarge.1, ?_⟩
  by_cases hk : k = 0
  · subst k
    have hR4 : a.order ⟨3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      simpa only using hlarge.1
    have hclasses :=
      ((a.heADC2025Proposition35 hADC.isIntegral).clausesIIIIV
        (3 : Fin 5) (by norm_num) hR4).prefixEndpointClass
    rcases hclasses with ⟨pairs, hpairs, hclass⟩
    change 2 * pairs = 4 at hpairs
    have hpairs' : pairs = 2 := by omega
    subst pairs
    have hclass' : IsSquare (a.prefixProduct 4) ∨
        IsSquare (a.prefixProduct 4 *
          (heHuDiscriminantClassLaws (K := K)).discriminantUnit) := by
      simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hclass
    rcases hclass' with hsquare | htwisted
    · have hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤ :=
        defectOrder_eq_top_of_isSquare hsquare
      have hR5Positive : 0 < a.order ⟨4, by omega⟩ := by
        have hgap' : 2 * (ramificationIndex K : Int) <
            a.order ⟨4, by omega⟩ - a.order ⟨3, by omega⟩ := by
          simpa only [Nat.mul_zero, Nat.zero_add] using hgap
        rw [hR4] at hgap'
        omega
      by_cases hR5 : a.order ⟨4, by omega⟩ = 1
      · exact hR5
      · have hR5Large : 1 < a.order ⟨4, by omega⟩ := by omega
        exact (a.heADC2025Lemma711_badBranch_impossible hADC h710.initial
          hR4 hR5Large hprefix).elim
    · have hdefect : a.heHuPrefixDefect 4 =
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) : WithTop ℚ) := by
        unfold heHuPrefixDefect
        simpa using defectOrder_eq_twoE_of_mul_discriminant_isSquare
          (K := K) (a.prefixProduct 4) htwisted
      exact hlarge.2 (Or.inr ⟨rfl, hdefect⟩)
  · have hkPositive : 0 < k := Nat.pos_of_ne_zero hk
    exact hlarge.2 (Or.inl (by omega))

/-- Necessity of Lemma 7.5(iv), with paper rank `n=2*k+3`. -/
theorem heADC2025Lemma75iv (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1) :
    Even (a.order ⟨2 * k + 3, by omega⟩) ∧
      2 - 2 * (ramificationIndex K : Int) ≤
        a.order ⟨2 * k + 3, by omega⟩ ∧
      a.order ⟨2 * k + 3, by omega⟩ ≤ 0 ∧
      (a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 4, by omega⟩ = 1) := by
  have h710 := a.heADC2025Lemma710 k hADC
  have hprevious : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    apply h710.initial.oddOrder ⟨2 * k + 2, by omega⟩
    change Odd (2 * k + 3)
    exact ⟨k + 1, by omega⟩
  have himpossible := a.heADC2025Lemma713_trigger_impossible k hADC hAlpha
  have hnextNe : a.order ⟨2 * k + 3, by omega⟩ ≠ 1 := by
    intro hnext
    exact himpossible (Or.inl hnext)
  have hlastLe : a.order ⟨2 * k + 4, by omega⟩ ≤ 1 := by
    exact le_of_not_gt (fun hlast ↦ himpossible (Or.inr hlast))
  let i : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  have hgap : a.orderGap i = a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap
    change a.order ⟨2 * k + 3, by omega⟩ -
      a.order ⟨2 * k + 2, by omega⟩ = _
    rw [hprevious, sub_zero]
  have hshape := (a.heADC2025Proposition34 i).alphaOne.mp hAlpha
  rw [hgap] at hshape
  have hnext : Even (a.order ⟨2 * k + 3, by omega⟩) ∧
      2 - 2 * (ramificationIndex K : Int) ≤
        a.order ⟨2 * k + 3, by omega⟩ ∧
      a.order ⟨2 * k + 3, by omega⟩ ≤ 0 := by
    rcases hshape with (hendpoint | hone) | hmiddle
    · have heven : Even (2 - 2 * (ramificationIndex K : Int)) := by
        refine ⟨1 - (ramificationIndex K : Int), ?_⟩
        ring
      have hePositive : (0 : Int) < ramificationIndex K := by
        exact_mod_cast ramificationIndex_pos (K := K)
      rw [hendpoint]
      exact ⟨heven, le_rfl, by omega⟩
    · exact (hnextNe hone).elim
    · exact ⟨hmiddle.1, by omega, hmiddle.2.2.1⟩
  have hlastNonneg : 0 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
    have heven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
    exact ((a.heHu2022Proposition27i hADC.isIntegral).oddIndexed
      ⟨2 * k + 4, by omega⟩ ⟨2 * k + 4, by omega⟩ le_rfl
        heven heven).1
  refine ⟨hnext.1, hnext.2.1, hnext.2.2, ?_⟩
  omega

/-- The complete necessity implication in He, Lemma 7.5. -/
theorem heADC2025Lemma75Necessity (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) :
    a.HeADCLemma75Conditions k := by
  have h710 := a.heADC2025Lemma710 k hADC
  exact
    { initial := h710.initial
      boundary := h710.boundary
      largeGap := a.heADC2025Lemma75iii k hADC
      alphaOneTail := a.heADC2025Lemma75iv k hADC }

/-- He (2025), Lemma 7.5: the numerical BONG conditions are equivalent to
`n`-ADC for odd paper rank `n=2*k+3`. -/
theorem heADC2025Lemma75 (k : Nat)
    (a : GoodBONG q L (2 * k + 5)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) ↔
      a.HeADCLemma75Conditions k := by
  constructor
  · exact a.heADC2025Lemma75Necessity k
  · intro C
    have hfirst : a.order 0 = 0 := by
      exact C.initial.oddOrder (0 : Fin (2 * k + 3)) odd_one
    exact a.heADC2025Lemma75Sufficiency k
      (heHuIntegral_of_firstOrder_nonneg a (by rw [hfirst])) C

end BONG.GoodBONG

end Bong
