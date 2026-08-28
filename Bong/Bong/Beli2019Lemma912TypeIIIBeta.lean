/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIAlpha
import Bong.Bong.Beli2019Lemma69RightTailMinimum

/-!
# Beli (2019), Lemma 9.12: the remaining type-III beta bound

This file records two exact reductions used in the type-III branch.

* Lemma 6.9(iv) gives
  `beta_i = min {alpha_i, S_(i+1) - S_4 + beta_3}` for `i >= 3`.
* Once `B_i <= C_i` is known, condition 2.1(ii) at the same boundary is
  equivalent to the single scalar inequality `B_i <= beta_i`.

Thus the longer parity argument printed in Lemma 9.12 is isolated from all
prefix-defect and representation-condition bookkeeping.
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
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- Lemma 6.9(iv) in the exact indexing used by the type-III branch of
Lemma 9.12: `beta_i = min {alpha_i, S_(i+1)-S_4+beta_3}`. -/
theorem beli2019Lemma912_typeIII_alphaValue_eq_min_sourceAlpha_shift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val) :
    (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have := i.lt_large; omega⟩ =
      min ((a.castLength hlength).alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩)
        (((((I.bong.castLength hlength).order
              ⟨i.val, i.lt_large⟩ -
            (I.bong.castLength hlength).order
              (⟨3, by
                have hlt := i.lt_large
                have hge := hi
                omega⟩ : Fin (T + 3)) : Int) : ℚ)) +
          (I.bong.castLength hlength).alphaValue
            (⟨2, by
              have hlt := i.lt_large
              have hge := hi
              omega⟩ : Fin (T + 2))) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let first : Fin (T + 2) := ⟨2, by
    have hlt := i.lt_large
    have hge := hi
    omega⟩
  let j : Fin (T + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hconditions := I.sourceRepresentationConditions a D hlength
  have hsuffix : ∀ k, first.val + 1 <= k -> k < T + 3 ->
      source.orderSequence.entryOrZero k =
        target.orderSequence.entryOrZero k := by
    intro k hk hkr
    rw [BeliOrderSequence.entryOrZero_of_lt source.orderSequence hkr,
      BeliOrderSequence.entryOrZero_of_lt target.orderSequence hkr]
    exact
      (beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength ⟨k, hkr⟩ (by simpa only [first] using hk)).symm
  have hformula := beli2019Lemma69_iv_beta_eq_min source target
    hconditions.orderCondition hconditions.defectCondition first j
      (by change 2 <= i.val - 1; omega) hsuffix
  have hjSucc : j.succ = (⟨i.val, i.lt_large⟩ : Fin (T + 3)) := by
    apply Fin.ext
    simp only [j, Fin.val_succ]
    omega
  have hfirstSucc : first.succ =
      (⟨3, by
        have hlt := i.lt_large
        have hge := hi
        omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  rw [hformula, hjSucc, hfirstSucc]

/-- At every boundary `i >= 3`, condition 2.1(ii) for the type-III image
is equivalent to the paper's scalar inequality `B_i <= beta_i`.

The source-prefix half follows from `B_i <= C_i` and the original source
defect condition; Remark 6.16 supplies the target-alpha half. -/
theorem beli2019Lemma912_typeIII_representationDefectAt_iff_targetAlpha
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val) :
    ((I.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) <=
        (I.bong.castLength hlength).truncatedPrefixDefect
          c 1 i.val i.val ↔
      (I.bong.castLength hlength).representationAlphaValue c i <=
        (I.bong.castLength hlength).alphaValue
          ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hmixed := beli2019Lemma912_typeIII_mixedPrefixDefect
    a c D I hlength i hi 1 i.val
  have hcomparison :=
    beli2019Lemma912_typeIII_representationAlpha_le_source
      a c D I hlength i hi
  have hsourceAt : source.representationAlpha c i <=
      source.truncatedPrefixDefect c 1 i.val i.val := by
    simpa only [← source.coe_representationAlphaValue c i] using hsource i
  have hold : target.representationAlpha c i <=
      source.truncatedPrefixDefect c 1 i.val i.val :=
    hcomparison.trans hsourceAt
  rw [hmixed]
  constructor
  · intro h
    exact WithTop.coe_le_coe.mp (h.trans (min_le_right _ _))
  · intro hbeta
    have holdValue :
        ((target.representationAlphaValue c i : ℚ) : WithTop ℚ) <=
          source.truncatedPrefixDefect c 1 i.val i.val := by
      rw [target.coe_representationAlphaValue]
      exact hold
    exact le_min holdValue (WithTop.coe_le_coe.mpr hbeta)

end BONG.GoodBONG

end Bong
