/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIICentralThird

/-!
# Beli (2019), Lemma 9.12: condition (iii) beyond the changed prefix

At every central index at least four, both ordinary representation invariants
in the trigger lie in the common tail of the source BONG and its type-III
image.  The image invariants are bounded by the source invariants, while the
two relevant orders agree literally.  Hence an image trigger is already a
source trigger.
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

/-- From the fourth central boundary onward, every target central-alpha
trigger is already a source trigger. -/
theorem beli2019Lemma912_typeIII_centralAlphaTrigger_source_of_target_of_four_le
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : CentralRepresentationIndex (T + 3) (T + 3))
    (hiFour : 4 ≤ i.val)
    (htrigger :
      (I.bong.castLength hlength).centralAlphaTrigger c i) :
    (a.castLength hlength).centralAlphaTrigger c i := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hiCurrent : i.val ≤ T + 3 := i.lt_large.le
  have horderCurrent : target.order
        (⟨i.val, i.lt_large⟩ : Fin (T + 3)) =
      source.order (⟨i.val, i.lt_large⟩ : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength (⟨i.val, i.lt_large⟩ : Fin (T + 3)) (by
        change 3 ≤ i.val
        omega)
  have horderPrevious : target.order
        (⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ :
          Fin (T + 3)) =
      source.order
        (⟨i.val - 1, by have := i.one_lt; have := i.lt_large; omega⟩ :
          Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength
        (⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : Fin (T + 3)) (by
            change 3 ≤ i.val - 1
            omega)
  have hprevious :=
    beli2019Lemma912_typeIII_representationAlphaValue_le_source
      (alpha := sourceAlpha) a c D I hlength i.previous (by
        simp only [CentralRepresentationIndex.previous]
        omega)
  have hcurrent :=
    beli2019Lemma912_typeIII_representationAlphaValue_le_source
      (alpha := sourceAlpha) a c D I hlength (i.current hiCurrent) (by
        simp only [CentralRepresentationIndex.current]
        omega)
  have hpreviousTop :
      ((target.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) ≤
        ((source.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) := by
    exact_mod_cast hprevious
  have hcurrentTop :
      (target.representationAlphaValue c (i.current hiCurrent) : WithTop ℚ) ≤
        (source.representationAlphaValue c (i.current hiCurrent) :
          WithTop ℚ) := by
    exact_mod_cast hcurrent
  have hadjusted : target.centralAdjustedAlpha c i ≤
      source.centralAdjustedAlpha c i := by
    unfold centralAdjustedAlpha
    rw [dif_pos hiCurrent, dif_pos hiCurrent]
    exact add_le_add (le_refl _) hcurrentTop
  have hright :
      ((target.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
          target.centralAdjustedAlpha c i ≤
        ((source.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
          source.centralAdjustedAlpha c i :=
    add_le_add hpreviousTop hadjusted
  unfold centralAlphaTrigger at htrigger ⊢
  refine ⟨htrigger.1.trans_eq horderCurrent, ?_⟩
  rw [horderPrevious] at htrigger
  exact htrigger.2.trans_le hright

end BONG.GoodBONG

end Bong
