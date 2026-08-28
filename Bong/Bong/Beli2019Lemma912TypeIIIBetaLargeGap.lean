/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBeta
import Bong.Bong.Beli2019RepresentationSourceHalfGap

/-!
# Beli (2019), Lemma 9.12: the type-III large-gap beta bound

This file proves the first branch of the parity argument establishing
`B_i <= beta_i` for the type-III index-uniformizer construction.  When
`S_4 - S_3 >= 2e`, property P4 identifies `beta_3` with its half-gap.
Monotonicity of adjacent order sums then compares the shifted `beta_3`
candidate with the source self half-gap at every later boundary.
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

/-- The large third-gap branch in the proof of Lemma 9.12(ii): if
`S_4 - S_3 >= 2e`, then every type-III comparison invariant from the
third boundary onward is bounded by the corresponding `beta_i`. -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_ge
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (horder : (I.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val)
    (hgap : 2 * (ramificationIndex K : Int) <=
      (I.bong.castLength hlength).orderGap
        (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 2))) :
    (I.bong.castLength hlength).representationAlphaValue c i <=
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have hlt := i.lt_large; omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceAlpha
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let first : Fin (T + 2) := ⟨2, by
    have hlt := i.lt_large
    omega⟩
  let current : Fin (T + 2) := ⟨i.val - 1, by
    have hlt := i.lt_large
    omega⟩
  have hcomparison : target.representationAlphaValue c i <=
      source.representationAlphaValue c i :=
    beli2019Lemma912_typeIII_representationAlphaValue_le_source
      (alpha := sourceAlpha) a c D I hlength i hi
  have hsourceAlphaTop := source.representationAlpha_le_leftAlpha c hsource i
  rw [← source.coe_representationAlphaValue c i] at hsourceAlphaTop
  have hsourceAlpha : source.representationAlphaValue c i <=
      source.alphaValue current := by
    exact WithTop.coe_le_coe.mp (by
      simpa only [current] using hsourceAlphaTop)
  have hleft : target.representationAlphaValue c i <=
      source.alphaValue current := hcomparison.trans hsourceAlpha
  have hselfHalf : target.representationAlphaValue c i <=
      target.halfGapValue current := by
    letI : Beli2006AlphaLaws.{u, w} K := comparisonAlpha
    exact target.representationAlphaValue_le_sourceHalfGapValue_of_orderCondition
      c horder i
  have hfirstAlpha : target.alphaValue first = target.halfGapValue first := by
    exact target.alpha_p4 first (by simpa only [target, first] using hgap)
  have hpair : target.adjacentOrderSum first <=
      target.adjacentOrderSum current := by
    exact target.adjacentOrderSum_monotone (show first <= current by
      change 2 <= i.val - 1
      omega)
  have hfirstCast : first.castSucc =
      (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have hfirstSucc : first.succ =
      (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (T + 3)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  unfold adjacentOrderSum at hpair
  rw [hfirstCast, hfirstSucc, hcurrentCast, hcurrentSucc] at hpair
  have hhalfShift : target.halfGapValue current <=
      (((target.order ⟨i.val, i.lt_large⟩ -
          target.order
            (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Int) :
            Rat) + target.alphaValue first) := by
    rw [hfirstAlpha]
    unfold halfGapValue orderGap
    rw [hcurrentSucc, hcurrentCast, hfirstSucc, hfirstCast]
    have hpairQ :
        (target.order
            (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Rat) +
            (target.order
              (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Rat) <=
          (target.order
            (⟨i.val - 1, by have hlt := i.lt_large; omega⟩ :
              Fin (T + 3)) : Rat) +
            (target.order ⟨i.val, i.lt_large⟩ : Rat) := by
      exact_mod_cast hpair
    push_cast at hpairQ ⊢
    linarith
  have hshift : target.representationAlphaValue c i <=
      (((target.order ⟨i.val, i.lt_large⟩ -
          target.order
            (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Int) :
            Rat) + target.alphaValue first) :=
    hselfHalf.trans hhalfShift
  rw [beli2019Lemma912_typeIII_alphaValue_eq_min_sourceAlpha_shift
    (alpha := sourceAlpha) a D I hlength i hi]
  exact le_min (by simpa only [source, current] using hleft)
    (by simpa only [target, first] using hshift)

end BONG.GoodBONG

end Bong
