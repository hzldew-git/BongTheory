/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaLargeGap
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 9.12: the type-III even small-gap branch

If `S_4 - S_3 < 2e` is even, property P3 and integrality force
`beta_3 >= S_4 - S_3 + 1`.  The latter quantity is the third source
gap, which is odd; P3 identifies it with `alpha_3`.  Property P1 then
shows that every later source alpha is at most the shifted `beta_3`
candidate.  This is the contradiction argument in the paper, stated
directly as the resulting `B_i <= beta_i` bound.
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

/-- The even branch below `2e` in the proof of Lemma 9.12(ii). -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_lt_even
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val)
    (hgapLt : (I.bong.castLength hlength).orderGap
        (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 2)) <
      2 * (ramificationIndex K : Int))
    (hgapEven : Even ((I.bong.castLength hlength).orderGap
      (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 2)))) :
    (I.bong.castLength hlength).representationAlphaValue c i <=
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have hlt := i.lt_large; omega⟩ := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceAlpha
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
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
  have hleft : target.representationAlphaValue c i <=
      source.alphaValue current := by
    apply hcomparison.trans
    exact WithTop.coe_le_coe.mp (by
      simpa only [current] using hsourceAlphaTop)
  have htargetGapLe : target.orderGap first <=
      2 * (ramificationIndex K : Int) := by
    exact (by simpa only [target, first] using hgapLt.le)
  have htargetLower : (target.orderGap first : Rat) <=
      target.alphaValue first :=
    (target.beli2009Lemma27_iii first htargetGapLe).1
  have htargetNotOdd : ¬ Odd (target.orderGap first) :=
    Int.not_odd_iff_even.mpr (by simpa only [target, first] using hgapEven)
  have htargetStrict : (target.orderGap first : Rat) <
      target.alphaValue first := by
    apply lt_of_le_of_ne htargetLower
    intro heq
    rcases (target.beli2009Lemma27_iii first htargetGapLe).2.mp heq.symm with
      hendpoint | hodd
    · have hlt : target.orderGap first <
          2 * (ramificationIndex K : Int) := by
        simpa only [target, first] using hgapLt
      exact (ne_of_lt hlt) hendpoint
    · exact htargetNotOdd hodd
  have htargetInteger : IsRationalInteger (target.alphaValue first) :=
    target.beli2009Corollary28_i first (by
      rintro ⟨hodd, _⟩
      exact htargetNotOdd hodd)
  have htargetNext : (((target.orderGap first + 1 : Int) : Rat)) <=
      target.alphaValue first := by
    rcases htargetInteger with ⟨z, hz⟩
    have hgapZ : target.orderGap first < z := by
      rw [hz] at htargetStrict
      exact_mod_cast htargetStrict
    rw [hz]
    exact_mod_cast (show target.orderGap first + 1 <= z by omega)
  have hfirstCast : first.castSucc =
      (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have hfirstSucc : first.succ =
      (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (T + 3)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have htargetTwo : target.order
        (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) =
      source.order
          (⟨2, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) + 1 := by
    simp only [target, source, GoodBONG.order_castLength]
    have htwoRaw :
        (⟨2, by omega⟩ : Fin (3 + T)) = (2 : Fin (3 + T)) := by
      apply Fin.ext
      change 2 = 2 % (3 + T)
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [htwoRaw]
    exact beli2019Lemma912TypeIIIIndexPData_order_two a D I
  have htargetThree : target.order
        (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) =
      source.order
        (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) := by
    exact
      beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength ⟨3, by have hlt := i.lt_large; omega⟩ (by rfl)
  have htargetCurrent : target.order ⟨i.val, i.lt_large⟩ =
      source.order ⟨i.val, i.lt_large⟩ := by
    exact
      beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength ⟨i.val, i.lt_large⟩ hi
  have hgapRelation : source.orderGap first = target.orderGap first + 1 := by
    unfold orderGap
    rw [hfirstSucc, hfirstCast, htargetTwo, htargetThree]
    omega
  have hsourceGapOdd : Odd (source.orderGap first) := by
    rcases (show Even (target.orderGap first) by
      simpa only [target, first] using hgapEven) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hgapRelation, hz]
    omega
  have hsourceGapLe : source.orderGap first <=
      2 * (ramificationIndex K : Int) := by
    rw [hgapRelation]
    have hlt : target.orderGap first <
        2 * (ramificationIndex K : Int) := by
      simpa only [target, first] using hgapLt
    omega
  have hsourceFirst : source.alphaValue first =
      (source.orderGap first : Rat) :=
    (source.beli2009Lemma27_iii first hsourceGapLe).2.mpr
      (Or.inr hsourceGapOdd)
  have hsourceFirstLeTarget : source.alphaValue first <=
      target.alphaValue first := by
    rw [hsourceFirst, hgapRelation]
    exact htargetNext
  have hendpoint := source.alphaRightEndpoint_antitone
    (show first <= current by
      change 2 <= i.val - 1
      omega)
  unfold alphaRightEndpoint at hendpoint
  rw [hfirstSucc, hcurrentSucc] at hendpoint
  have hsourceShift : source.alphaValue current <=
      (((source.order ⟨i.val, i.lt_large⟩ -
          source.order
            (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Int) :
            Rat) + target.alphaValue first) := by
    push_cast at hendpoint ⊢
    linarith [hsourceFirstLeTarget]
  have hsourceShiftTarget : source.alphaValue current <=
      (((target.order ⟨i.val, i.lt_large⟩ -
          target.order
            (⟨3, by have hlt := i.lt_large; omega⟩ : Fin (T + 3)) : Int) :
            Rat) + target.alphaValue first) := by
    rw [htargetCurrent, htargetThree]
    exact hsourceShift
  rw [beli2019Lemma912_typeIII_alphaValue_eq_min_sourceAlpha_shift
    (alpha := sourceAlpha) a D I hlength i hi]
  exact le_min (by simpa only [source, current] using hleft)
    (by
      apply hleft.trans
      simpa only [target, first] using hsourceShiftTarget)

end BONG.GoodBONG

end Bong
