/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIICentralBounds

/-!
# Beli (2019), Lemma 9.12: the two low central indices

The first possible central trigger, at index two, is contradictory: its two
representation invariants sum to at most `2e`.  The next file will use the
index-three definition together with Lemma 2.14 and the auxiliary `+1` bound.
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

/-- The first possible index in condition 2.1(iii). -/
def beli2019Lemma912TypeIIISecondCentralIndex :
    CentralRepresentationIndex (T + 3) (T + 3) where
  val := 2
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- The exceptional next index in condition 2.1(iii). -/
def beli2019Lemma912TypeIIIThirdCentralIndex (hT : 0 < T) :
    CentralRepresentationIndex (T + 3) (T + 3) where
  val := 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- The type-III central-alpha trigger at the first possible index is
impossible.  This is the paper's estimate
`B_1 + B_2 <= (R_2-R_1+1)+1 <= 2e`. -/
theorem beli2019Lemma912_typeIII_not_secondCentralAlphaTrigger
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hsecondAlpha : (a.castLength hlength).alphaValue
      (1 : Fin (T + 2)) = 1)
    (hfirstAlpha : (a.castLength hlength).alphaValue
      (0 : Fin (T + 2)) = c.alphaValue (0 : Fin (T + 2)))
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hfirstGapLe : (a.castLength hlength).orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2) :
    ¬ (I.bong.castLength hlength).centralAlphaTrigger c
      (beli2019Lemma912TypeIIISecondCentralIndex (T := T)) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let first : RepresentationIndex (T + 3) (T + 3) := {
    val := 1
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  let second : RepresentationIndex (T + 3) (T + 3) := {
    val := 2
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  let central := beli2019Lemma912TypeIIISecondCentralIndex (T := T)
  have hzero : target.order (0 : Fin (T + 3)) =
      source.order (0 : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_zero
      a D I hlength
  have hone : target.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_one
      a D I hlength
  have htargetComparisonOne : target.order (1 : Fin (T + 3)) =
      c.order (1 : Fin (T + 3)) := hone.trans hsecond.symm
  have hbeta : target.alphaValue (0 : Fin (T + 2)) =
      source.alphaValue (0 : Fin (T + 2)) :=
    beli2019Lemma912_typeIII_firstAlpha_eq_source
      a D I hlength houter hsecondAlpha hfirstGapEven hfirstGapLe
  have htargetFirst : target.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)) := hzero.trans hfirst
  have hfirstRepresentation : target.representationAlpha c first =
      (target.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) := by
    simpa only [first, firstRepresentationIndex] using
      target.beli2019Lemma812_i c htargetFirst
  have hBOne : target.representationAlphaValue c first =
      source.alphaValue (0 : Fin (T + 2)) := by
    apply WithTop.coe_eq_coe.mp
    rw [target.coe_representationAlphaValue, hfirstRepresentation, hbeta]
  have hsourceFormula : source.alphaValue (0 : Fin (T + 2)) =
      ((source.orderGap (0 : Fin (T + 2)) + 1 : Int) : ℚ) :=
    source.firstAlpha_eq_orderGap_add_one_of_outer_eq_of_secondAlpha_eq_one
      houter hsecondAlpha
  have hBOneLe : target.representationAlphaValue c first ≤
      (2 * (ramificationIndex K : ℚ) - 1 : ℚ) := by
    rw [hBOne, hsourceFormula]
    have hgap : source.orderGap (0 : Fin (T + 2)) + 1 ≤
        2 * (ramificationIndex K : Int) - 1 := by
      have hgapLe : source.orderGap (0 : Fin (T + 2)) ≤
          2 * (ramificationIndex K : Int) - 2 := by
        simpa only [source] using hfirstGapLe
      omega
    exact_mod_cast hgap
  have hBTwo : target.representationAlphaValue c second ≤ 1 := by
    simpa only [second, secondRepresentationIndex] using
      beli2019Lemma912_typeIII_representationAlphaValue_two_le_one
        (sourceAlpha := sourceAlpha) a c D I hlength hsecond houter
          hsecondAlpha hfirstAlpha
  intro htrigger
  have hsum := htrigger.2
  unfold centralAdjustedAlpha at hsum
  rw [dif_pos (show central.val ≤ T + 3 by
    simp only [central, beli2019Lemma912TypeIIISecondCentralIndex]
    omega)] at hsum
  simp only [beli2019Lemma912TypeIIISecondCentralIndex,
    CentralRepresentationIndex.previous,
    CentralRepresentationIndex.current,
    Nat.reduceSub] at hsum
  norm_cast at hsum
  push_cast at hsum
  have htargetComparisonOne' :
      target.order (⟨1, by omega⟩ : Fin (T + 3)) =
        c.order (⟨1, by omega⟩ : Fin (T + 3)) := by
    convert htargetComparisonOne using 1 <;> congr 1 <;> apply Fin.ext <;>
      simp [Nat.mod_eq_of_lt (by omega)]
  rw [htargetComparisonOne'] at hsum
  dsimp only [target, first, second] at hBOneLe hBTwo
  linarith

end BONG.GoodBONG

end Bong
