/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaComplete
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma79DefectOneCap
import Bong.Bong.Beli2019Remark87

/-!
# Beli (2019), Lemma 9.12: the first two type-III defect boundaries

The high boundaries of condition 2.1(ii) were settled by the three gap
branches.  This file treats the two exceptional low boundaries exactly as in
the paper.  At the first boundary, Lemma 8.12 and capped-defect domination
give the result.  At the second boundary, the representation invariant is at
most one, while the two alpha caps and the even-order prefix product are at
least one.
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

/-- The defect-one closing argument in the mixed-ambient form needed by
Lemma 9.12.  The original Lemma 7.9 helper used two lattices in one ambient
space, but its proof only concerns their BONG square classes. -/
theorem representationDefectAt_of_alpha_le_one_and_even_mixed
    [PerfectResidueFieldLaws K]
    {n : Nat}
    (b : GoodBONG q L (n + 1)) (c : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : b.representationAlphaValue c i ≤ 1)
    (hb : (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      have := i.pos
      omega⟩)
    (hc : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      have := i.pos
      omega⟩)
    (heven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
      (1 * b.prefixProduct i.val * c.prefixProduct i.val) := by
    simpa only [one_mul] using defectOrder_one_le_of_even
      (b.prefixProduct i.val * c.prefixProduct i.val) heven
  have hbCap : (1 : WithTop ℚ) ≤ b.prefixAlphaCap i.val := by
    rw [b.prefixAlphaCap_of_internal i.pos i.lt_large]
    exact_mod_cast hb
  have hcCap : (1 : WithTop ℚ) ≤ c.prefixAlphaCap i.val := by
    rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
    exact_mod_cast hc
  have htruncated : (1 : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
    unfold truncatedPrefixDefect
    exact le_min hraw (le_min hbCap hcCap)
  exact (show (b.representationAlphaValue c i : WithTop ℚ) ≤ 1 by
    exact_mod_cast hAlpha).trans htruncated

/-- When the first and third orders agree and the second alpha is one, the
first alpha is the first order gap plus one. -/
theorem firstAlpha_eq_orderGap_add_one_of_outer_eq_of_secondAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    (source : GoodBONG q L (T + 3))
    (houter : source.order (0 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)))
    (hsecondAlpha : source.alphaValue (1 : Fin (T + 2)) = 1) :
    source.alphaValue (0 : Fin (T + 2)) =
      ((source.orderGap (0 : Fin (T + 2)) + 1 : Int) : ℚ) := by
  have hremark := source.beli2019Remark87 (0 : Fin (T + 1)) houter
  have hformula := hremark.previousAlpha_eq
  change source.alphaValue (0 : Fin (T + 2)) =
    ((source.order (1 : Fin (T + 3)) -
      source.order (2 : Fin (T + 3)) : Int) : ℚ) +
      source.alphaValue (1 : Fin (T + 2)) at hformula
  rw [← houter, hsecondAlpha] at hformula
  push_cast at hformula ⊢
  have hsucc : Fin.succ (0 : Fin (T + 2)) =
      (1 : Fin (T + 3)) := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt]
  have hcast : Fin.castSucc (0 : Fin (T + 2)) =
      (0 : Fin (T + 3)) := by
    apply Fin.ext
    simp
  rw [orderGap, hsucc, hcast]
  push_cast
  exact hformula

/-- The first alpha of the type-III image is the source first alpha. -/
theorem beli2019Lemma912_typeIII_firstAlpha_eq_source
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hsecondAlpha : (a.castLength hlength).alphaValue
      (1 : Fin (T + 2)) = 1)
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hfirstGapLe : (a.castLength hlength).orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2) :
    (I.bong.castLength hlength).alphaValue (0 : Fin (T + 2)) =
      (a.castLength hlength).alphaValue (0 : Fin (T + 2)) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hzero : target.order (0 : Fin (T + 3)) =
      source.order (0 : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_zero
      a D I hlength
  have hone : target.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_one
      a D I hlength
  have hsucc : Fin.succ (0 : Fin (T + 2)) =
      (1 : Fin (T + 3)) := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt]
  have hcast : Fin.castSucc (0 : Fin (T + 2)) =
      (0 : Fin (T + 3)) := by
    apply Fin.ext
    simp
  have hgap : target.orderGap (0 : Fin (T + 2)) =
      source.orderGap (0 : Fin (T + 2)) + 1 := by
    unfold orderGap
    rw [hsucc, hcast, hzero, hone]
    omega
  have hfirstGapEven' : Even
      (source.orderGap (0 : Fin (T + 2))) := by
    simpa only [source] using hfirstGapEven
  have hfirstGapLe' : source.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    simpa only [source] using hfirstGapLe
  have hgapOdd : Odd (target.orderGap (0 : Fin (T + 2))) := by
    rcases hfirstGapEven' with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hgap, hz]
    omega
  have hgapLe : target.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) := by
    rw [hgap]
    omega
  have htarget :=
    (target.alpha_p3 (0 : Fin (T + 2)) hgapLe).2.mpr (Or.inr hgapOdd)
  have hsource :=
    source.firstAlpha_eq_orderGap_add_one_of_outer_eq_of_secondAlpha_eq_one
      houter hsecondAlpha
  rw [htarget, hgap, hsource]

/-- Condition 2.1(ii) at the first boundary of the type-III image. -/
theorem beli2019Lemma912_typeIII_defectAt_one
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hsecondAlpha : (a.castLength hlength).alphaValue
      (1 : Fin (T + 2)) = 1)
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hfirstGapLe : (a.castLength hlength).orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2) :
    let first := firstRepresentationIndex (T + 1) (T + 2)
    ((I.bong.castLength hlength).representationAlphaValue c first :
        WithTop ℚ) ≤
      (I.bong.castLength hlength).truncatedPrefixDefect
        c 1 first.val first.val := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let first := firstRepresentationIndex (T + 1) (T + 2)
  have hzero : target.order (0 : Fin (T + 3)) =
      source.order (0 : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_zero
      a D I hlength
  have hbeta : target.alphaValue (0 : Fin (T + 2)) =
      source.alphaValue (0 : Fin (T + 2)) :=
    beli2019Lemma912_typeIII_firstAlpha_eq_source
      a D I hlength houter hsecondAlpha hfirstGapEven hfirstGapLe
  have hsourceTarget :=
    (I.sourceRepresentationConditions a D hlength).defectCondition first
  have hsourceTargetAlpha : source.representationAlpha target first =
      (source.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) :=
    source.beli2019Lemma812_i target hzero.symm
  have hsourceTargetLower :
      (source.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
        source.truncatedPrefixDefect target 1 first.val first.val := by
    rw [← hsourceTargetAlpha, ← source.coe_representationAlphaValue]
    exact hsourceTarget
  have hsourceComparisonAlpha : source.representationAlpha c first =
      (source.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) :=
    source.beli2019Lemma812_i c hfirst
  have hsourceComparisonLower :
      (source.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
        source.truncatedPrefixDefect c 1 first.val first.val := by
    rw [← hsourceComparisonAlpha, ← source.coe_representationAlphaValue]
    exact hsource first
  have htargetComparisonAlpha : target.representationAlpha c first =
      (target.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) :=
    target.beli2019Lemma812_i c (hzero.trans hfirst)
  have hdom := target.truncatedPrefixDefect_domination
    source c 1 1 first.val first.val first.val
  rw [target.truncatedPrefixDefect_comm source 1 first.val first.val,
    one_mul] at hdom
  change (target.representationAlphaValue c first : WithTop ℚ) ≤
    target.truncatedPrefixDefect c 1 first.val first.val
  rw [target.coe_representationAlphaValue, htargetComparisonAlpha, hbeta]
  exact (le_min hsourceTargetLower hsourceComparisonLower).trans hdom

/-- At the second boundary the type-III comparison invariant is at most
one.  This is the displayed estimate `B₂ ≤ S₃-T₂+γ₁ = 1`. -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_two_le_one
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hsecondAlpha : (a.castLength hlength).alphaValue
      (1 : Fin (T + 2)) = 1)
    (hfirstAlpha : (a.castLength hlength).alphaValue
      (0 : Fin (T + 2)) = c.alphaValue (0 : Fin (T + 2))) :
    let second := secondRepresentationIndex T (T + 1)
    (I.bong.castLength hlength).representationAlphaValue c second ≤ 1 := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let second := secondRepresentationIndex T (T + 1)
  have htwo : target.order (2 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_two
      a D I hlength
  have hsourceAlpha : source.alphaValue (0 : Fin (T + 2)) =
      ((source.orderGap (0 : Fin (T + 2)) + 1 : Int) : ℚ) :=
    source.firstAlpha_eq_orderGap_add_one_of_outer_eq_of_secondAlpha_eq_one
      houter hsecondAlpha
  have hprimary := target.representationAlpha_le_primary c second
  have hcap' : target.truncatedPrefixDefect c (-1) 3 1 ≤
      (c.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) := by
    have hcap := target.truncatedPrefixDefect_le_rightCap c (-1) 3 1
    rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    exact hcap
  have hprimary' : target.representationAlpha c second ≤
      ((((target.order (2 : Fin (T + 3)) -
          c.order (1 : Fin (T + 3)) : Int) : ℚ) : WithTop ℚ) +
        (c.alphaValue (0 : Fin (T + 2)) : WithTop ℚ)) := by
    apply hprimary.trans
    unfold representationPrimaryDefect
    dsimp only [second, secondRepresentationIndex]
    convert add_le_add_right hcap'
      (((target.order (2 : Fin (T + 3)) -
        c.order (1 : Fin (T + 3)) : Int) : ℚ) : WithTop ℚ) using 1 <;>
      congr 2 <;> apply Fin.ext <;> simp [Nat.mod_eq_of_lt]
  have hone :
      ((((target.order (2 : Fin (T + 3)) -
          c.order (1 : Fin (T + 3)) : Int) : ℚ) : WithTop ℚ) +
        (c.alphaValue (0 : Fin (T + 2)) : WithTop ℚ)) = 1 := by
    rw [htwo, hsecond, ← houter, ← hfirstAlpha, hsourceAlpha]
    unfold orderGap
    have hsucc : Fin.succ (0 : Fin (T + 2)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hcast : Fin.castSucc (0 : Fin (T + 2)) =
        (0 : Fin (T + 3)) := by
      apply Fin.ext
      simp
    rw [hsucc, hcast]
    norm_cast
    push_cast
    ring
  have hvalue :
      ((target.representationAlphaValue c second : ℚ) : WithTop ℚ) ≤
        (1 : WithTop ℚ) := by
    rw [target.coe_representationAlphaValue]
    exact hprimary'.trans_eq hone
  change target.representationAlphaValue c second ≤ 1
  exact WithTop.coe_le_coe.mp hvalue

/-- The image alpha at the second boundary is nonzero, hence at least one. -/
theorem beli2019Lemma912_typeIII_secondAlpha_one_le
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (houter : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hfirstGapLe : (a.castLength hlength).orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2) :
    (1 : ℚ) ≤ (I.bong.castLength hlength).alphaValue
      (1 : Fin (T + 2)) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have houter' : source.order (0 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)) := by
    simpa only [source] using houter
  have hfirstGapLe' : source.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    simpa only [source] using hfirstGapLe
  have hone : target.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_one
      a D I hlength
  have htwo : target.order (2 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_two
      a D I hlength
  have hne : target.alphaValue (1 : Fin (T + 2)) ≠ 0 := by
    intro hzero
    have hgap := (target.alpha_p2 (1 : Fin (T + 2))).2.mp hzero
    have hsuccOne : Fin.succ (1 : Fin (T + 2)) =
        (2 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hcastOne : Fin.castSucc (1 : Fin (T + 2)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hsuccZero : Fin.succ (0 : Fin (T + 2)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hcastZero : Fin.castSucc (0 : Fin (T + 2)) =
        (0 : Fin (T + 3)) := by
      apply Fin.ext
      simp
    unfold orderGap at hgap hfirstGapLe'
    rw [hsuccOne, hcastOne, htwo, hone, ← houter'] at hgap
    rw [hsuccZero, hcastZero] at hfirstGapLe'
    omega
  exact target.one_le_alphaValue_of_ne_zero (1 : Fin (T + 2)) hne

/-- The comparison alpha at the second boundary is nonzero, hence at least
one. -/
theorem beli2019Lemma912_typeIII_comparisonSecondAlpha_one_le
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    (comparisonParity : Beli2009AlphaParityLaws.{u, w} K)
    (source : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (hfirst : source.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1)
    (houter : source.order (0 : Fin (T + 3)) =
      source.order (2 : Fin (T + 3)))
    (hfirstGapEven : Even (source.orderGap (0 : Fin (T + 2))))
    (hfirstGapLe : source.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) - 2) :
    (1 : ℚ) ≤ c.alphaValue (1 : Fin (T + 2)) := by
  letI : Beli2006AlphaLaws.{u, w} K := comparisonAlpha
  letI : Beli2009AlphaParityLaws.{u, w} K := comparisonParity
  have hthird : c.order (0 : Fin (T + 3)) <
      c.order (2 : Fin (T + 3)) :=
    beli2019Lemma912_typeIII_comparisonThird_gt_first
      source c hfirst hsecond houter hfirstGapEven
  have hthirdSource : source.order (0 : Fin (T + 3)) <
      c.order (2 : Fin (T + 3)) := hfirst.trans_lt hthird
  have hne : c.alphaValue (1 : Fin (T + 2)) ≠ 0 := by
    intro hzero
    have hgap := (c.alpha_p2 (1 : Fin (T + 2))).2.mp hzero
    have hsuccOne : Fin.succ (1 : Fin (T + 2)) =
        (2 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hcastOne : Fin.castSucc (1 : Fin (T + 2)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hsuccZero : Fin.succ (0 : Fin (T + 2)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt]
    have hcastZero : Fin.castSucc (0 : Fin (T + 2)) =
        (0 : Fin (T + 3)) := by
      apply Fin.ext
      simp
    unfold orderGap at hgap hfirstGapLe
    rw [hsuccOne, hcastOne] at hgap
    rw [hsuccZero, hcastZero] at hfirstGapLe
    rw [hsecond] at hgap
    omega
  exact c.one_le_alphaValue_of_ne_zero (1 : Fin (T + 2)) hne

/-- The two-term image and comparison prefixes have the same total order,
so their product has even valuation. -/
theorem beli2019Lemma912_typeIII_secondPrefixProduct_order_even
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1) :
    Even (ordUnit K
      ((I.bong.castLength hlength).prefixProduct 2 * c.prefixProduct 2)) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hzero : target.order (0 : Fin (T + 3)) =
      source.order (0 : Fin (T + 3)) :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_zero
      a D I hlength
  have hone : target.order (1 : Fin (T + 3)) =
      source.order (1 : Fin (T + 3)) + 1 :=
    beli2019Lemma912TypeIIIIndexPData_order_castLength_one
      a D I hlength
  apply target.comparisonPrefixProduct_order_even_of_prefixSum_modEq
    c 2 (by omega) (by omega)
  have hsum : target.orderSequence.prefixSum 2 =
      c.orderSequence.prefixSum 2 := by
    rw [target.orderSequence.prefixSum_succ 1,
      target.orderSequence.prefixSum_one,
      c.orderSequence.prefixSum_succ 1,
      c.orderSequence.prefixSum_one,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt,
      BeliOrderSequence.entryOrZero_of_lt]
    change target.order (0 : Fin (T + 3)) +
        target.order (1 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)) + c.order (1 : Fin (T + 3))
    rw [hzero, hone, ← hfirst, hsecond]
  rw [hsum]

/-- Condition 2.1(ii) at the second boundary of the type-III image. -/
theorem beli2019Lemma912_typeIII_defectAt_two
    [PerfectResidueFieldLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    (comparisonParity : Beli2009AlphaParityLaws.{u, w} K)
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
    let second := secondRepresentationIndex T (T + 1)
    ((I.bong.castLength hlength).representationAlphaValue c second :
        WithTop ℚ) ≤
      (I.bong.castLength hlength).truncatedPrefixDefect
        c 1 second.val second.val := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let second := secondRepresentationIndex T (T + 1)
  have hAlpha := beli2019Lemma912_typeIII_representationAlphaValue_two_le_one
    (sourceAlpha := sourceAlpha)
      a c D I hlength hsecond houter hsecondAlpha hfirstAlpha
  have hbeta := beli2019Lemma912_typeIII_secondAlpha_one_le
    (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
      a D I hlength houter hfirstGapLe
  have hgamma := beli2019Lemma912_typeIII_comparisonSecondAlpha_one_le
    (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
      comparisonAlpha comparisonParity source c hfirst hsecond houter
        hfirstGapEven hfirstGapLe
  have heven := beli2019Lemma912_typeIII_secondPrefixProduct_order_even
    a c D I hlength hfirst hsecond
  change (target.representationAlphaValue c second : WithTop ℚ) ≤
    target.truncatedPrefixDefect c 1 second.val second.val
  exact target.representationDefectAt_of_alpha_le_one_and_even_mixed
    c second hAlpha hbeta hgamma heven

end BONG.GoodBONG

end Bong
