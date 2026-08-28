/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIIRightValue
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCenter

/-!
# Beli (2019), Lemma 6.9(ii): type-III right branch from the centre

This isolates the reverse-dual core of the right-interval argument.  The
nonoverlapping proof obtains the target central alpha from Lemma 7.8; the
overlapping proof obtains the same equality from its central gap-one identity.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The reverse-dual right type-III formula, assuming only the target central
alpha equality used by the proof. -/
theorem beli2019Lemma69_ii_typeIII_targetRightValue_of_center
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (htargetCenter : b.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiEven : Even i) (hiNonterminal : i < n + 2) :
    a.representationAlphaValue b
        ⟨i, by omega, hiNonterminal, hiNonterminal.le⟩ =
      b.alphaValue ⟨i - 1, by omega⟩ := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by omega, hiNonterminal, hiNonterminal.le⟩
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have htargetCenter' : b.alphaValue center = 1 := by
    simpa only [center] using htargetCenter
  rcases a.exists_reverseDual_typeIII b D horder hdefect htotal hlast with
    ⟨aDual, bDual, Ddual, haOrders, hbOrders, _, hbAlpha,
      hDefectMap, hconditionDual, hdualFirst, hdualLeft, _⟩
  let dualCenter : Fin (n + 1) :=
    ⟨Ddual.outer.transition.lastZero, by
      have hbound := Ddual.outer.transition.firstTwo_le_rank
      rw [Ddual.adjacent] at hbound
      omega⟩
  have hreverseCenter : Fin.rev dualCenter = center := by
    apply Fin.ext
    simp only [dualCenter, center, Fin.rev]
    rw [hdualLeft, D.adjacent]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hdualCenterOne : bDual.alphaValue dualCenter = 1 := by
    rw [hbAlpha dualCenter, hreverseCenter]
    exact htargetCenter'
  have hleftEven : Even D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hrightLtLast : D.outer.transition.firstTwo - 1 < D.outer.last := by
    rw [hlast, D.adjacent]
    omega
  have hrightParity := (D.outer.rightProfile hrightLtLast).1
  have hrankEven : Even (n + 2) := by
    rcases hleftEven with ⟨d, hd⟩
    rcases hrightParity with ⟨e, he⟩
    refine ⟨e + d + 1, ?_⟩
    rw [hlast, D.adjacent] at he
    omega
  have hdualEven : Even idx.reverse.val := by
    rcases hrankEven with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    refine ⟨d - e, ?_⟩
    simp only [RepresentationIndex.reverse_val, idx]
    omega
  have hdualTwo : 2 ≤ idx.reverse.val := by
    have hpos := idx.reverse.pos
    rcases hdualEven with ⟨d, hd⟩
    omega
  have hdualLeftBound : idx.reverse.val ≤
      Ddual.outer.transition.lastZero := by
    simp only [RepresentationIndex.reverse_val, idx]
    rw [hdualLeft, D.adjacent]
    omega
  have hdualValue :=
    bDual.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
      aDual Ddual hdualFirst (by
        simpa only [dualCenter] using hdualCenterOne)
      hconditionDual idx.reverse.val hdualTwo hdualLeftBound hdualEven
  let dualAlpha : Fin (n + 1) := ⟨idx.reverse.val - 1, by
    have hbound := Ddual.outer.transition.firstTwo_le_rank
    rw [Ddual.adjacent] at hbound
    omega⟩
  have hdualValue' : bDual.representationAlphaValue aDual idx.reverse =
      bDual.alphaValue dualAlpha := by
    simpa only [dualAlpha] using hdualValue
  let targetAlpha : Fin (n + 1) := ⟨i - 1, by omega⟩
  have hreverseAlpha : Fin.rev dualAlpha = targetAlpha := by
    apply Fin.ext
    simp only [dualAlpha, targetAlpha, Fin.rev,
      RepresentationIndex.reverse_val, idx]
    omega
  have hrepresentationMap :=
    a.representationAlphaValue_reverseDual_swap
      b aDual bDual haOrders hbOrders hDefectMap idx
  calc
    a.representationAlphaValue b idx =
        bDual.representationAlphaValue aDual idx.reverse :=
      hrepresentationMap.symm
    _ = bDual.alphaValue dualAlpha := hdualValue'
    _ = b.alphaValue targetAlpha := by rw [hbAlpha dualAlpha, hreverseAlpha]
    _ = b.alphaValue ⟨i - 1, by omega⟩ := by
      apply congrArg b.alphaValue
      apply Fin.ext
      rfl

/-- The right type-III formula in the overlapping type-II/III branch. -/
theorem beli2019Lemma69_ii_typeIII_targetRightValue_of_overlap
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : Nat) (hiStart : D.outer.transition.lastZero + 2 ≤ i)
    (hiEven : Even i) (hiNonterminal : i < n + 2) :
    a.representationAlphaValue b
        ⟨i, by omega, hiNonterminal, hiNonterminal.le⟩ =
      b.alphaValue ⟨i - 1, by omega⟩ := by
  apply a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center
    b D hfirst hlast horder hdefect htotal
  · exact a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one
      b D hlast horder hdefect htotal hoverlap
  · exact hiStart
  · exact hiEven

end BONG.GoodBONG

end Bong
