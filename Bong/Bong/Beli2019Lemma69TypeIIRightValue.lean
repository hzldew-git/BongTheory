/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIISourceLeftValue

/-!
# Beli (2019), Lemma 6.9(ii): type-II right branch

Reverse duality transports the normalized source-left classification to the
target-right interval.  This gives the `A_i = beta_i` identity used in the
type-II part of Lemma 7.9(ii), case 7.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- On a boundary of the alternating right type-II interval, the
representation alpha is the target alpha. -/
theorem beli2019Lemma69_ii_typeII_targetRightValue
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : Nat) (hiStart : D.outer.transition.firstTwo ≤ i)
    (hiParity : Odd (i - (D.outer.transition.firstTwo - 1)))
    (hiNonterminal : i < n + 2) :
    a.representationAlphaValue b
        ⟨i, by
          have hlong := D.long
          omega, hiNonterminal, hiNonterminal.le⟩ =
      b.alphaValue ⟨i - 1, by omega⟩ := by
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i, by
      have hlong := D.long
      omega, hiNonterminal, hiNonterminal.le⟩
  rcases a.exists_reverseDual_typeII b D horder hdefect htotal hlast with
    ⟨aDual, bDual, Ddual, haOrders, hbOrders, _, hbAlpha,
      hDefectMap, hconditionDual, hdualFirst, hdualLeft, _⟩
  have hdualLeftEven := Ddual.outer.left_even_of_first_eq_zero hdualFirst
  have hgapEven : Even (i - D.outer.transition.firstTwo) := by
    rcases hiParity with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    have hlong := D.long
    omega
  have hdualEven : Even idx.reverse.val := by
    have hfirstBound := D.outer.transition.firstTwo_le_rank
    have hdualLeftEven' :
        Even (n + 2 - D.outer.transition.firstTwo) := by
      rw [← hdualLeft]
      exact hdualLeftEven
    have hrankIffFirst : Even (n + 2) ↔
        Even D.outer.transition.firstTwo :=
      (Nat.even_sub hfirstBound).mp hdualLeftEven'
    have hiIffFirst : Even i ↔ Even D.outer.transition.firstTwo :=
      (Nat.even_sub hiStart).mp hgapEven
    have hrankIffI : Even (n + 2) ↔ Even i :=
      hrankIffFirst.trans hiIffFirst.symm
    simpa only [RepresentationIndex.reverse_val, idx] using
      (Nat.even_sub hiNonterminal.le).mpr hrankIffI
  have hdualTwo : 2 ≤ idx.reverse.val := by
    have hpos := idx.reverse.pos
    rcases hdualEven with ⟨d, hd⟩
    omega
  have hdualLeftBound : idx.reverse.val ≤
      Ddual.outer.transition.lastZero := by
    rw [hdualLeft]
    simpa only [RepresentationIndex.reverse_val, idx] using
      Nat.sub_le_sub_left hiStart (n + 2)
  have hdualValue :=
    bDual.beli2019Lemma69_ii_typeII_sourceLeftValue
      aDual Ddual hdualFirst hconditionDual idx.reverse.val hdualTwo
        hdualLeftBound hdualEven
  let dualAlpha : Fin (n + 1) := ⟨idx.reverse.val - 1, by
    have hbound := Ddual.outer.transition.firstTwo_le_rank
    have hlong := Ddual.long
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

end BONG.GoodBONG

end Bong
