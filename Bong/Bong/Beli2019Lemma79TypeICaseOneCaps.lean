/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneProfile
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 7.9(ii), case 1: the two prefix caps

In the exceptional case the comparison half-gap is the half-gap at the
boundary of the `b` prefix.  Condition 2.1(i) makes the corresponding gap of
`c` at least as large.  The large-gap formula for alpha therefore bounds the
comparison invariant by both prefix caps.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Both endpoint caps dominate the comparison alpha in case 1. -/
theorem beli2019Lemma79_typeI_caseOne_prefixCaps
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        b.prefixAlphaCap i.val ∧
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        c.prefixAlphaCap i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  have hpreviousSucc : previous.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ, Nat.sub_add_cancel i.pos]
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hgapPrevious : b.orderGap previous =
      2 * (ramificationIndex K : Int) + 1 := by
    simpa only [previous] using hgap
  have hgapLarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap previous := by
    omega
  have hbAlpha := b.beli2009Lemma27_ii previous hgapLarge
  have hhalfB : b.representationHalfGap c i =
      (b.halfGapValue previous : WithTop ℚ) := by
    unfold representationHalfGap halfGapValue orderGap
    rw [hpreviousSucc, hpreviousCast, hprevious]
  have hcurrentLe : b.order ⟨i.val, i.lt_large⟩ ≤
      c.order ⟨i.val, i.lt_large⟩ := by
    rcases horderBC ⟨i.val, i.lt_large⟩ with hcurrent | ⟨_, hiNext, hpair⟩
    · exact hcurrent
    · have htwoStep := b.good ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ (by
          change (i.val - 1) + 2 < n + 2
          have hiNextNat : i.val + 1 < n + 2 := hiNext
          have hiPos := i.pos
          omega)
      change b.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ ≤ b.order ⟨(i.val - 1) + 2, by
          have hiNextNat : i.val + 1 < n + 2 := hiNext
          have hiPos := i.pos
          omega⟩ at htwoStep
      have htwoStep' : b.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ ≤ b.order ⟨i.val + 1, hiNext⟩ := by
        have hnextEq : (⟨(i.val - 1) + 2, by
              have hiNextNat : i.val + 1 < n + 2 := hiNext
              have hiPos := i.pos
              omega⟩ : Fin (n + 2)) = ⟨i.val + 1, hiNext⟩ := by
          apply Fin.ext
          simp only
          have hiPos := i.pos
          omega
        rw [hnextEq] at htwoStep
        exact htwoStep
      have hpair' : b.order ⟨i.val, i.lt_large⟩ +
            b.order ⟨i.val + 1, hiNext⟩ ≤
          c.order ⟨i.val - 1, by
              have hiBound := i.lt_large
              omega⟩ + c.order ⟨i.val, i.lt_large⟩ := by
        simpa only using hpair
      rw [hprevious] at hpair'
      omega
  have hgapLe : b.orderGap previous ≤ c.orderGap previous := by
    unfold orderGap
    rw [hpreviousSucc, hpreviousCast, hprevious]
    omega
  have hcGapLarge : 2 * (ramificationIndex K : Int) ≤
      c.orderGap previous := hgapLarge.trans hgapLe
  have hcAlpha := c.beli2009Lemma27_ii previous hcGapLarge
  have hhalfQ : b.halfGapValue previous ≤
      c.halfGapValue previous := by
    have hgapQ : (b.orderGap previous : ℚ) ≤
        (c.orderGap previous : ℚ) := by
      exact_mod_cast hgapLe
    unfold halfGapValue
    linarith
  have hhalfTop : (b.halfGapValue previous : WithTop ℚ) ≤
      (c.halfGapValue previous : WithTop ℚ) := by
    exact_mod_cast hhalfQ
  have halphaHalf := b.representationAlpha_le_halfGap c i
  constructor
  · rw [b.prefixAlphaCap_of_internal i.pos i.lt_large]
    rw [b.coe_representationAlphaValue c i]
    calc
      b.representationAlpha c i ≤
          b.representationHalfGap c i := halphaHalf
      _ = (b.halfGapValue previous : WithTop ℚ) := hhalfB
      _ = (b.alphaValue previous : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hbAlpha.symm
      _ = (b.alphaValue ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ : WithTop ℚ) := by
        rfl
  · rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
    rw [b.coe_representationAlphaValue c i]
    calc
      b.representationAlpha c i ≤
          b.representationHalfGap c i := halphaHalf
      _ = (b.halfGapValue previous : WithTop ℚ) := hhalfB
      _ ≤ (c.halfGapValue previous : WithTop ℚ) := hhalfTop
      _ = (c.alphaValue previous : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hcAlpha.symm
      _ = (c.alphaValue ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ : WithTop ℚ) := by
        rfl

end BONG.GoodBONG

end Bong
