/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29TargetReduction
import Bong.Bong.Beli2019KeyLemma
import Bong.Bong.Beli2019WeightSequence

/-!
# Beli (2019), Proposition 6.2: the target-alpha candidate

This file isolates the third-candidate contradiction in the proof that
conditions 2.1(i) and 2.1(ii) imply `W(M) ≤ W(N)`.  If the
secondary-previous candidate realizes `A_i`, Lemma 2.9 bounds the
target-alpha replacement by `A_i`.  The source two-step inequality then
gives exactly the second alternative for the even coordinate of `W`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- When the secondary-previous candidate realizes `A_i`, its target-alpha
replacement is no larger than `A_i`. -/
theorem representationSecondaryTargetAlpha_le_representationAlpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hsecondary : a.representationAlpha b i =
      a.representationSecondaryPreviousDefect b i hi)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩) :
    a.representationSecondaryTargetAlpha b i hi i.lt_large ≤
      a.representationAlpha b i := by
  let C := a.representationAlphaValue b i
  have hprevious : a.representationSecondaryPreviousDefect b i hi ≤
      (C : WithTop ℚ) := by
    rw [← hsecondary, a.coe_representationAlphaValue b i]
  have hcomparison : (C : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    exact hdefect i
  have htarget :=
    a.representationSecondaryTargetAlpha_le_of_previous_le_comparison
      b i hi i.lt_large C hprevious hcomparison hshift
  simpa only [C, a.coe_representationAlphaValue b i] using htarget

/-- The target-alpha branch gives the second `W`-comparison alternative at
the corresponding even coordinate. -/
theorem weightSequence_even_pair_of_secondaryPrevious
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hsecondary : a.representationAlpha b i =
      a.representationSecondaryPreviousDefect b i hi)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩) :
    a.order ⟨i.val - 1, by omega⟩ + a.order ⟨i.val, i.lt_large⟩ ≤
      2 * b.order ⟨i.val - 1, by omega⟩ +
        b.alphaValue ⟨i.val - 1, by omega⟩ -
        b.alphaValue ⟨i.val - 2, by omega⟩ := by
  have htarget :=
    a.representationSecondaryTargetAlpha_le_representationAlpha
      b hdefect i hi hsecondary hshift
  have hright := a.representationAlpha_le_rightAlpha b hdefect i
  have htargetBeta :
      a.representationSecondaryTargetAlpha b i hi i.lt_large ≤
        (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) :=
    htarget.trans hright
  unfold representationSecondaryTargetAlpha at htargetBeta
  norm_cast at htargetBeta
  push_cast at htargetBeta
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hstep : previous.val + 2 < n + 1 := by
    simp only [previous]
    omega
  have htwoRaw := a.good previous hstep
  have htwo : a.order ⟨i.val - 1, by omega⟩ ≤
      a.order ⟨i.val + 1, by omega⟩ := by
    unfold order
    simpa only [previous, show i.val - 1 + 2 = i.val + 1 by omega]
      using htwoRaw
  have htwoQ : (a.order ⟨i.val - 1, by omega⟩ : ℚ) ≤
      (a.order ⟨i.val + 1, by omega⟩ : ℚ) := by
    exact_mod_cast htwo
  linarith

end BONG.GoodBONG

end Bong
