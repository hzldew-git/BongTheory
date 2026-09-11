/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenMixedTests
import Bong.Bong.Beli2019Lemma65

/-!
# The terminal defect obstruction in He (2025), Lemma 6.5(i)

The conclusion identifies the precise failing inequality of Theorem 3.6(ii),
not only failure of representation. The target BONG is arbitrary on any
integrally isometric copy of either named unit-uniformizer maximal lattice.
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
  {L : Lattice K V} {M : Lattice K W}

/-- At a terminal source index, odd comparison-prefix valuation and a
strict cross-order gap force failure of the single defect inequality there. -/
theorem heADCTerminalDefectCondition_fails {m n : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (hterminal : i.val + 1 = m + 1)
    (hodd : Odd (ordUnit K (a.prefixProduct i.val * b.prefixProduct i.val)))
    (hgap : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩) :
    ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  intro h
  rw [a.truncatedPrefixDefect_eq_zero_of_odd_order b i.val hodd,
    a.coe_representationAlphaValue b i, a.representationAlpha_eq_min_halfGap_prime b i,
    a.representationAlphaPrime_eq_primary_of_not_interior b i (by omega)] at h
  rcases min_le_iff.mp h with hhalf | hprimary
  · exact (not_le_of_gt hgap) (a.sourceNext_le_targetCurrent_of_halfGap_le_zero b i hhalf)
  · exact (not_le_of_gt hgap) (a.sourceNext_le_targetCurrent_of_primary_le_zero b i hprimary)

section PublishedTargets

variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The orders of any good BONG on either named unit-uniformizer maximal
target, including arbitrary integral-isometric copies of the target. -/
theorem heADCUniformizerTest_orders (k : Nat) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (b : GoodBONG r M (2 * k + 2)) (hM : Lattice.IsIntegral r M)
    (hmodel :
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW1Even k (ε * uniformizerPowerUnit K 1)))
        M (heADCN1Even k (ε * uniformizerPowerUnit K 1)).lattice ∨
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)))
        M (heADCN2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)).lattice)
    (i : Fin (2 * k + 2)) :
    b.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] ⟨i.val, by omega⟩ := by
  let b' := b.castLength (by omega : 2 * k + 2 = 2 + 2 * k)
  have H : ∀ j, b'.order j = heADCMaximalOrderProfile (K := K) k ![0, 1] j := by
    rcases hmodel with hOne | hTwo
    · exact (heADC2025Lemma411iiiUniformizerFirstPublished ε hε k b' hM
        ⟨(Classical.choice hOne).toQuadraticSpaceIsometry⟩).mp hOne
    · exact (heADC2025Lemma411iiiUniformizerSecondPublished ε hε k b' hM
        ⟨(Classical.choice hTwo).toQuadraticSpaceIsometry⟩).mp hTwo
  simpa only [b', order_castLength] using H ⟨i.val, by omega⟩

/-- The order-profile form of He (2025), Lemma 6.5(i). The published
target-profile hypotheses are discharged by `heADCUniformizerTest_orders`. -/
theorem heADC2025Lemma65i_of_orders (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
      a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))
    (hnext : 2 ≤ a.order ⟨2 * k + 2, by omega⟩)
    (hTarget : ∀ i : Fin (2 * k + 2),
      b.order i = heADCMaximalOrderProfile (K := K) k ![0, 1] ⟨i.val, by omega⟩) :
    let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
      ⟨2 * k + 2, by omega, by omega, le_rfl⟩
    ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) := by
  let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
    ⟨2 * k + 2, by omega, by omega, le_rfl⟩
  have hprevB : b.order ⟨2 * k, by omega⟩ = 0 := by
    simpa [heADCMaximalOrderProfile] using hTarget ⟨2 * k, by omega⟩
  have hlastB : b.order ⟨2 * k + 1, by omega⟩ = 1 := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
      show 2 * k + 1 - 2 * k = 1 by omega] using hTarget ⟨2 * k + 1, by omega⟩
  have hheads : a.orderSequence.prefixSum (2 * k) = b.orderSequence.prefixSum (2 * k) := by
    apply BeliOrderSequence.prefixSum_eq_of_entryOrZero_eq_before
    intro j hj
    rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega),
      BeliOrderSequence.entryOrZero_of_lt _ (by omega), orderSequence_at, orderSequence_at]
    have hb := hTarget ⟨j, by omega⟩
    simp only [heADCMaximalOrderProfile, dif_pos hj] at hb
    exact (hhead ⟨j, hj⟩).trans hb.symm
  have hodd : Odd (ordUnit K (a.prefixProduct (2 * k + 2) * b.prefixProduct (2 * k + 2))) := by
    rw [ordUnit_mul,
      a.ordUnit_prefixProduct_eq_orderSequence_prefixSum _ (by omega),
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum _ le_rfl,
      BeliOrderSequence.prefixSum_add_two, BeliOrderSequence.prefixSum_add_two]
    rw [a.orderSequence.entryOrZero_of_lt (show 2 * k < 2 * k + 3 by omega),
      a.orderSequence.entryOrZero_of_lt (show 2 * k + 1 < 2 * k + 3 by omega),
      b.orderSequence.entryOrZero_of_lt (show 2 * k < 2 * k + 2 by omega),
      b.orderSequence.entryOrZero_of_lt (show 2 * k + 1 < 2 * k + 2 by omega)]
    simp only [orderSequence_at, hheads, hprevious, hprevB, hlastB]
    rcases hlast with h | h
    · rw [h]
      exact ⟨b.orderSequence.prefixSum (2 * k) - ramificationIndex K, by ring⟩
    · rw [h]
      exact ⟨b.orderSequence.prefixSum (2 * k) - ramificationIndex K + 1, by ring⟩
  exact a.heADCTerminalDefectCondition_fails b i rfl hodd
    (by simp only [i, show 2 * k + 2 - 1 = 2 * k + 1 by omega, hlastB]; omega)

/-- He (2025), Lemma 6.5(i), with every target BONG on either named
unit-uniformizer maximal class and failure at exactly the paper index n. -/
theorem heADC2025Lemma65i (k : Nat) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 2))
    (_hL : Lattice.IsIntegral q L) (hM : Lattice.IsIntegral r M)
    (hmodel :
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW1Even k (ε * uniformizerPowerUnit K 1)))
        M (heADCN1Even k (ε * uniformizerPowerUnit K 1)).lattice ∨
      Lattice.IsIsometric r (BONG.coefficientDiagonalSpace
        (heADCW2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)))
        M (heADCN2Even k (ε * uniformizerPowerUnit K 1)
          (Or.inr (heADCUnitUniformizerSharpDomain ε hε).notSquare)).lattice)
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
      a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))
    (hnext : 2 ≤ a.order ⟨2 * k + 2, by omega⟩) :
    let i : RepresentationIndex (2 * k + 3) (2 * k + 2) :=
      ⟨2 * k + 2, by omega, by omega, le_rfl⟩
    ¬ (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * k + 2) (2 * k + 2) :=
  heADC2025Lemma65i_of_orders k a b hhead hprevious hlast hnext
    (heADCUniformizerTest_orders k ε hε b hM hmodel)

end PublishedTargets

end BONG.GoodBONG

end Bong
