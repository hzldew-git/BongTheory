/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightProfileAlpha
import Bong.Bong.Beli2019Lemma79DefectOne

/-!
# Beli (2019), Lemma 7.9(ii): the first case-7 beta subbranch

When the target order immediately before the current coordinate does not
exceed the comparison order, the case-7 target-alpha recursion bounds the
representation invariant by the required target alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The beta bound in the non-strict order subcase of Lemma 7.9(ii),
case 7. -/
theorem lemma79_rightProfile_beta_bound_of_target_le_comparison
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : O.transition.firstTwo ≤ i.val)
    (hlast : i.val < O.last)
    (hodd : Odd (i.val - (O.transition.firstTwo - 1)))
    (hcurrent : b.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ ≤ c.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiPreviousAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hfarBound : i.val + 1 < n + 2 := by
    have hb := O.lastDifference.bound
    omega
  have hprofile := lemma79_rightProfile_target_twoStep_and_alpha
    a b O i hright hlast hodd
  have hprimary := b.representationAlphaValue_le_primary_nextAlpha
    c i hfarBound
  have hcurrentQ :
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) ≤
      ((b.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) := by
    exact_mod_cast (show b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, hiPrevious⟩ ≤
        b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, hiPrevious⟩ by omega)
  have hbound : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, hiPreviousAlpha⟩ := by
    linarith [hprimary, hcurrentQ, hprofile.2]
  exact WithTop.coe_le_coe.mpr hbound

end BONG.GoodBONG

end Bong
