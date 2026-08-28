/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaPrevious
import Bong.Bong.Beli2019Lemma69TypeIBetaHalfGap

/-!
# Beli (2019), Lemma 6.9(ii): odd type-I values from one predecessor

The previous-defect normal form of Lemma 2.7 removes the apparent need for
an earlier odd-boundary seed.  An odd central value follows solely from the
immediately preceding even source-alpha value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The representation invariant equals the target alpha at an odd central
type-I boundary once the immediately preceding source-alpha value is known.
Unlike `lemma69_typeI_beta_eq_of_previous`, no earlier odd value is needed. -/
theorem lemma69_typeI_beta_eq_of_previous_normal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ : RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := by
    constructor
    · exact hiTwo
    · rcases hodd with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      have hr := C.right_le_last
      have hb := D.profile.lastDifference.bound
      omega
  have hhalf := lemma69_typeI_beta_le_halfGap
    a b D C hfirst i hodd hiTwo hleft hright hweight
  have hprimary := lemma69_typeI_beta_le_primary_of_previous
    a b D C hfirst hdefect i hodd hiTwo hleft hright hweight hprevious
  have hpreviousDefect := lemma69_typeI_beta_le_previousDefect_of_previous
    a b D C hfirst i hodd hiTwo hleft hright hweight hprevious
  have hcross := lemma69_typeI_beta_previous_cross
    a b D C hfirst i hodd hiTwo hleft hright
  have hlower :
      (b.alphaValue ⟨i.val - 1, by
        have h := i.lt_large
        omega⟩ : WithTop ℚ) ≤ a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_min_primary_previous b i hi hcross]
    exact le_min hhalf (le_min hprimary hpreviousDefect)
  exact le_antisymm (a.representationAlpha_le_rightAlpha b hdefect i)
    hlower

end BONG.GoodBONG

end Bong
