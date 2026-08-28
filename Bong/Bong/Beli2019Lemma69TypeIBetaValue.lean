/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaHalfGap
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 6.9(ii): noninitial type-I beta value

At a noninitial odd boundary, the preceding source-alpha and target-beta
equalities bound the primary and secondary candidates.  Together with the
half-gap bound, this identifies the full representation invariant.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The representation invariant equals the target alpha at every
noninitial odd boundary whose two preceding induction values are known. -/
theorem lemma69_typeI_beta_eq_of_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiThree : 2 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 2)
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
          omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨i.val - 2, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ))
    (hearlier : a.representationAlpha b
        (⟨i.val - 2, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 3, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := by
    constructor
    · omega
    · rcases hodd with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      have hr := C.right_le_last
      have hb := D.profile.lastDifference.bound
      omega
  have hhalf := lemma69_typeI_beta_le_halfGap
    a b D C hfirst i hodd (by omega) (by omega) hright hweight
  have hprimary := lemma69_typeI_beta_le_primary_of_previous
    a b D C hfirst hdefect i hodd (by omega) (by omega) hright
      hweight hprevious
  have hsecondary := lemma69_typeI_beta_le_secondary_of_earlier
    a b D C hfirst hdefect i hodd hiThree hleft hright hweight hearlier
  have hlower :
      (b.alphaValue ⟨i.val - 1, by
        have h := i.lt_large
        omega⟩ : WithTop ℚ) ≤ a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi]
    exact le_min hhalf (le_min hprimary hsecondary)
  exact le_antisymm (a.representationAlpha_le_rightAlpha b hdefect i)
    hlower

end BONG.GoodBONG

end Bong
