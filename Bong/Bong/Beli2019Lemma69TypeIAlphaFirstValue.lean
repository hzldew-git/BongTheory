/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaValue
import Bong.Bong.Beli2019Lemma69TypeILeftZeroOdd

/-!
# Beli (2019), Lemma 6.9(ii): the first central even value

The strengthened secondary-candidate lemma treats `i = 2` by evaluating its
empty diagonal prefix.  Consequently the usual even value proof extends to
the first central even boundary without assuming a nonexistent earlier
representation index.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- An interior even central value follows from the preceding target-beta
value; an earlier even value is requested only when `2 < i`. -/
theorem lemma69_typeI_alpha_eq_of_previous_or_first
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (heven : Even i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 2)
    (hright : i.val - 1 < C.rightSwitch)
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hweightPrevious : a.alphaLeftEndpoint ⟨i.val - 2, by omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 2, by omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ))
    (hearlier : ∀ hthree : 2 < i.val,
      a.representationAlpha b
          (⟨i.val - 2, by omega, by omega, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (a.alphaValue ⟨i.val - 3, by omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  have hhalf := lemma69_typeI_alpha_le_halfGap
    a b D C hfirst i heven hiTwo (by omega) hright
  have hprimary := lemma69_typeI_alpha_le_primary_of_previousBeta
    a b D C hfirst hdefect i heven hiTwo (by omega) hright
      hweightPrevious hprevious
  have hsecondary := lemma69_typeI_alpha_le_secondary_of_earlier
    a b D C hfirst hdefect i heven hiTwo hleft hright hi hearlier
  have hlower :
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) ≤
        a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi]
    exact le_min hhalf (le_min hprimary hsecondary)
  exact le_antisymm (a.representationAlpha_le_leftAlpha b hdefect i)
    hlower

end BONG.GoodBONG

end Bong
