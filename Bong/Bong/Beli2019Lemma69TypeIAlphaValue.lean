/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaSecondary

/-!
# Beli (2019), Lemma 6.9(ii): noninitial type-I source-alpha values

The three candidate bounds identify the invariant at an interior even
boundary.  At a terminal even boundary Definition 5 has no secondary
candidate, so the half-gap and primary bounds suffice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At an interior noninitial even boundary, the representation invariant
equals the source alpha once the two preceding induction values are known. -/
theorem lemma69_typeI_alpha_eq_of_previous
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (heven : Even i.val) (hiThree : 2 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 2)
    (hright : i.val - 1 < C.rightSwitch)
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hweightPrevious : a.alphaLeftEndpoint ⟨i.val - 2, by omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 2, by omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 2, by omega⟩ : WithTop ℚ))
    (hearlier : a.representationAlpha b
        (⟨i.val - 2, by omega, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨i.val - 3, by omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  have hhalf := lemma69_typeI_alpha_le_halfGap
    a b D C hfirst i heven (by omega) (by omega) hright
  have hprimary := lemma69_typeI_alpha_le_primary_of_previousBeta
    a b D C hfirst hdefect i heven (by omega) (by omega) hright
      hweightPrevious hprevious
  have hsecondary := lemma69_typeI_alpha_le_secondary_of_earlier
    a b D C hfirst hdefect i heven (by omega) hleft hright hi
      (fun _ => hearlier)
  have hlower :
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) ≤
        a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi]
    exact le_min hhalf (le_min hprimary hsecondary)
  exact le_antisymm (a.representationAlpha_le_leftAlpha b hdefect i)
    hlower

/-- At a terminal noninitial even boundary, the absent secondary candidate
can be omitted from the same source-alpha argument. -/
theorem lemma69_typeI_alpha_eq_of_previous_terminal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (heven : Even i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch < i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hiNot : ¬(1 < i.val ∧ i.val + 1 < n + 2))
    (hweightPrevious : a.alphaLeftEndpoint ⟨i.val - 2, by
        have h := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 2, by
        have h := i.lt_large
        omega⟩)
    (hprevious : a.representationAlpha b
        (⟨i.val - 1, by omega, by
          have h := i.lt_large
          omega, by
          have h := i.lt_large
          omega⟩ : RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 2, by
        have h := i.lt_large
        omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have h := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hhalf := lemma69_typeI_alpha_le_halfGap
    a b D C hfirst i heven hiTwo hleft hright
  have hprimary := lemma69_typeI_alpha_le_primary_of_previousBeta
    a b D C hfirst hdefect i heven hiTwo hleft hright
      hweightPrevious hprevious
  have hlower :
      (a.alphaValue ⟨i.val - 1, by
        have h := i.lt_large
        omega⟩ : WithTop ℚ) ≤ a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_primary_of_not_interior b i hiNot]
    exact le_min hhalf hprimary
  exact le_antisymm (a.representationAlpha_le_leftAlpha b hdefect i)
    hlower

end BONG.GoodBONG

end Bong
