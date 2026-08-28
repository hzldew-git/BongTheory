/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftSecondary
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 6.9(ii): type-I left source-alpha values

The three Definition 4 candidate bounds identify the representation invariant
with the source alpha.  Strong induction in steps of two then covers the whole
normalized left branch, including its first boundary with empty prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- A single even left-profile boundary equals the source alpha once the
earlier same-parity value is available. -/
theorem lemma69_typeI_left_alpha_eq_of_earlier
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val)
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hearlier : ∀ hthree : 2 < i.val,
      a.representationAlpha b
          (⟨i.val - 2, by omega, by omega, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (a.alphaValue ⟨i.val - 3, by omega⟩ : WithTop ℚ)) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  have hhalf := lemma69_typeI_left_alpha_le_halfGap
    a b D C hfirst i hiTwo hiLeft hiEven
  have hprimary := lemma69_typeI_left_alpha_le_primary
    a b D C hfirst hdefect i hiTwo hiLeft hiEven
  have hsecondary := lemma69_typeI_left_alpha_le_secondary
    a b D C hfirst hdefect i hiTwo hiLeft hiEven hi hearlier
  have hlower : (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) ≤
      a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi]
    exact le_min hhalf (le_min hprimary hsecondary)
  exact le_antisymm (a.representationAlpha_le_leftAlpha b hdefect i)
    hlower

set_option maxHeartbeats 5000000 in
-- Strong induction repeatedly transports dependent representation indices.
/-- Lemma 6.9(ii) on the complete normalized left type-I branch. -/
theorem beli2019Lemma69_ii_typeI_sourceLeftValue
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnext : C.leftSwitch + 1 < n + 2)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  have hmain : ∀ t : Nat, 1 < t → t ≤ C.leftSwitch → Even t →
      ∀ j : RepresentationIndex (n + 2) (n + 2), j.val = t →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hj := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro htTwo htLeft htEven j hj
        subst t
        have hjBound := j.lt_large
        have hinterior : 1 < j.val ∧ j.val + 1 < n + 2 := by
          exact ⟨htTwo, by omega⟩
        apply lemma69_typeI_left_alpha_eq_of_earlier
          a b D C hfirst hdefect j htTwo htLeft htEven hinterior
        intro hthree
        have hjFour : 4 ≤ j.val := by
          rcases htEven with ⟨m, hm⟩
          omega
        have hearlierEven : Even (j.val - 2) := by
          rcases htEven with ⟨m, hm⟩
          exact ⟨m - 1, by omega⟩
        let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
          ⟨j.val - 2, by omega, by omega, by omega⟩
        have hearlierLt : j.val - 2 < j.val := by omega
        have hearlierTwo : 1 < j.val - 2 := by omega
        have hearlierLeft : j.val - 2 ≤ C.leftSwitch := by omega
        have hearlier := ih (j.val - 2) hearlierLt hearlierTwo
          hearlierLeft hearlierEven earlierIdx rfl
        simpa only [earlierIdx,
          show j.val - 2 - 1 = j.val - 3 by omega] using hearlier
  exact hmain i.val hiTwo hiLeft hiEven i rfl

/-- The value immediately before the central type-I interval, stated in the
form needed to start its odd-boundary induction. -/
theorem beli2019Lemma69_ii_typeI_leftSwitchValue
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hnext : C.leftSwitch + 1 < n + 2)
    (hdefect : a.RepresentationDefectCondition b) :
    a.representationAlpha b
        (⟨C.leftSwitch, hleftPos, by omega, by omega⟩ :
          RepresentationIndex (n + 2) (n + 2)) =
      (a.alphaValue ⟨C.leftSwitch - 1, by omega⟩ : WithTop ℚ) := by
  apply beli2019Lemma69_ii_typeI_sourceLeftValue
    a b D C hfirst hnext hdefect
  · change 1 < C.leftSwitch
    rcases C.left_even with ⟨m, hm⟩
    omega
  · exact le_rfl
  · exact C.left_even

end BONG.GoodBONG

end Bong
