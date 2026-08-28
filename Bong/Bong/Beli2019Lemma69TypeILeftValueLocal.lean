/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftValue

/-!
# Beli (2019), Lemma 6.9(ii): a local type-I left value theorem

The original assembled theorem assumed that the coordinate after the
canonical switch exists.  Its induction only needs the coordinate after
the boundary currently under consideration.  This local form removes the
unnecessary global endpoint hypothesis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At a terminal type-I left boundary the absent secondary candidate can
be omitted; the half-gap and primary candidates still identify the value. -/
theorem lemma69_typeI_left_alpha_eq_terminal
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val)
    (hiNot : ¬(1 < i.val ∧ i.val + 1 < n + 2)) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  have hhalf := lemma69_typeI_left_alpha_le_halfGap
    a b D C hfirst i hiTwo hiLeft hiEven
  have hprimary := lemma69_typeI_left_alpha_le_primary
    a b D C hfirst hdefect i hiTwo hiLeft hiEven
  have hlower : (a.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationAlpha b i := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i,
      a.representationAlphaPrime_eq_primary_of_not_interior b i hiNot]
    exact le_min hhalf hprimary
  exact le_antisymm (a.representationAlpha_le_leftAlpha b hdefect i)
    hlower

set_option maxHeartbeats 5000000 in
-- Strong induction transports dependent representation indices.
/-- Lemma 6.9(ii) at one type-I left boundary, assuming only that its
immediate successor lies in the BONG. -/
theorem beli2019Lemma69_ii_typeI_sourceLeftValue_of_next
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) (hiNext : i.val + 1 < n + 2) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  have hmain : ∀ t : Nat, 1 < t → t ≤ i.val →
      t ≤ C.leftSwitch → Even t →
      ∀ j : RepresentationIndex (n + 2) (n + 2), j.val = t →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hj := j.lt_large
            omega⟩ : WithTop ℚ) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro htTwo htCurrent htLeft htEven j hj
        subst t
        have hjBound := j.lt_large
        have hinterior : 1 < j.val ∧ j.val + 1 < n + 2 := by
          constructor
          · exact htTwo
          · omega
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
        have hearlierCurrent : j.val - 2 ≤ i.val := by omega
        have hearlierLeft : j.val - 2 ≤ C.leftSwitch := by omega
        have hearlier := ih (j.val - 2) hearlierLt hearlierTwo
          hearlierCurrent hearlierLeft hearlierEven earlierIdx rfl
        simpa only [earlierIdx,
          show j.val - 2 - 1 = j.val - 3 by omega] using hearlier
  exact hmain i.val hiTwo le_rfl hiLeft hiEven i rfl

/-- Lemma 6.9(ii) on the complete type-I left branch, including a possible
terminal switch coordinate. -/
theorem beli2019Lemma69_ii_typeI_sourceLeftValue_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) :
    a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ) := by
  by_cases hiNext : i.val + 1 < n + 2
  · exact beli2019Lemma69_ii_typeI_sourceLeftValue_of_next
      a b D C hfirst hdefect i hiTwo hiLeft hiEven hiNext
  · exact lemma69_typeI_left_alpha_eq_terminal
      a b D C hfirst hdefect i hiTwo hiLeft hiEven (by
        intro hi
        exact hiNext hi.2)

end BONG.GoodBONG

end Bong
