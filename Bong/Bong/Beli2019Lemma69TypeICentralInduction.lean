/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaValue

/-!
# Beli (2019), Lemma 6.9(ii): alternating type-I induction

The middle type-I interval alternates between target-beta values at odd
boundaries and source-alpha values at even boundaries.  Once its first two
values are known, the candidate lemmas propagate the pattern by strong
induction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- Strong induction repeatedly transports dependent representation indices.
/-- The two seed values propagate through the entire canonical type-I
interval. -/
theorem lemma69_typeI_central_values_of_seeds
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hweight : ∀ p : Fin (n + 1),
      C.leftSwitch ≤ p.val → p.val < C.rightSwitch →
        a.alphaLeftEndpoint p = b.alphaLeftEndpoint p)
    (hseedOdd : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 1 →
        a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hp := j.pos
            have hl := j.lt_large
            omega⟩ : WithTop ℚ))
    (hseedEven : ∀ j : RepresentationIndex (n + 2) (n + 2),
      j.val = C.leftSwitch + 2 →
        a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hp := j.pos
            have hl := j.lt_large
            omega⟩ : WithTop ℚ))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    (Odd i.val → a.representationAlpha b i =
      (b.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) ∧
    (Even i.val → a.representationAlpha b i =
      (a.alphaValue ⟨i.val - 1, by
        have hp := i.pos
        have hl := i.lt_large
        omega⟩ : WithTop ℚ)) := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hmain : ∀ k : Nat,
      C.leftSwitch + 1 ≤ k → k ≤ C.rightSwitch →
      ∀ j : RepresentationIndex (n + 2) (n + 2), j.val = k →
        (Odd j.val → a.representationAlpha b j =
          (b.alphaValue ⟨j.val - 1, by
            have hp := j.pos
            have hl := j.lt_large
            omega⟩ : WithTop ℚ)) ∧
        (Even j.val → a.representationAlpha b j =
          (a.alphaValue ⟨j.val - 1, by
            have hp := j.pos
            have hl := j.lt_large
            omega⟩ : WithTop ℚ)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hkLeft hkRight j hj
        subst k
        constructor
        · intro hjOdd
          by_cases hkFirst : j.val = C.leftSwitch + 1
          · apply hseedOdd j
            omega
          by_cases hkSecond : j.val = C.leftSwitch + 2
          · rcases hjOdd with ⟨d, hd⟩
            rcases C.left_even with ⟨e, he⟩
            omega
          have hkLater : C.leftSwitch + 2 < j.val := by omega
          let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
            ⟨j.val - 1, by omega, by omega, by omega⟩
          let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
            ⟨j.val - 2, by omega, by omega, by omega⟩
          rcases hjOdd with ⟨d, hd⟩
          have hpreviousEven : Even previousIdx.val :=
            ⟨d, by simp only [previousIdx]; omega⟩
          have hearlierOdd : Odd earlierIdx.val :=
            ⟨d - 1, by simp only [earlierIdx]; omega⟩
          have hpreviousIH :=
            (ih (j.val - 1) (by omega) (by omega) (by omega)
              previousIdx rfl).2 hpreviousEven
          have hearlierIH :=
            (ih (j.val - 2) (by omega) (by omega) (by omega)
              earlierIdx rfl).1 hearlierOdd
          have hprevious : a.representationAlpha b
              (⟨j.val - 1, by omega, by omega, by omega⟩ :
                RepresentationIndex (n + 2) (n + 2)) =
            (a.alphaValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) := by
            simpa only [previousIdx,
              show j.val - 1 - 1 = j.val - 2 by omega] using hpreviousIH
          have hearlier : a.representationAlpha b
              (⟨j.val - 2, by omega, by omega, by omega⟩ :
                RepresentationIndex (n + 2) (n + 2)) =
            (b.alphaValue ⟨j.val - 3, by omega⟩ : WithTop ℚ) := by
            simpa only [earlierIdx,
              show j.val - 2 - 1 = j.val - 3 by omega] using hearlierIH
          let currentAlpha : Fin (n + 1) :=
            ⟨j.val - 1, by have hl := j.lt_large; omega⟩
          have hweightCurrent := hweight currentAlpha (by
            simp only [currentAlpha]
            omega) (by
              simp only [currentAlpha]
              omega)
          exact lemma69_typeI_beta_eq_of_previous
            a b D C hfirst hdefect j ⟨d, hd⟩ (by omega) (by omega)
              (by omega) hweightCurrent hprevious hearlier
        · intro hjEven
          by_cases hkFirst : j.val = C.leftSwitch + 1
          · rcases hjEven with ⟨d, hd⟩
            rcases C.left_even with ⟨e, he⟩
            omega
          by_cases hkSecond : j.val = C.leftSwitch + 2
          · apply hseedEven j
            omega
          have hkLater : C.leftSwitch + 2 < j.val := by omega
          let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
            ⟨j.val - 1, by omega, by omega, by omega⟩
          let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
            ⟨j.val - 2, by omega, by omega, by omega⟩
          rcases hjEven with ⟨d, hd⟩
          have hpreviousOdd : Odd previousIdx.val :=
            ⟨d - 1, by simp only [previousIdx]; omega⟩
          have hearlierEven : Even earlierIdx.val :=
            ⟨d - 1, by simp only [earlierIdx]; omega⟩
          have hpreviousIH :=
            (ih (j.val - 1) (by omega) (by omega) (by omega)
              previousIdx rfl).1 hpreviousOdd
          have hearlierIH :=
            (ih (j.val - 2) (by omega) (by omega) (by omega)
              earlierIdx rfl).2 hearlierEven
          have hprevious : a.representationAlpha b
              (⟨j.val - 1, by omega, by omega, by omega⟩ :
                RepresentationIndex (n + 2) (n + 2)) =
            (b.alphaValue ⟨j.val - 2, by omega⟩ : WithTop ℚ) := by
            simpa only [previousIdx,
              show j.val - 1 - 1 = j.val - 2 by omega] using hpreviousIH
          have hearlier : a.representationAlpha b
              (⟨j.val - 2, by omega, by omega, by omega⟩ :
                RepresentationIndex (n + 2) (n + 2)) =
            (a.alphaValue ⟨j.val - 3, by omega⟩ : WithTop ℚ) := by
            simpa only [earlierIdx,
              show j.val - 2 - 1 = j.val - 3 by omega] using hearlierIH
          let previousAlpha : Fin (n + 1) :=
            ⟨j.val - 2, by have hl := j.lt_large; omega⟩
          have hweightPrevious := hweight previousAlpha (by
            simp only [previousAlpha]
            omega) (by
              simp only [previousAlpha]
              omega)
          by_cases hnext : j.val + 1 < n + 2
          · exact lemma69_typeI_alpha_eq_of_previous
              a b D C hfirst hdefect j ⟨d, hd⟩ (by omega) (by omega)
                (by omega) ⟨by omega, hnext⟩ hweightPrevious hprevious
                  hearlier
          · apply lemma69_typeI_alpha_eq_of_previous_terminal
              a b D C hfirst hdefect j ⟨d, hd⟩ (by omega) (by omega)
                (by omega) (by omega) hweightPrevious hprevious
  have hiMainLeft : C.leftSwitch + 1 ≤ i.val := by
    have hp := i.pos
    omega
  have hiMainRight : i.val ≤ C.rightSwitch := by
    have hp := i.pos
    omega
  exact hmain i.val hiMainLeft hiMainRight i rfl

end BONG.GoodBONG

end Bong
