/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCNonDyadicTheorem110

/-!
# He (2025), Lemma 4.6 over the non-dyadic interface

The repository's concrete lattice hierarchy is currently dyadic. This file
therefore derives the full non-dyadic Lemma 4.6 from explicit interfaces for
Lemma 4.5(i), Proposition 4.2(iii), and representation transport. Neither
actual-lattice conclusion of Lemma 4.6 is a field of the interface.
-/

namespace Bong

universe u

namespace HeADC2025NonDyadicColumn

/-- The opposite table column, corresponding to the paper's `3 - nu`. -/
def other : HeADC2025NonDyadicColumn → HeADC2025NonDyadicColumn
  | .one => .two
  | .two => .one

@[simp]
theorem other_one : other .one = .two := rfl

@[simp]
theorem other_two : other .two = .one := rfl

@[simp]
theorem other_other (nu : HeADC2025NonDyadicColumn) :
    other (other nu) = nu := by
  cases nu <;> rfl

end HeADC2025NonDyadicColumn

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- Actual-lattice version of representing exactly one of two targets. -/
def RepresentsExactlyOne (M A B : S.Lattice) : Prop :=
  (S.represents M A ∧ ¬ S.represents M B) ∨
    (¬ S.represents M A ∧ S.represents M B)

/-- Quadratic-space version of representing exactly one of two targets. -/
def SpaceRepresentsExactlyOne (X A B : S.Space) : Prop :=
  (S.spaceRepresents X A ∧ ¬ S.spaceRepresents X B) ∨
    (¬ S.spaceRepresents X A ∧ S.spaceRepresents X B)

/-- Explicit lower-level non-dyadic inputs used by He, Lemma 4.6.

`sameDeterminant` records equality of determinant square classes. The two
`lemma45i` fields are ambient-space statements, and `proposition42iii` is the
unique-excluding-space result. No field states an `n`-ADC lattice conclusion.
-/
structure Lemma46Laws
    (sameDeterminant : S.Space → S.Space → Prop) : Prop where
  sectionFive : S.SectionFiveLaws
  represents_ambient {M N : S.Lattice} :
    S.represents M N →
      S.spaceRepresents (S.ambient M) (S.ambient N)
  spaceRepresents_of_isometric_left {X Y Z : S.Space} :
    S.spaceIsometric X Y → S.spaceRepresents Y Z →
      S.spaceRepresents X Z
  lemma45i_corankOne (X : S.Space) (n : Nat) :
    2 ≤ n →
      ∀ (c : HeADC2025NonDyadicSquareClass),
        HeADC2025NonDyadicRowIsDefined n .one c →
        HeADC2025NonDyadicRowIsDefined n .two c →
        S.spaceRank X = n + 1 →
          S.SpaceRepresentsExactlyOne X
            (S.ambient (S.target .one n c))
            (S.ambient (S.target .two n c))
  lemma45i_corankTwo (X : S.Space) (n : Nat) :
    2 ≤ n →
      ∀ (nu : HeADC2025NonDyadicColumn)
        (c : HeADC2025NonDyadicSquareClass),
        HeADC2025NonDyadicRowIsDefined n .one c →
        HeADC2025NonDyadicRowIsDefined n .two c →
        S.spaceRank X = n + 2 →
        sameDeterminant X (S.ambient (S.target nu n c)) →
          S.SpaceRepresentsExactlyOne X
            (S.ambient (S.target .one n c))
            (S.ambient (S.target .two n c))
  proposition42iii (n : Nat) :
    2 ≤ n →
      ∀ (nu : HeADC2025NonDyadicColumn)
        (c : HeADC2025NonDyadicSquareClass),
        HeADC2025NonDyadicRowIsDefined (n + 2) nu c →
        HeADC2025NonDyadicRowIsDefined n nu.other c →
        ∀ {Y : S.Space}, S.spaceRank Y = n →
          ¬ S.spaceIsometric Y
              (S.ambient (S.target nu.other n c)) →
            S.spaceRepresents
              (S.ambient (S.target nu (n + 2) c)) Y

namespace Lemma46Laws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {sameDeterminant : S.Space → S.Space → Prop}

private theorem largeRow_defined (n : Nat) (hn : 2 ≤ n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined (n + 2) nu c := by
  simp [HeADC2025NonDyadicRowIsDefined]
  omega

/-- Lift an ambient exactly-one alternative through `n`-ADC-ness. -/
private theorem representsExactlyOne_of_ambient
    (H : S.Lemma46Laws sameDeterminant)
    {M : S.Lattice} {n : Nat}
    (hADC : S.IsNADC M n)
    (c : HeADC2025NonDyadicSquareClass)
    (hAmbient : S.SpaceRepresentsExactlyOne (S.ambient M)
      (S.ambient (S.target .one n c))
      (S.ambient (S.target .two n c))) :
    S.RepresentsExactlyOne M
      (S.target .one n c) (S.target .two n c) := by
  rcases hAmbient with ⟨hFirst, hNotSecond⟩ |
      ⟨hNotFirst, hSecond⟩
  · left
    constructor
    · exact hADC.2 (S.target .one n c)
        (H.sectionFive.target_rank .one n c)
        (H.sectionFive.target_integral .one n c) hFirst
    · intro hSecond
      exact hNotSecond (H.represents_ambient hSecond)
  · right
    constructor
    · intro hFirst
      exact hNotFirst (H.represents_ambient hFirst)
    · exact hADC.2 (S.target .two n c)
        (H.sectionFive.target_rank .two n c)
        (H.sectionFive.target_integral .two n c) hSecond

/-- He, Lemma 4.6(i), complete non-dyadic conditional endpoint. -/
theorem heADC2025Lemma46iNonDyadic
    (H : S.Lemma46Laws sameDeterminant)
    {M : S.Lattice} (n : Nat) (hn : 2 ≤ n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hFirstDefined : HeADC2025NonDyadicRowIsDefined n .one c)
    (hSecondDefined : HeADC2025NonDyadicRowIsDefined n .two c)
    (hADC : S.IsNADC M n)
    (hRank : S.rank M = n + 1 ∨
      (S.rank M = n + 2 ∧
        sameDeterminant (S.ambient M)
          (S.ambient (S.target nu n c)))) :
    S.RepresentsExactlyOne M
      (S.target .one n c) (S.target .two n c) := by
  apply H.representsExactlyOne_of_ambient hADC c
  rcases hRank with hCorankOne | ⟨hCorankTwo, hDet⟩
  · exact H.lemma45i_corankOne (S.ambient M) n hn c
      hFirstDefined hSecondDefined
      ((H.sectionFive.ambient_rank M).trans hCorankOne)
  · exact H.lemma45i_corankTwo (S.ambient M) n hn nu c
      hFirstDefined hSecondDefined
      ((H.sectionFive.ambient_rank M).trans hCorankTwo) hDet

/-- He, Lemma 4.6(ii), complete non-dyadic conditional endpoint. -/
theorem heADC2025Lemma46iiNonDyadic
    (H : S.Lemma46Laws sameDeterminant)
    {M : S.Lattice} (n : Nat) (hn : 2 ≤ n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hExcludedDefined :
      HeADC2025NonDyadicRowIsDefined n nu.other c)
    (hADC : S.IsNADC M n)
    (hSource : S.spaceIsometric (S.ambient M)
      (S.ambient (S.target nu (n + 2) c))) :
    ∀ N : S.Lattice, S.rank N = n → S.integral N →
      ¬ S.spaceIsometric (S.ambient N)
          (S.ambient (S.target nu.other n c)) →
        S.represents M N := by
  intro N hRank hIntegral hNotExceptional
  apply hADC.2 N hRank hIntegral
  apply H.spaceRepresents_of_isometric_left hSource
  exact H.proposition42iii n hn nu c
    (largeRow_defined n hn nu c) hExcludedDefined
    ((H.sectionFive.ambient_rank N).trans hRank)
    hNotExceptional

/-- The maximal-lattice sentence following He, Lemma 4.6(ii). -/
theorem heADC2025Lemma46iiNonDyadicMaximal
    (H : S.Lemma46Laws sameDeterminant)
    {M : S.Lattice} (n : Nat) (hn : 2 ≤ n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hExcludedDefined :
      HeADC2025NonDyadicRowIsDefined n nu.other c)
    (hADC : S.IsNADC M n)
    (hSource : S.spaceIsometric (S.ambient M)
      (S.ambient (S.target nu (n + 2) c)))
    (N : S.Lattice) (hRank : S.rank N = n)
    (hMaximal : S.isMaximal N)
    (hNotExceptional : ¬ S.spaceIsometric (S.ambient N)
      (S.ambient (S.target nu.other n c))) :
    S.represents M N :=
  H.heADC2025Lemma46iiNonDyadic n hn nu c hExcludedDefined hADC
    hSource N hRank (H.sectionFive.isMaximal_integral hMaximal)
    hNotExceptional

end Lemma46Laws

end HeADC2025NonDyadicSystem

end Bong
