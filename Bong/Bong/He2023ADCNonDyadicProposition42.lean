/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCNonDyadicLemma45
import Bong.Bong.He2023ADCNonDyadicTable

/-!
# He (2025), Proposition 4.2(ii) and Lemma 4.4(i), non-dyadic case

The four determinant square classes and the two Hasse signs give a finite
classification of non-dyadic local quadratic spaces.  This file derives the
published table exhaustion and table-row uniqueness from that invariant
classification.  Neither conclusion is a field of the input structure.
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

theorem ne_other (nu : HeADC2025NonDyadicColumn) : nu ≠ other nu := by
  cases nu <;> decide

theorem eq_other_of_ne {nu mu : HeADC2025NonDyadicColumn}
    (h : mu ≠ nu) : mu = other nu := by
  cases nu <;> cases mu <;> simp_all

/-- Boolean encoding of the two Hasse-invariant columns. -/
def hasseBit : HeADC2025NonDyadicColumn → Bool
  | .one => false
  | .two => true

@[simp]
theorem hasseBit_one : hasseBit .one = false := rfl

@[simp]
theorem hasseBit_two : hasseBit .two = true := rfl

theorem hasseBit_injective : Function.Injective hasseBit := by
  intro nu mu h
  cases nu <;> cases mu <;> simp_all

end HeADC2025NonDyadicColumn

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})
  (I : S.Lemma45InvariantData)

/-- The square-class parameterization used by the non-dyadic space table. -/
structure Proposition42InvariantData where
  parameter : S.Space → HeADC2025NonDyadicSquareClass
  determinantOfParameter :
    HeADC2025NonDyadicSquareClass → I.DeterminantClass
  hilbertBit : HeADC2025NonDyadicSquareClass →
    HeADC2025NonDyadicSquareClass → Bool

variable (T : S.Proposition42InvariantData I)

/-- Lower-level invariant facts used for the non-dyadic space table.

The only low-rank exceptional input says that when the second row is
undefined, every space in that rank and determinant class has the first
column's Hasse bit.  The table exhaustion and row uniqueness are proved below.
-/
structure Proposition42Laws : Prop where
  sectionFive : S.SectionFiveLaws
  lemma45 : S.Lemma45Laws I
  spaceIsometric_refl (X : S.Space) : S.spaceIsometric X X
  spaceRepresents_of_isometric_left {X Y Z : S.Space} :
    S.spaceIsometric X Y → S.spaceRepresents Y Z →
      S.spaceRepresents X Z
  spaceRepresents_of_isometric_right {X Y Z : S.Space} :
    S.spaceIsometric Y Z → S.spaceRepresents X Z →
      S.spaceRepresents X Y
  determinantOfParameter_injective :
    Function.Injective T.determinantOfParameter
  space_determinant (X : S.Space) :
    I.determinantClass X =
      T.determinantOfParameter (T.parameter X)
  target_determinant (n : Nat) (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined n nu c →
      I.determinantClass (S.ambient (S.target nu n c)) =
        T.determinantOfParameter c
  target_hasseBit (n : Nat) (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined n nu c →
      I.hasseBit (S.ambient (S.target nu n c)) = nu.hasseBit
  undefinedSecond_hasseBit (X : S.Space) (n : Nat) :
    S.spaceRank X = n →
      ¬ HeADC2025NonDyadicRowIsDefined n .two (T.parameter X) →
      I.hasseBit X = HeADC2025NonDyadicColumn.one.hasseBit
  represents_corankTwo_of_determinant_ne {X W : S.Space} :
    S.spaceRank X = S.spaceRank W + 2 →
      I.determinantClass X ≠ I.determinantClass W →
        S.spaceRepresents X W
  target_forwardCorankTwoExpected (n : Nat)
      (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined (n + 2) nu c →
      I.forwardCorankTwoExpected
          (S.ambient (S.target nu (n + 2) c)) = nu.hasseBit
  target_forwardCorankOneExpected (n : Nat)
      (nu : HeADC2025NonDyadicColumn)
      (c' c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined (n + 1) nu c' →
      I.forwardCorankOneExpected
          (S.ambient (S.target nu (n + 1) c'))
          (T.determinantOfParameter c) =
        Bool.xor nu.hasseBit (T.hilbertBit c' c)

namespace Proposition42Laws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {I : S.Lemma45InvariantData}
  {T : S.Proposition42InvariantData I}

private theorem firstRow_defined (n : Nat)
    (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined n .one c := by
  simp [HeADC2025NonDyadicRowIsDefined]

private theorem target_spaceRank
    (H : S.Proposition42Laws I T) (n : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) :
    S.spaceRank (S.ambient (S.target nu n c)) = n :=
  (H.sectionFive.ambient_rank (S.target nu n c)).trans
    (H.sectionFive.target_rank nu n c)

/-- Proposition 4.2(i), invariant part: the two defined columns have the same
determinant class. -/
theorem target_pair_determinant_eq
    (H : S.Proposition42Laws I T) (n : Nat)
    (c : HeADC2025NonDyadicSquareClass)
    (hFirstDefined : HeADC2025NonDyadicRowIsDefined n .one c)
    (hSecondDefined : HeADC2025NonDyadicRowIsDefined n .two c) :
    I.determinantClass (S.ambient (S.target .one n c)) =
      I.determinantClass (S.ambient (S.target .two n c)) := by
  rw [H.target_determinant n .one c hFirstDefined,
    H.target_determinant n .two c hSecondDefined]

/-- Proposition 4.2(i), invariant part: the two defined columns are not
isometric. -/
theorem target_pair_nonisometric
    (H : S.Proposition42Laws I T) (n : Nat)
    (c : HeADC2025NonDyadicSquareClass)
    (hFirstDefined : HeADC2025NonDyadicRowIsDefined n .one c)
    (hSecondDefined : HeADC2025NonDyadicRowIsDefined n .two c) :
    ¬ S.spaceIsometric
      (S.ambient (S.target .one n c))
      (S.ambient (S.target .two n c)) := by
  intro hIso
  have hBit := H.lemma45.hasseBit_eq_of_isometric hIso
  rw [H.target_hasseBit n .one c hFirstDefined,
    H.target_hasseBit n .two c hSecondDefined] at hBit
  cases hBit

/-- He (2025), Lemma 4.4(i), table-row uniqueness in the non-dyadic case. -/
theorem heADC2025Lemma44iNonDyadic
    (H : S.Proposition42Laws I T) {n : Nat}
    {nu mu : HeADC2025NonDyadicColumn}
    {c d : HeADC2025NonDyadicSquareClass}
    (hNu : HeADC2025NonDyadicRowIsDefined n nu c)
    (hMu : HeADC2025NonDyadicRowIsDefined n mu d) :
    S.spaceIsometric
        (S.ambient (S.target nu n c))
        (S.ambient (S.target mu n d)) ↔
      nu = mu ∧ c = d := by
  constructor
  · intro hIso
    have hDet := H.lemma45.determinantClass_eq_of_isometric hIso
    rw [H.target_determinant n nu c hNu,
      H.target_determinant n mu d hMu] at hDet
    have hc : c = d := H.determinantOfParameter_injective hDet
    have hBit := H.lemma45.hasseBit_eq_of_isometric hIso
    rw [H.target_hasseBit n nu c hNu,
      H.target_hasseBit n mu d hMu] at hBit
    exact ⟨HeADC2025NonDyadicColumn.hasseBit_injective hBit, hc⟩
  · rintro ⟨rfl, rfl⟩
    exact H.spaceIsometric_refl _

/-- He (2025), Lemma 4.4(ii).  `hilbertBit = false` encodes Hilbert
symbol `+1`, so the Boolean xor on the right is exactly the source sign
`(-1)^(nu' + nu)`. -/
theorem heADC2025Lemma44iiNonDyadic
    (H : S.Proposition42Laws I T) (n : Nat)
    (nu' nu : HeADC2025NonDyadicColumn)
    (c' c : HeADC2025NonDyadicSquareClass)
    (hLarge : HeADC2025NonDyadicRowIsDefined (n + 1) nu' c')
    (hSmall : HeADC2025NonDyadicRowIsDefined n nu c) :
    S.spaceRepresents
        (S.ambient (S.target nu' (n + 1) c'))
        (S.ambient (S.target nu n c)) ↔
      T.hilbertBit c' c = Bool.xor nu'.hasseBit nu.hasseBit := by
  rw [H.lemma45.represents_corankOne_iff
      (X := S.ambient (S.target nu' (n + 1) c'))
      (W := S.ambient (S.target nu n c))
      (by
        have hLargeRank := H.target_spaceRank (n + 1) nu' c'
        have hSmallRank := H.target_spaceRank n nu c
        omega),
    H.target_hasseBit n nu c hSmall,
    H.target_determinant n nu c hSmall,
    H.target_forwardCorankOneExpected n nu' c' c hLarge]
  cases nu' <;> cases nu <;> cases hHilbert : T.hilbertBit c' c <;>
    simp_all [HeADC2025NonDyadicColumn.hasseBit, Bool.xor]

/-- He (2025), Lemma 4.4(iii), obtained from the codimension-two
determinant criterion and the displayed hyperbolic stabilization of each
table column. -/
theorem heADC2025Lemma44iiiNonDyadic
    (H : S.Proposition42Laws I T) (n : Nat)
    (nu' nu : HeADC2025NonDyadicColumn)
    (c' c : HeADC2025NonDyadicSquareClass)
    (hLarge : HeADC2025NonDyadicRowIsDefined (n + 2) nu' c')
    (hSmall : HeADC2025NonDyadicRowIsDefined n nu c) :
    S.spaceRepresents
        (S.ambient (S.target nu' (n + 2) c'))
        (S.ambient (S.target nu n c)) ↔
      c' ≠ c ∨ (nu' = nu ∧ c' = c) := by
  constructor
  · intro hRep
    by_cases hc : c' = c
    · subst c'
      right
      refine ⟨?_, rfl⟩
      by_contra hColumns
      have hLargeRank := H.target_spaceRank (n + 2) nu' c
      have hSmallRank := H.target_spaceRank n nu c
      have hLargeDet := H.target_determinant (n + 2) nu' c hLarge
      have hSmallDet := H.target_determinant n nu c hSmall
      have hSmallExpected :=
        (H.lemma45.represents_corankTwo_iff
          (X := S.ambient (S.target nu' (n + 2) c))
          (W := S.ambient (S.target nu n c))
          (by omega) (hLargeDet.trans hSmallDet.symm)).1 hRep
      have hBits : nu'.hasseBit = nu.hasseBit := by
        rw [← H.target_hasseBit n nu c hSmall,
          hSmallExpected,
          H.target_forwardCorankTwoExpected n nu' c hLarge]
      exact hColumns
        (HeADC2025NonDyadicColumn.hasseBit_injective hBits)
    · exact Or.inl hc
  · intro hCriterion
    rcases hCriterion with hc | ⟨hColumns, hClasses⟩
    · apply H.represents_corankTwo_of_determinant_ne
      · have hLargeRank := H.target_spaceRank (n + 2) nu' c'
        have hSmallRank := H.target_spaceRank n nu c
        omega
      · intro hDet
        have hParameters := H.determinantOfParameter_injective
          ((H.target_determinant (n + 2) nu' c' hLarge).symm.trans
            (hDet.trans (H.target_determinant n nu c hSmall)))
        exact hc hParameters
    · subst nu'
      subst c'
      apply (H.lemma45.represents_corankTwo_iff
        (X := S.ambient (S.target nu (n + 2) c))
        (W := S.ambient (S.target nu n c))
        (by
          have hLargeRank := H.target_spaceRank (n + 2) nu c
          have hSmallRank := H.target_spaceRank n nu c
          omega)
        ((H.target_determinant (n + 2) nu c hLarge).trans
          (H.target_determinant n nu c hSmall).symm)).2
      exact (H.target_hasseBit n nu c hSmall).trans
        (H.target_forwardCorankTwoExpected n nu c hLarge).symm

/-- He (2025), Proposition 4.2(ii): every non-dyadic `n`-space occurs in the
defined table. -/
theorem heADC2025Proposition42iiNonDyadic
    (H : S.Proposition42Laws I T) (X : S.Space)
    (n : Nat) (_hN : 1 ≤ n) (hRank : S.spaceRank X = n) :
    ∃ nu : HeADC2025NonDyadicColumn,
      ∃ c : HeADC2025NonDyadicSquareClass,
        HeADC2025NonDyadicRowIsDefined n nu c ∧
          S.spaceIsometric X (S.ambient (S.target nu n c)) := by
  let c := T.parameter X
  cases hBit : I.hasseBit X with
  | false =>
      have hDefined := firstRow_defined n c
      refine ⟨.one, c, hDefined, ?_⟩
      apply H.lemma45.isometric_of_rank_det_hasse
      · exact hRank.trans (H.target_spaceRank n .one c).symm
      · exact (H.space_determinant X).trans
          (H.target_determinant n .one c hDefined).symm
      · simpa [hBit] using
          (H.target_hasseBit n .one c hDefined).symm
  | true =>
      have hDefined : HeADC2025NonDyadicRowIsDefined n .two c := by
        by_contra hNot
        have hForced := H.undefinedSecond_hasseBit X n hRank hNot
        simp [HeADC2025NonDyadicColumn.hasseBit, hBit] at hForced
      refine ⟨.two, c, hDefined, ?_⟩
      apply H.lemma45.isometric_of_rank_det_hasse
      · exact hRank.trans (H.target_spaceRank n .two c).symm
      · exact (H.space_determinant X).trans
          (H.target_determinant n .two c hDefined).symm
      · simpa [hBit] using
          (H.target_hasseBit n .two c hDefined).symm

/-- He (2025), Proposition 4.2(iii): the opposite-column stabilization is
the unique `(n+2)`-space representing every `n`-space except the named one. -/
theorem heADC2025Proposition42iiiNonDyadic
    (H : S.Proposition42Laws I T) (n : Nat) (hn : 1 ≤ n)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hLarge : HeADC2025NonDyadicRowIsDefined (n + 2) nu c)
    (_hExcluded : HeADC2025NonDyadicRowIsDefined n nu.other c)
    {Y : S.Space} (hRank : S.spaceRank Y = n)
    (hNotExcluded : ¬ S.spaceIsometric Y
      (S.ambient (S.target nu.other n c))) :
    S.spaceRepresents
      (S.ambient (S.target nu (n + 2) c)) Y := by
  rcases H.heADC2025Proposition42iiNonDyadic Y n hn hRank with
    ⟨mu, d, hDefined, hIso⟩
  apply H.spaceRepresents_of_isometric_right hIso
  apply (H.heADC2025Lemma44iiiNonDyadic n nu mu c d
    hLarge hDefined).2
  by_cases hd : c ≠ d
  · exact Or.inl hd
  · have hdc : d = c := (not_ne_iff.mp hd).symm
    subst d
    right
    refine ⟨?_, rfl⟩
    by_contra hColumns
    have hOther : mu = nu.other :=
      HeADC2025NonDyadicColumn.eq_other_of_ne
        (fun h => hColumns h.symm)
    rw [hOther] at hIso
    exact hNotExcluded hIso

/-- The displayed opposite-column space does not represent the excluded
space in Proposition 4.2(iii). -/
theorem heADC2025Proposition42iiiNonDyadic_excludes
    (H : S.Proposition42Laws I T) (n : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hLarge : HeADC2025NonDyadicRowIsDefined (n + 2) nu c)
    (hExcluded : HeADC2025NonDyadicRowIsDefined n nu.other c) :
    ¬ S.spaceRepresents
      (S.ambient (S.target nu (n + 2) c))
      (S.ambient (S.target nu.other n c)) := by
  intro hRep
  rcases (H.heADC2025Lemma44iiiNonDyadic n nu nu.other c c
    hLarge hExcluded).1 hRep with hClass | ⟨hColumns, _⟩
  · exact hClass rfl
  · exact HeADC2025NonDyadicColumn.ne_other nu hColumns

/-- The uniqueness assertion in Proposition 4.2(iii): any `(n+2)`-space
which fails to represent the named `n`-space is isometric to the displayed
opposite-column space. -/
theorem heADC2025Proposition42iiiNonDyadic_unique
    (H : S.Proposition42Laws I T) (n : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (_hLarge : HeADC2025NonDyadicRowIsDefined (n + 2) nu c)
    (hExcluded : HeADC2025NonDyadicRowIsDefined n nu.other c)
    {X : S.Space} (hRank : S.spaceRank X = n + 2)
    (hNotRepresents : ¬ S.spaceRepresents X
      (S.ambient (S.target nu.other n c))) :
    S.spaceIsometric X
      (S.ambient (S.target nu (n + 2) c)) := by
  rcases H.heADC2025Proposition42iiNonDyadic X (n + 2) (by omega)
      hRank with ⟨mu, d, hDefined, hIso⟩
  have hTableDoesNotRepresent :
      ¬ S.spaceRepresents
        (S.ambient (S.target mu (n + 2) d))
        (S.ambient (S.target nu.other n c)) := by
    intro hRep
    exact hNotRepresents
      (H.spaceRepresents_of_isometric_left hIso hRep)
  have hCriterionNot :
      ¬ (d ≠ c ∨ (mu = nu.other ∧ d = c)) := by
    intro hCriterion
    exact hTableDoesNotRepresent
      ((H.heADC2025Lemma44iiiNonDyadic n mu nu.other d c
        hDefined hExcluded).2 hCriterion)
  have hd : d = c := by
    by_contra hne
    exact hCriterionNot (Or.inl hne)
  subst d
  have hmu : mu = nu := by
    by_contra hne
    have hOther : mu = nu.other :=
      HeADC2025NonDyadicColumn.eq_other_of_ne hne
    exact hCriterionNot (Or.inr ⟨hOther, rfl⟩)
  subst mu
  exact hIso

end Proposition42Laws

end HeADC2025NonDyadicSystem

end Bong
