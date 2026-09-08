/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionFive

/-!
# He (2025), Lemma 4.5 over the non-dyadic interface

The published proof uses the determinant class and the two-valued Hasse
invariant classification of quadratic spaces over a non-dyadic local field.
This file exposes exactly that lower-level invariant interface.  Both
directions of Lemma 4.5 are then derived; neither exactly-one conclusion is a
field of the interface.

The concrete lattice hierarchy of the repository is still dyadic.  Thus a
construction of this invariant package for a concrete non-dyadic completion
remains a separate arithmetic task.
-/

namespace Bong

universe u

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- A space represents exactly one member of an ordered pair. -/
def SpaceRepresentsExactlyOne (X A B : S.Space) : Prop :=
  (S.spaceRepresents X A ∧ ¬ S.spaceRepresents X B) ∨
    (¬ S.spaceRepresents X A ∧ S.spaceRepresents X B)

/-- A space is represented by exactly one member of an ordered pair. -/
def SpaceIsRepresentedByExactlyOne (X A B : S.Space) : Prop :=
  (S.spaceRepresents A X ∧ ¬ S.spaceRepresents B X) ∨
    (¬ S.spaceRepresents A X ∧ S.spaceRepresents B X)

/-- Invariant data occurring in the standard local classification and
codimension-one/two representation criteria. -/
structure Lemma45InvariantData where
  DeterminantClass : Type u
  determinantClass : S.Space → DeterminantClass
  hasseBit : S.Space → Bool
  forwardCorankOneExpected : S.Space → DeterminantClass → Bool
  forwardCorankTwoExpected : S.Space → Bool
  backwardCorankOneExpected : S.Space → DeterminantClass → Bool
  backwardCorankTwoExpected : S.Space → Bool

variable (I : S.Lemma45InvariantData)

/-- The lower-level local-space facts used to prove He, Lemma 4.5.

`isometric_of_rank_det_hasse` is the classification step.  The four remaining
fields are the invariant forms of the codimension-one and codimension-two
representation criteria, in the two possible directions. -/
structure Lemma45Laws : Prop where
  determinantClass_eq_of_isometric {A B : S.Space} :
    S.spaceIsometric A B →
      I.determinantClass A = I.determinantClass B
  hasseBit_eq_of_isometric {A B : S.Space} :
    S.spaceIsometric A B → I.hasseBit A = I.hasseBit B
  isometric_of_rank_det_hasse {A B : S.Space} :
    S.spaceRank A = S.spaceRank B →
      I.determinantClass A = I.determinantClass B →
      I.hasseBit A = I.hasseBit B → S.spaceIsometric A B
  represents_corankOne_iff {X W : S.Space}
      (hRank : S.spaceRank X = S.spaceRank W + 1) :
    S.spaceRepresents X W ↔
      I.hasseBit W =
        I.forwardCorankOneExpected X (I.determinantClass W)
  represents_corankTwo_iff {X W : S.Space}
      (hRank : S.spaceRank X = S.spaceRank W + 2)
      (hDet : I.determinantClass X = I.determinantClass W) :
    S.spaceRepresents X W ↔
      I.hasseBit W = I.forwardCorankTwoExpected X
  representedBy_corankOne_iff {X W : S.Space}
      (hRank : S.spaceRank W = S.spaceRank X + 1) :
    S.spaceRepresents W X ↔
      I.hasseBit W =
        I.backwardCorankOneExpected X (I.determinantClass W)
  representedBy_corankTwo_iff {X W : S.Space}
      (hRank : S.spaceRank W = S.spaceRank X + 2)
      (hDet : I.determinantClass X = I.determinantClass W) :
    S.spaceRepresents W X ↔
      I.hasseBit W = I.backwardCorankTwoExpected X

namespace Lemma45Laws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {I : S.Lemma45InvariantData}

private theorem bool_exactlyOne_eq (x y expected : Bool) (hxy : x ≠ y) :
    (x = expected ∧ y ≠ expected) ∨
      (x ≠ expected ∧ y = expected) := by
  cases x <;> cases y <;> cases expected <;> simp_all

private theorem hasseBit_ne_of_pair
    (H : S.Lemma45Laws I) {n : Nat} {W1 W2 : S.Space}
    (hW1 : S.spaceRank W1 = n) (hW2 : S.spaceRank W2 = n)
    (hDet : I.determinantClass W1 = I.determinantClass W2)
    (hNonisometric : ¬ S.spaceIsometric W1 W2) :
    I.hasseBit W1 ≠ I.hasseBit W2 := by
  intro hHasse
  exact hNonisometric
    (H.isometric_of_rank_det_hasse (hW1.trans hW2.symm) hDet hHasse)

/-- He (2025), Lemma 4.5(i), for an arbitrary pair of non-isometric
`n`-dimensional spaces with the same determinant class. -/
theorem heADC2025Lemma45iNonDyadic
    (H : S.Lemma45Laws I) (n : Nat) (_hN : 2 ≤ n)
    {W1 W2 X : S.Space}
    (hW1 : S.spaceRank W1 = n) (hW2 : S.spaceRank W2 = n)
    (hDet : I.determinantClass W1 = I.determinantClass W2)
    (hNonisometric : ¬ S.spaceIsometric W1 W2)
    (hRank : S.spaceRank X = n + 1 ∨
      (S.spaceRank X = n + 2 ∧
        I.determinantClass X = I.determinantClass W1)) :
    S.SpaceRepresentsExactlyOne X W1 W2 := by
  have hHasse := H.hasseBit_ne_of_pair hW1 hW2 hDet hNonisometric
  rcases hRank with hCorankOne | ⟨hCorankTwo, hXDet⟩
  · let expected :=
      I.forwardCorankOneExpected X (I.determinantClass W1)
    have hFirst : S.spaceRepresents X W1 ↔ I.hasseBit W1 = expected := by
      exact H.represents_corankOne_iff (by omega)
    have hSecond : S.spaceRepresents X W2 ↔ I.hasseBit W2 = expected := by
      have h := H.represents_corankOne_iff
        (X := X) (W := W2) (by omega)
      rw [← hDet] at h
      exact h
    rcases bool_exactlyOne_eq _ _ expected hHasse with hOnlyFirst | hOnlySecond
    · exact Or.inl ⟨hFirst.2 hOnlyFirst.1,
        fun h => hOnlyFirst.2 (hSecond.1 h)⟩
    · exact Or.inr ⟨(fun h => hOnlySecond.1 (hFirst.1 h)),
        hSecond.2 hOnlySecond.2⟩
  · let expected := I.forwardCorankTwoExpected X
    have hFirst : S.spaceRepresents X W1 ↔ I.hasseBit W1 = expected :=
      H.represents_corankTwo_iff (by omega) hXDet
    have hSecond : S.spaceRepresents X W2 ↔ I.hasseBit W2 = expected :=
      H.represents_corankTwo_iff (by omega) (hXDet.trans hDet)
    rcases bool_exactlyOne_eq _ _ expected hHasse with hOnlyFirst | hOnlySecond
    · exact Or.inl ⟨hFirst.2 hOnlyFirst.1,
        fun h => hOnlyFirst.2 (hSecond.1 h)⟩
    · exact Or.inr ⟨(fun h => hOnlySecond.1 (hFirst.1 h)),
        hSecond.2 hOnlySecond.2⟩

/-- He (2025), Lemma 4.5(ii), for an arbitrary pair of non-isometric
`n`-dimensional spaces with the same determinant class. -/
theorem heADC2025Lemma45iiNonDyadic
    (H : S.Lemma45Laws I) (n : Nat) (_hN : 3 ≤ n)
    {W1 W2 X : S.Space}
    (hW1 : S.spaceRank W1 = n) (hW2 : S.spaceRank W2 = n)
    (hDet : I.determinantClass W1 = I.determinantClass W2)
    (hNonisometric : ¬ S.spaceIsometric W1 W2)
    (hRank : S.spaceRank X + 1 = n ∨
      (S.spaceRank X + 2 = n ∧
        I.determinantClass X = I.determinantClass W1)) :
    S.SpaceIsRepresentedByExactlyOne X W1 W2 := by
  have hHasse := H.hasseBit_ne_of_pair hW1 hW2 hDet hNonisometric
  rcases hRank with hCorankOne | ⟨hCorankTwo, hXDet⟩
  · let expected :=
      I.backwardCorankOneExpected X (I.determinantClass W1)
    have hFirst : S.spaceRepresents W1 X ↔ I.hasseBit W1 = expected := by
      exact H.representedBy_corankOne_iff (by omega)
    have hSecond : S.spaceRepresents W2 X ↔ I.hasseBit W2 = expected := by
      have h := H.representedBy_corankOne_iff
        (X := X) (W := W2) (by omega)
      rw [← hDet] at h
      exact h
    rcases bool_exactlyOne_eq _ _ expected hHasse with hOnlyFirst | hOnlySecond
    · exact Or.inl ⟨hFirst.2 hOnlyFirst.1,
        fun h => hOnlyFirst.2 (hSecond.1 h)⟩
    · exact Or.inr ⟨(fun h => hOnlySecond.1 (hFirst.1 h)),
        hSecond.2 hOnlySecond.2⟩
  · let expected := I.backwardCorankTwoExpected X
    have hFirst : S.spaceRepresents W1 X ↔ I.hasseBit W1 = expected :=
      H.representedBy_corankTwo_iff (by omega) hXDet
    have hSecond : S.spaceRepresents W2 X ↔ I.hasseBit W2 = expected :=
      H.representedBy_corankTwo_iff (by omega) (hXDet.trans hDet)
    rcases bool_exactlyOne_eq _ _ expected hHasse with hOnlyFirst | hOnlySecond
    · exact Or.inl ⟨hFirst.2 hOnlyFirst.1,
        fun h => hOnlyFirst.2 (hSecond.1 h)⟩
    · exact Or.inr ⟨(fun h => hOnlySecond.1 (hFirst.1 h)),
        hSecond.2 hOnlySecond.2⟩

end Lemma45Laws

end HeADC2025NonDyadicSystem

end Bong
