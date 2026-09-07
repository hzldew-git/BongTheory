/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCSectionFive

/-!
# He (2025), Theorem 1.10 over non-dyadic local fields

This file completes the finite-catalogue and counting argument in the
non-dyadic branch of Theorem 1.10.  It uses the four square classes and two
maximal-lattice columns of the published table.  In rank two the undefined
row `N_2^2(1)` is removed, giving seven rows; in every rank at least three all
eight rows occur.

The theorem is stated over `HeADC2025NonDyadicSystem`.  Consequently the
concrete local-field content of Proposition 4.2, Remark 4.3, Lemmas 4.7--4.8,
and Proposition 4.15 is isolated in `CatalogueLaws`.  No classification or
cardinality conclusion is included as a field of that structure.
-/

namespace Bong

universe u v

/-- The rank-two table: all four first-column rows and the three defined
second-column rows. -/
abbrev HeADC2025NonDyadicBinaryIndex :=
  HeADC2025NonDyadicSquareClass ⊕
    {c : HeADC2025NonDyadicSquareClass // c ≠ .one}

/-- The eight rows occurring in every non-dyadic rank at least three. -/
abbrev HeADC2025NonDyadicGeneralIndex :=
  HeADC2025NonDyadicColumn × HeADC2025NonDyadicSquareClass

/-- The only excluded row for ranks covered by Theorem 1.10 is
`N_2^2(1)`. -/
def HeADC2025NonDyadicRowIsDefined (m : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass) : Prop :=
  m ≠ 2 ∨ nu ≠ .two ∨ c ≠ .one

/-- The table coordinates represented by a binary index. -/
def heADC2025NonDyadicBinaryRow
    (i : HeADC2025NonDyadicBinaryIndex) :
    HeADC2025NonDyadicColumn × HeADC2025NonDyadicSquareClass :=
  match i with
  | .inl c => (.one, c)
  | .inr c => (.two, c)

theorem heADC2025NonDyadicBinaryRow_defined
    (i : HeADC2025NonDyadicBinaryIndex) :
    HeADC2025NonDyadicRowIsDefined 2
      (heADC2025NonDyadicBinaryRow i).1
      (heADC2025NonDyadicBinaryRow i).2 := by
  rcases i with c | c
  · simp [HeADC2025NonDyadicRowIsDefined,
      heADC2025NonDyadicBinaryRow]
  · simpa [HeADC2025NonDyadicRowIsDefined,
      heADC2025NonDyadicBinaryRow] using c.property

theorem heADC2025NonDyadicBinaryRow_injective :
    Function.Injective heADC2025NonDyadicBinaryRow := by
  intro i j hij
  rcases i with ci | ci
  · rcases j with cj | cj
    · have hc : ci = cj := by
        simpa [heADC2025NonDyadicBinaryRow] using congrArg Prod.snd hij
      exact congrArg Sum.inl hc
    · have hcolumn : HeADC2025NonDyadicColumn.one = .two := by
        simpa [heADC2025NonDyadicBinaryRow] using congrArg Prod.fst hij
      cases hcolumn
  · rcases j with cj | cj
    · have hcolumn : HeADC2025NonDyadicColumn.two = .one := by
        simpa [heADC2025NonDyadicBinaryRow] using congrArg Prod.fst hij
      cases hcolumn
    · have hc : ci.val = cj.val := by
        simpa [heADC2025NonDyadicBinaryRow] using congrArg Prod.snd hij
      exact congrArg Sum.inr (Subtype.ext hc)

/-- The binary table has exactly seven defined rows. -/
theorem card_heADC2025NonDyadicBinaryIndex :
    Fintype.card HeADC2025NonDyadicBinaryIndex = 7 := by
  decide

/-- Every general non-dyadic table has exactly eight rows. -/
theorem card_heADC2025NonDyadicGeneralIndex :
    Fintype.card HeADC2025NonDyadicGeneralIndex = 8 := by
  decide

namespace HeADC2025NonDyadicSystem

variable (S : HeADC2025NonDyadicSystem.{u})

/-- Exactness of a finite `n`-ADC catalogue with respect to integral
isometry. -/
structure IsExactNADCIsometryCatalogue
    (isometric : S.Lattice → S.Lattice → Prop)
    {J : Type v} (n m : Nat) (family : J → S.Lattice) : Prop where
  rank (j : J) : S.rank (family j) = m
  nADC (j : J) : S.IsNADC (family j) n
  complete (M : S.Lattice) :
    S.rank M = m → S.IsNADC M n →
      ∃ j : J, isometric M (family j)
  irredundant {i j : J} : isometric (family i) (family j) → i = j

/-- Concrete non-dyadic classification inputs used to turn Section 5 into
an exact isometry catalogue.  These are precisely the maximal-row facts of
Proposition 4.2, Remark 4.3, Lemmas 4.7--4.8, and the equal-rank implication
of Proposition 4.15. -/
structure CatalogueLaws
    (isometric : S.Lattice → S.Lattice → Prop) : Prop where
  sectionFive : S.SectionFiveLaws
  target_isMaximal (m : Nat) (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined m nu c →
      S.isMaximal (S.target nu m c)
  maximal_complete (M : S.Lattice) (m : Nat) :
    S.rank M = m → S.isMaximal M →
      ∃ nu : HeADC2025NonDyadicColumn,
        ∃ c : HeADC2025NonDyadicSquareClass,
          HeADC2025NonDyadicRowIsDefined m nu c ∧
            isometric M (S.target nu m c)
  target_irredundant (m : Nat)
      {nu mu : HeADC2025NonDyadicColumn}
      {c d : HeADC2025NonDyadicSquareClass} :
    HeADC2025NonDyadicRowIsDefined m nu c →
      HeADC2025NonDyadicRowIsDefined m mu d →
      isometric (S.target nu m c) (S.target mu m d) →
        nu = mu ∧ c = d
  equalRank_isMaximal (M : S.Lattice) (n : Nat) :
    S.rank M = n → S.IsNADC M n → S.isMaximal M

/-- The rank-two family with the undefined row removed. -/
def nonDyadicBinaryFamily (i : HeADC2025NonDyadicBinaryIndex) : S.Lattice :=
  S.target (heADC2025NonDyadicBinaryRow i).1 2
    (heADC2025NonDyadicBinaryRow i).2

/-- The eight-row family used in every rank at least three. -/
def nonDyadicGeneralFamily (m : Nat)
    (i : HeADC2025NonDyadicGeneralIndex) : S.Lattice :=
  S.target i.1 m i.2

namespace CatalogueLaws

variable {S : HeADC2025NonDyadicSystem.{u}}
  {isometric : S.Lattice → S.Lattice → Prop}

private theorem generalRow_defined (m : Nat) (hm : 3 ≤ m)
    (i : HeADC2025NonDyadicGeneralIndex) :
    HeADC2025NonDyadicRowIsDefined m i.1 i.2 := by
  exact Or.inl (by omega)

/-- A maximality implication supplies an exact eight-row catalogue in every
rank at least three. -/
theorem general_exactCatalogue_of_isMaximal
    (H : S.CatalogueLaws isometric) (n m : Nat) (hm : 3 ≤ m)
    (hMaximal : ∀ M : S.Lattice,
      S.rank M = m → S.IsNADC M n → S.isMaximal M) :
    S.IsExactNADCIsometryCatalogue isometric n m
      (S.nonDyadicGeneralFamily m) where
  rank i := H.sectionFive.target_rank i.1 m i.2
  nADC i := H.sectionFive.isMaximal_isNADC
    (H.target_isMaximal m i.1 i.2 (generalRow_defined m hm i)) n
  complete M hRank hADC := by
    obtain ⟨nu, c, hDefined, hIso⟩ :=
      H.maximal_complete M m hRank (hMaximal M hRank hADC)
    exact ⟨(nu, c), hIso⟩
  irredundant {i j} hIso := by
    obtain ⟨hnu, hc⟩ := H.target_irredundant m
      (generalRow_defined m hm i) (generalRow_defined m hm j) hIso
    exact Prod.ext hnu hc

/-- The equal-rank binary branch is the exact seven-row catalogue. -/
theorem binary_exactCatalogue (H : S.CatalogueLaws isometric) :
    S.IsExactNADCIsometryCatalogue isometric 2 2
      S.nonDyadicBinaryFamily where
  rank i := H.sectionFive.target_rank
    (heADC2025NonDyadicBinaryRow i).1 2
    (heADC2025NonDyadicBinaryRow i).2
  nADC i := H.sectionFive.isMaximal_isNADC
    (H.target_isMaximal 2
      (heADC2025NonDyadicBinaryRow i).1
      (heADC2025NonDyadicBinaryRow i).2
      (heADC2025NonDyadicBinaryRow_defined i)) 2
  complete M hRank hADC := by
    obtain ⟨nu, c, hDefined, hIso⟩ := H.maximal_complete M 2 hRank
      (H.equalRank_isMaximal M 2 hRank hADC)
    by_cases hnu : nu = .one
    · subst hnu
      exact ⟨Sum.inl c, hIso⟩
    · have hnuTwo : nu = .two := by
        cases nu <;> simp_all
      subst hnuTwo
      have hc : c ≠ .one := by
        simpa [HeADC2025NonDyadicRowIsDefined] using hDefined
      exact ⟨Sum.inr ⟨c, hc⟩, hIso⟩
  irredundant {i j} hIso := by
    apply heADC2025NonDyadicBinaryRow_injective
    obtain ⟨hnu, hc⟩ := H.target_irredundant 2
      (heADC2025NonDyadicBinaryRow_defined i)
      (heADC2025NonDyadicBinaryRow_defined j) hIso
    exact Prod.ext hnu hc

/-- The complete non-dyadic branch of Theorem 1.10.  Since the ramification
index is zero, the printed formulas reduce to seven classes in binary rank
and eight classes in every rank at least three. -/
structure Theorem110NonDyadicConclusion
    (isometric : S.Lattice → S.Lattice → Prop) : Prop where
  binary :
    S.IsExactNADCIsometryCatalogue isometric 2 2
        S.nonDyadicBinaryFamily ∧
      Fintype.card HeADC2025NonDyadicBinaryIndex = 7
  equalRank (m : Nat) (hm : 3 ≤ m) :
    S.IsExactNADCIsometryCatalogue isometric m m
        (S.nonDyadicGeneralFamily m) ∧
      Fintype.card HeADC2025NonDyadicGeneralIndex = 8
  corankOne (n : Nat) (hn : 2 ≤ n) :
    S.IsExactNADCIsometryCatalogue isometric n (n + 1)
        (S.nonDyadicGeneralFamily (n + 1)) ∧
      Fintype.card HeADC2025NonDyadicGeneralIndex = 8
  corankTwo (n : Nat) (hn : 2 ≤ n) :
    S.IsExactNADCIsometryCatalogue isometric n (n + 2)
        (S.nonDyadicGeneralFamily (n + 2)) ∧
      Fintype.card HeADC2025NonDyadicGeneralIndex = 8
  binaryPublishedFormula (residueNorm : Nat) :
    Fintype.card HeADC2025NonDyadicBinaryIndex =
      8 * residueNorm ^ 0 - 1
  generalPublishedFormula (residueNorm : Nat) :
    Fintype.card HeADC2025NonDyadicGeneralIndex =
      8 * residueNorm ^ 0

/-- Theorem 1.10 over a non-dyadic local field, relative only to the explicit
catalogue-law boundary above. -/
theorem heADC2025Theorem110NonDyadic
    (H : S.CatalogueLaws isometric) :
    Theorem110NonDyadicConclusion (S := S) isometric where
  binary := ⟨H.binary_exactCatalogue,
    card_heADC2025NonDyadicBinaryIndex⟩
  equalRank m hm :=
    ⟨H.general_exactCatalogue_of_isMaximal m m hm
      (fun M hRank hADC => H.equalRank_isMaximal M m hRank hADC),
      card_heADC2025NonDyadicGeneralIndex⟩
  corankOne n hn :=
    ⟨H.general_exactCatalogue_of_isMaximal n (n + 1) (by omega)
      (fun M hRank hADC =>
        (H.sectionFive.heADC2025Theorem51 M n hn (Or.inl hRank)).mp hADC),
      card_heADC2025NonDyadicGeneralIndex⟩
  corankTwo n hn :=
    ⟨H.general_exactCatalogue_of_isMaximal n (n + 2) (by omega)
      (fun M hRank hADC =>
        (H.sectionFive.heADC2025Theorem51 M n hn (Or.inr hRank)).mp hADC),
      card_heADC2025NonDyadicGeneralIndex⟩
  binaryPublishedFormula residueNorm := by
    rw [card_heADC2025NonDyadicBinaryIndex]
    simp
  generalPublishedFormula residueNorm := by
    rw [card_heADC2025NonDyadicGeneralIndex]
    simp

end CatalogueLaws

end HeADC2025NonDyadicSystem

end Bong
