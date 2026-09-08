/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCNonDyadicProposition42

/-!
# He (2025), Theorem 1.10 over non-dyadic local fields

This file completes the finite-catalogue and counting argument in the
non-dyadic branch of Theorem 1.10.  It uses the four square classes and two
maximal-lattice columns of the published table.  In rank two the undefined
row `N_2^2(1)` is removed, giving seven rows; in every rank at least three all
eight rows occur.

The theorem is stated over `HeADC2025NonDyadicSystem`.  Consequently the
concrete local-field content of Proposition 4.2, Remark 4.3, and Lemmas
4.7--4.8 is isolated in `CatalogueLaws`.  The equal-rank implication of
Proposition 4.15 is proved below from the maximal-lattice existence and
same-rank transfer facts used in the published proof.  No classification,
Proposition 4.15, or cardinality conclusion is included as a field of the
structure.
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

/-- Remaining non-dyadic inputs used to turn the proved invariant-space
classification into an exact lattice-isometry catalogue.  Proposition 4.2
and Lemma 4.4 are carried by `proposition42`; maximal-row exhaustion and row
irredundancy are derived below rather than stored as fields. -/
structure CatalogueLaws
    (I : S.Lemma45InvariantData)
    (P : S.Proposition42InvariantData I)
    (isometric : S.Lattice → S.Lattice → Prop) : Prop where
  proposition42 : S.Proposition42Laws I P
  target_isMaximal (m : Nat) (nu : HeADC2025NonDyadicColumn)
      (c : HeADC2025NonDyadicSquareClass) :
    HeADC2025NonDyadicRowIsDefined m nu c →
      S.isMaximal (S.target nu m c)
  isometric_ambient {M N : S.Lattice} :
    isometric M N →
      S.spaceIsometric (S.ambient M) (S.ambient N)
  maximal_isometric_of_ambient {M N : S.Lattice} :
    S.isMaximal M → S.isMaximal N →
      S.spaceIsometric (S.ambient M) (S.ambient N) →
        isometric M N
  sameAmbient_has_maximal (M : S.Lattice) (n : Nat) :
    S.rank M = n →
      ∃ N : S.Lattice,
        S.rank N = n ∧ S.isMaximal N ∧
          S.spaceRepresents (S.ambient M) (S.ambient N)
  maximal_of_represents_maximal_sameRank {M N : S.Lattice} :
    S.rank M = S.rank N → S.integral M → S.isMaximal N →
      S.represents M N → S.isMaximal M
  /-- The specialization of O'Meara (1958), Theorem 1 cited in Lemma 4.8. -/
  omeara1958Theorem1_of_isJordanZeroOne {M N : S.Lattice} :
    S.isJordanZeroOne N →
      (S.represents M N ↔
        S.spaceRepresents (S.jordanZero M) (S.jordanZero N) ∧
          S.spaceRepresents (S.jordanZeroOne M) (S.ambient N))

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
  {I : S.Lemma45InvariantData}
  {P : S.Proposition42InvariantData I}
  {isometric : S.Lattice → S.Lattice → Prop}

/-- The shared Section 5 laws carried by the invariant classification
package. -/
theorem sectionFive (H : S.CatalogueLaws I P isometric) : S.SectionFiveLaws :=
  H.proposition42.sectionFive

private theorem generalRow_defined (m : Nat) (hm : 3 ≤ m)
    (i : HeADC2025NonDyadicGeneralIndex) :
    HeADC2025NonDyadicRowIsDefined m i.1 i.2 := by
  constructor <;> omega

/-- Remark 4.3, exhaustion of maximal lattices, derived from Proposition
4.2(ii) and uniqueness of a maximal lattice on a fixed quadratic space. -/
theorem maximal_complete
    (H : S.CatalogueLaws I P isometric) (M : S.Lattice)
    (m : Nat) (hm : 1 ≤ m) (hRank : S.rank M = m)
    (hMaximal : S.isMaximal M) :
    ∃ nu : HeADC2025NonDyadicColumn,
      ∃ c : HeADC2025NonDyadicSquareClass,
        HeADC2025NonDyadicRowIsDefined m nu c ∧
          isometric M (S.target nu m c) := by
  rcases H.proposition42.heADC2025Proposition42iiNonDyadic
      (S.ambient M) m hm ((H.sectionFive.ambient_rank M).trans hRank) with
    ⟨nu, c, hDefined, hAmbient⟩
  exact ⟨nu, c, hDefined,
    H.maximal_isometric_of_ambient hMaximal
      (H.target_isMaximal m nu c hDefined) hAmbient⟩

/-- Remark 4.3, irredundancy of the maximal-lattice rows, derived from
Lemma 4.4(i) after passing an integral isometry to ambient spaces. -/
theorem target_irredundant
    (H : S.CatalogueLaws I P isometric) (m : Nat) (hm : 1 ≤ m)
    {nu mu : HeADC2025NonDyadicColumn}
    {c d : HeADC2025NonDyadicSquareClass}
    (hNu : HeADC2025NonDyadicRowIsDefined m nu c)
    (hMu : HeADC2025NonDyadicRowIsDefined m mu d)
    (hIso : isometric (S.target nu m c) (S.target mu m d)) :
    nu = mu ∧ c = d :=
  (H.proposition42.heADC2025Lemma44iNonDyadic hm hNu hMu).1
    (H.isometric_ambient hIso)

/-- He (2025), Lemma 4.8, first sentence for a defined Table 4.7 row.
The maximality assertion records the source's named maximal lattice, while
`isJordanZeroOne` is the abstract system's form of `J_{0,1}(N) = N`. -/
theorem heADC2025Lemma48_jordanZeroOne
    (H : S.CatalogueLaws I P isometric) (n : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hDefined : HeADC2025NonDyadicRowIsDefined n nu c) :
    S.isMaximal (S.target nu n c) ∧
      S.isJordanZeroOne (S.target nu n c) := by
  constructor
  · exact H.target_isMaximal n nu c hDefined
  · apply (H.sectionFive.isJordanZeroOne_iff_rank _).2
    rw [H.sectionFive.target_jordanZeroOne_rank,
      H.sectionFive.target_rank]

/-- He (2025), Lemma 4.8, complete representation equivalence for a defined
Table 4.7 row, derived from the cited general O'Meara representation theorem. -/
theorem heADC2025Lemma48
    (H : S.CatalogueLaws I P isometric) (M : S.Lattice) (n : Nat)
    (nu : HeADC2025NonDyadicColumn)
    (c : HeADC2025NonDyadicSquareClass)
    (hDefined : HeADC2025NonDyadicRowIsDefined n nu c) :
    S.represents M (S.target nu n c) ↔
      S.spaceRepresents (S.jordanZero M)
          (S.jordanZero (S.target nu n c)) ∧
        S.spaceRepresents (S.jordanZeroOne M)
          (S.ambient (S.target nu n c)) :=
  H.omeara1958Theorem1_of_isJordanZeroOne
    (H.heADC2025Lemma48_jordanZeroOne n nu c hDefined).2

/-- He (2025), Proposition 4.15, necessity over a non-dyadic local field.
Choose a maximal lattice on the source space, use `n`-ADC to represent it,
and transfer maximality across the resulting same-rank representation. -/
theorem heADC2025Proposition415_isMaximal
    (H : S.CatalogueLaws I P isometric) (M : S.Lattice) (n : Nat)
    (hRank : S.rank M = n) (hADC : S.IsNADC M n) :
    S.isMaximal M := by
  obtain ⟨N, hRankN, hMaximalN, hAmbient⟩ :=
    H.sameAmbient_has_maximal M n hRank
  have hMN : S.represents M N :=
    hADC.2 N hRankN (H.sectionFive.isMaximal_integral hMaximalN) hAmbient
  exact H.maximal_of_represents_maximal_sameRank
    (hRank.trans hRankN.symm) hADC.1 hMaximalN hMN

/-- He (2025), Proposition 4.15, full non-dyadic equivalence relative to
the explicit maximal-lattice construction and representation laws. -/
theorem heADC2025Proposition415
    (H : S.CatalogueLaws I P isometric) (M : S.Lattice) (n : Nat)
    (_hN : 2 ≤ n) (hRank : S.rank M = n) :
    S.IsNADC M n ↔ S.isMaximal M := by
  constructor
  · intro hADC
    exact H.heADC2025Proposition415_isMaximal M n hRank hADC
  · intro hMaximal
    exact H.sectionFive.isMaximal_isNADC hMaximal n

/-- A maximality implication supplies an exact eight-row catalogue in every
rank at least three. -/
theorem general_exactCatalogue_of_isMaximal
    (H : S.CatalogueLaws I P isometric) (n m : Nat) (hm : 3 ≤ m)
    (hMaximal : ∀ M : S.Lattice,
      S.rank M = m → S.IsNADC M n → S.isMaximal M) :
    S.IsExactNADCIsometryCatalogue isometric n m
      (S.nonDyadicGeneralFamily m) where
  rank i := H.sectionFive.target_rank i.1 m i.2
  nADC i := H.sectionFive.isMaximal_isNADC
    (H.target_isMaximal m i.1 i.2 (generalRow_defined m hm i)) n
  complete M hRank hADC := by
    obtain ⟨nu, c, hDefined, hIso⟩ :=
      H.maximal_complete M m (by omega) hRank (hMaximal M hRank hADC)
    exact ⟨(nu, c), hIso⟩
  irredundant {i j} hIso := by
    obtain ⟨hnu, hc⟩ := H.target_irredundant m (by omega)
      (generalRow_defined m hm i) (generalRow_defined m hm j) hIso
    exact Prod.ext hnu hc

/-- The equal-rank binary branch is the exact seven-row catalogue. -/
theorem binary_exactCatalogue (H : S.CatalogueLaws I P isometric) :
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
    obtain ⟨nu, c, hDefined, hIso⟩ := H.maximal_complete M 2 (by omega) hRank
      (H.heADC2025Proposition415_isMaximal M 2 hRank hADC)
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
    obtain ⟨hnu, hc⟩ := H.target_irredundant 2 (by omega)
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
    (H : S.CatalogueLaws I P isometric) :
    Theorem110NonDyadicConclusion (S := S) isometric where
  binary := ⟨H.binary_exactCatalogue,
    card_heADC2025NonDyadicBinaryIndex⟩
  equalRank m hm :=
    ⟨H.general_exactCatalogue_of_isMaximal m m hm
      (fun M hRank hADC =>
        H.heADC2025Proposition415_isMaximal M m hRank hADC),
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
