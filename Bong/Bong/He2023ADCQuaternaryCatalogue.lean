/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCCorollary721
import Bong.Bong.He2023ADCExceptionalQuaternaryTesting
import Bong.Bong.He2023ADCQuaternaryBoundaryClassification
import Bong.Bong.He2023ADCTheorem62Discrepancy

/-!
# The corrected quaternary 2-ADC catalogue in He (2025)

The binary instance of Theorems 1.9(ii), 1.10, and 6.2 omits one
nonmaximal class.  This file packages the corrected classification as a
finite, complete, and irredundant isometry catalogue.  Its maximal part is
the four-row published even table in rank four.  Its two additional indices
are the exceptional lattice from Lemma 6.12 and the independently constructed
second-discriminant boundary lattice.

Consequently the corrected total is `4 * |U| + 2`, hence
`8 * (N p)^e + 2` after the same O'Meara 63:9 counting input used in the
paper.  The printed formula has `+ 1` and is therefore refuted as a separate
formal proposition below.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace HeADC2025QuaternaryCatalogue

variable {I : Type u} (U : I -> Kˣ)

/-- The exceptional lattice from Lemma 6.12 as a bundled model. -/
noncomputable def exceptionalModel :
    Lattice.QuadraticLatticeModel (K := K) where
  Carrier := Lattice.HyperbolicExtension K (Fin 2 -> K) 1
  form := BONG.GoodBONG.heADCExceptionalQuaternaryForm (K := K)
  lattice := BONG.GoodBONG.heADCExceptionalQuaternaryLattice (K := K)

/-- The omitted second-discriminant boundary lattice as a bundled model. -/
noncomputable def boundaryModel :
    Lattice.QuadraticLatticeModel (K := K) where
  Carrier := Lattice.HyperbolicExtension K (Fin 2 -> K) 1
  form := BONG.GoodBONG.heADCQuaternaryBoundaryForm (K := K)
  lattice := BONG.GoodBONG.heADCQuaternaryBoundaryLattice (K := K)

/-- Four maximal rank-four rows, followed by the two nonmaximal classes. -/
abbrev Index := HeHuPublishedEvenTestingIndex (K := K) U 1 ⊕ Bool

/-- The corrected representative attached to a catalogue index. -/
noncomputable def model : Index (K := K) U ->
    Lattice.QuadraticLatticeModel (K := K)
  | .inl i => HeHuPublishedEvenTestingIndex.model (K := K) i
  | .inr false => exceptionalModel (K := K)
  | .inr true => boundaryModel (K := K)

/-- Integral isometry between two bundled catalogue representatives. -/
abbrev IsIntegrallyIsometric :=
  HeADC2025Corollary721Index.IsIntegrallyIsometric (K := K)

/-- The exceptional model has rank four. -/
theorem exceptionalModel_rank :
    (exceptionalModel (K := K)).rank = 4 := by
  change finrank K (Lattice.HyperbolicExtension K (Fin 2 -> K) 1) = 4
  exact
    (BONG.GoodBONG.heADCExceptionalQuaternaryCandidate
      (K := K)).toBONG.length_eq_finrank.symm

/-- The boundary model has rank four. -/
theorem boundaryModel_rank :
    (boundaryModel (K := K)).rank = 4 := by
  change finrank K (Lattice.HyperbolicExtension K (Fin 2 -> K) 1) = 4
  exact
    (BONG.GoodBONG.heADCQuaternaryBoundaryCandidate
      (K := K)).toBONG.length_eq_finrank.symm

/-- The exceptional model is 2-ADC. -/
theorem exceptionalModel_isNADC :
    (exceptionalModel (K := K)).IsNADC 2 := by
  exact BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC (K := K)

/-- The boundary model is 2-ADC. -/
theorem boundaryModel_isNADC :
    (boundaryModel (K := K)).IsNADC 2 := by
  exact BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_is2ADC (K := K)

/-- The exceptional model is genuinely nonmaximal. -/
theorem exceptionalModel_not_isOMaximal :
    ¬ (exceptionalModel (K := K)).IsOMaximal := by
  exact BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_isOMaximal
    (K := K)

/-- The boundary model is genuinely nonmaximal. -/
theorem boundaryModel_not_isOMaximal :
    ¬ (boundaryModel (K := K)).IsOMaximal := by
  exact BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isOMaximal
    (K := K)

/-- Every corrected catalogue representative has rank four. -/
theorem model_rank (x : Index (K := K) U) :
    (model (K := K) U x).rank = 4 := by
  rcases x with i | b
  · exact HeHuPublishedEvenTestingIndex.model_rank i
  · cases b
    · exact exceptionalModel_rank (K := K)
    · exact boundaryModel_rank (K := K)

/-- Every corrected catalogue representative is 2-ADC. -/
theorem model_isNADC (x : Index (K := K) U) :
    (model (K := K) U x).IsNADC 2 := by
  rcases x with i | b
  · exact (HeHuPublishedEvenTestingIndex.model_isOMaximal i).isNADC 2
  · cases b
    · exact exceptionalModel_isNADC (K := K)
    · exact boundaryModel_isNADC (K := K)

/-- Every rank-four 2-ADC lattice is integrally isometric to a member of the
corrected catalogue. -/
theorem exists_index_isIntegrallyIsometric
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (X : Lattice.QuadraticLatticeModel (K := K))
    (hRank : X.rank = 4) (hADC : X.IsNADC 2) :
    ∃ x : Index (K := K) U,
      IsIntegrallyIsometric (K := K) X (model (K := K) U x) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hfinrank : finrank K X.Carrier = 4 := by
    simpa only [Lattice.QuadraticLatticeModel.rank] using hRank
  change Lattice.IsNADC.{u, u, u} X.form X.lattice 2 at hADC
  rcases Lattice.heADC2025Theorem62_binary_corrected hADC hfinrank with
    hmaximal | hexceptional | hboundary
  · obtain ⟨i, hambient⟩ :=
      Lattice.QuadraticLatticeModel.exists_publishedEvenIndex_for_model
        U hU 1 X (by omega)
    let Y := HeHuPublishedEvenTestingIndex.model (K := K) i
    letI : AddCommGroup Y.Carrier := Y.addCommGroup
    letI : Module K Y.Carrier := Y.module
    have hisometric : Lattice.IsIsometric X.form Y.form X.lattice Y.lattice :=
      Lattice.oMaximal_isIsometric_of_isometric hmaximal
        (HeHuPublishedEvenTestingIndex.model_isOMaximal i) hambient
    exact ⟨.inl i, hisometric⟩
  · exact ⟨.inr false, hexceptional⟩
  · exact ⟨.inr true, hboundary⟩

/-- Different corrected indices give different integral isometry classes. -/
theorem model_eq_of_isIntegrallyIsometric
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {x y : Index (K := K) U}
    (hiso : IsIntegrallyIsometric (K := K)
      (model (K := K) U x) (model (K := K) U y)) :
    x = y := by
  rcases x with i | b
  · rcases y with j | c
    · let X := HeHuPublishedEvenTestingIndex.model (K := K) i
      let Y := HeHuPublishedEvenTestingIndex.model (K := K) j
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      letI : AddCommGroup Y.Carrier := Y.addCommGroup
      letI : Module K Y.Carrier := Y.module
      change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
      rcases hiso with ⟨f⟩
      have hambient : X.IsAmbientlyIsometric Y :=
        ⟨f.toQuadraticSpaceIsometry⟩
      exact congrArg Sum.inl
        (Lattice.QuadraticLatticeModel.heHuPublishedEven_model_eq_of_ambientlyIsometric
          U hU hambient)
    · cases c
      · let X := HeHuPublishedEvenTestingIndex.model (K := K) i
        let Y := exceptionalModel (K := K)
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        rcases hiso with ⟨f⟩
        exfalso
        exact (exceptionalModel_not_isOMaximal (K := K))
          ((HeHuPublishedEvenTestingIndex.model_isOMaximal i).of_latticeIsometry f)
      · let X := HeHuPublishedEvenTestingIndex.model (K := K) i
        let Y := boundaryModel (K := K)
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        rcases hiso with ⟨f⟩
        exfalso
        exact (boundaryModel_not_isOMaximal (K := K))
          ((HeHuPublishedEvenTestingIndex.model_isOMaximal i).of_latticeIsometry f)
  · rcases y with j | c
    · cases b
      · let X := exceptionalModel (K := K)
        let Y := HeHuPublishedEvenTestingIndex.model (K := K) j
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        rcases hiso with ⟨f⟩
        exfalso
        exact (exceptionalModel_not_isOMaximal (K := K))
          ((HeHuPublishedEvenTestingIndex.model_isOMaximal j).of_latticeIsometry f.symm)
      · let X := boundaryModel (K := K)
        let Y := HeHuPublishedEvenTestingIndex.model (K := K) j
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        rcases hiso with ⟨f⟩
        exfalso
        exact (boundaryModel_not_isOMaximal (K := K))
          ((HeHuPublishedEvenTestingIndex.model_isOMaximal j).of_latticeIsometry f.symm)
    · cases b <;> cases c
      · rfl
      · let X := exceptionalModel (K := K)
        let Y := boundaryModel (K := K)
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        rcases hiso with ⟨f⟩
        exfalso
        exact
          (BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isometric_exceptional
            (K := K)) ⟨f.symm⟩
      · let X := boundaryModel (K := K)
        let Y := exceptionalModel (K := K)
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        letI : AddCommGroup Y.Carrier := Y.addCommGroup
        letI : Module K Y.Carrier := Y.module
        change Lattice.IsIsometric X.form Y.form X.lattice Y.lattice at hiso
        exfalso
        exact
          (BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isometric_exceptional
            (K := K)) hiso
      · rfl

/-- A rank-four family is an exact 2-ADC isometry catalogue if all entries
have the right rank and property, every such lattice occurs, and no class is
repeated. -/
structure IsExactIsometryCatalogue
    {J : Type u} (family : J -> Lattice.QuadraticLatticeModel (K := K)) :
    Prop where
  rank (j : J) : (family j).rank = 4
  nADC (j : J) : (family j).IsNADC 2
  complete (X : Lattice.QuadraticLatticeModel (K := K)) :
    X.rank = 4 -> X.IsNADC 2 ->
      ∃ j : J, IsIntegrallyIsometric (K := K) X (family j)
  irredundant {i j : J} :
    IsIntegrallyIsometric (K := K) (family i) (family j) -> i = j

/-- The six-row corrected family is a complete and irredundant catalogue. -/
theorem isExactIsometryCatalogue
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    IsExactIsometryCatalogue (K := K) (model (K := K) U) where
  rank := model_rank U
  nADC := model_isNADC U
  complete := exists_index_isIntegrallyIsometric U hU
  irredundant := model_eq_of_isIntegrallyIsometric U hU

/-- Maximality is exactly membership in the published-table summand. -/
theorem model_isOMaximal_iff
    (x : Index (K := K) U) :
    (model (K := K) U x).IsOMaximal ↔
      ∃ i : HeHuPublishedEvenTestingIndex (K := K) U 1, x = .inl i := by
  rcases x with i | b
  · exact ⟨fun _ ↦ ⟨i, rfl⟩,
      fun _ ↦ HeHuPublishedEvenTestingIndex.model_isOMaximal i⟩
  · cases b
    · constructor
      · exact fun h ↦ (exceptionalModel_not_isOMaximal (K := K) h).elim
      · rintro ⟨i, h⟩
        cases h
    · constructor
      · exact fun h ↦ (boundaryModel_not_isOMaximal (K := K) h).elim
      · rintro ⟨i, h⟩
        cases h

/-- The corrected catalogue has four maximal rows and two nonmaximal rows. -/
theorem card_index [Fintype I] :
    Fintype.card (Index (K := K) U) = 4 * Fintype.card I + 2 := by
  rw [Fintype.card_sum,
    card_heHuPublishedEvenTestingIndex_of_pos U (by omega : 0 < 1),
    Fintype.card_bool]

/-- Numerical corrected count after the proved unit square-class formula of
O'Meara 63:9. -/
theorem card_index_corrected
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (Index (K := K) U) =
      8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K + 2 := by
  rw [card_index,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

/-- The exact binary count printed in Theorem 1.10. -/
def HeADC2025Theorem110BinaryCountStatement [Fintype I] : Prop :=
  Fintype.card (Index (K := K) U) =
    8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K + 1

/-- The `+1` binary count in Theorem 1.10 is false; the corrected catalogue
contains two nonmaximal classes. -/
theorem not_heADC2025Theorem110BinaryCountStatement
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    ¬ HeADC2025Theorem110BinaryCountStatement (K := K) U := by
  rw [HeADC2025Theorem110BinaryCountStatement, card_index_corrected U hU]
  omega

/-- The exact binary specialization of Theorem 1.9(ii) is the same
biconditional as the binary specialization of Theorem 6.2. -/
abbrev HeADC2025Theorem19iiBinaryStatement : Prop :=
  BONG.GoodBONG.HeADC2025Theorem62BinaryStatement (K := K)

/-- The binary specialization of Theorem 1.9(ii) is false. -/
theorem not_heADC2025Theorem19iiBinaryStatement :
    ¬ HeADC2025Theorem19iiBinaryStatement (K := K) :=
  BONG.GoodBONG.not_heADC2025Theorem62BinaryStatement (K := K)

/-- Corrected binary specialization of Theorems 1.9(ii) and 6.2. -/
def HeADC2025Theorem19iiBinaryCorrectedStatement : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V),
    finrank K V = 4 ->
      (Lattice.IsNADC.{u, u, u} q L 2 ↔
        Lattice.IsOMaximal q L ∨
          Lattice.IsIsometric q
            (BONG.GoodBONG.heADCExceptionalQuaternaryForm (K := K)) L
            (BONG.GoodBONG.heADCExceptionalQuaternaryLattice (K := K)) ∨
          Lattice.IsIsometric q
            (BONG.GoodBONG.heADCQuaternaryBoundaryForm (K := K)) L
            (BONG.GoodBONG.heADCQuaternaryBoundaryLattice (K := K)))

/-- Proof of the corrected binary biconditional. -/
theorem heADC2025Theorem19ii_binary_corrected :
    HeADC2025Theorem19iiBinaryCorrectedStatement (K := K) := by
  intro V _ _ q L hRank
  constructor
  · exact fun hADC ↦ Lattice.heADC2025Theorem62_binary_corrected hADC hRank
  · rintro (hmaximal | hexceptional | hboundary)
    · exact hmaximal.isNADC 2
    · rcases hexceptional with ⟨f⟩
      exact
        (BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC
          (K := K)).of_latticeIsometry f.symm
    · rcases hboundary with ⟨f⟩
      exact
        (BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_is2ADC
          (K := K)).of_latticeIsometry f.symm

/-- Corrected binary conclusions: exact classification and exact count. -/
theorem heADC2025Theorems19iiAnd110BinaryCorrected
    [Fintype I]
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    HeADC2025Theorem19iiBinaryCorrectedStatement (K := K) ∧
      IsExactIsometryCatalogue (K := K) (model (K := K) U) ∧
      Fintype.card (Index (K := K) U) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K + 2 := by
  exact ⟨heADC2025Theorem19ii_binary_corrected (K := K),
    isExactIsometryCatalogue U hU, card_index_corrected U hU⟩

end HeADC2025QuaternaryCatalogue

end Bong
