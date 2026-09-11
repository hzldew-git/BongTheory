/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma720
import Bong.Bong.He2023ADCTheorem72Published
import Bong.Bong.He2023ADCUnitRepresentativeCount
import Bong.Bong.GoodExistence
import Bong.Bong.StructuralProof
import Bong.Dyadic.UnitSquareClassCount

/-!
# He (2025), Corollary 7.21

This file turns Definition 7.16 and Lemma 7.20 into an actual finite,
complete, and irredundant catalogue of the odd-corank-two `n`-ADC isometry
classes.  The index is split into the maximal and nonmaximal parts printed in
the proof of Corollary 7.21:

* the three endpoint rows of Lemma 7.20(i), together with the one overlap row
  of Lemma 7.20(ii), give `4 * |U|` maximal classes;
* the remaining rows of Lemma 7.20(iii) give `(4e - 1) * |U|` nonmaximal
  classes.

The final substitution `|U| = 2 * (N p)^e`, quoted in the paper from O'Meara
63:9, is proved from the principal-unit filtration in
`Bong.Dyadic.UnitSquareClassCount`.  Thus the numerical conclusions below do
not require an external counting hypothesis.
-/

namespace Bong

open Dyadic Module HeHuPublishedSquareClassIndex

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The residue-field norm `N p` in Corollary 7.21. -/
noncomputable def heADC2025ResidueNorm : Nat := by
  letI := Fintype.ofFinite (normalizedResidueField K)
  exact Fintype.card (normalizedResidueField K)

namespace HeADC2025Corollary721CountingLaw

/-- O'Meara's intrinsic unit-square-class cardinality formula in the notation
of He (2025). -/
theorem card_unit_square_classes :
    Nat.card (ValuationUnitClass K) =
      2 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  simpa [heADC2025ResidueNorm, Fintype.card_eq_nat_card] using
    card_valuationUnitClass K

/-- The intrinsic unit-square-class count transported to any complete
irredundant normalized representative system. -/
theorem card_unit_representatives
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card I =
      2 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_heHuCompleteUnitRepresentativeSystem U hU]
  exact HeADC2025Corollary721CountingLaw.card_unit_square_classes

end HeADC2025Corollary721CountingLaw

/-- The three endpoint rows in Lemma 7.20(i): the first ambient column for
both valuation parities and the second column only for odd valuation. -/
abbrev HeADC2025Corollary721TopIndex (I : Type u) :=
  HeHuPublishedSquareClassIndex I ⊕ I

/-- The three nonoverlap ambient rows at `r=e-1`. -/
abbrev HeADC2025Corollary721LastNonmaximalIndex (I : Type u) :=
  HeHuPublishedSquareClassIndex I ⊕ I

/-- The maximal catalogue: the three top rows and the exceptional
second-column unit row one level lower. -/
abbrev HeADC2025Corollary721MaximalIndex (I : Type u) :=
  HeADC2025Corollary721TopIndex I ⊕ I

/-- The nonmaximal catalogue: all four ambient rows before `e-1`, followed by
the three nonoverlap rows at `e-1`. -/
abbrev HeADC2025Corollary721NonmaximalIndex
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] (I : Type u) :=
  (Fin (ramificationIndex K - 1) × HeHuPublishedOddTestingIndex I) ⊕
    HeADC2025Corollary721LastNonmaximalIndex I

/-- The complete finite index of Corollary 7.21, visibly partitioned into
maximal and nonmaximal classes. -/
abbrev HeADC2025Corollary721Index
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] (I : Type u) :=
  HeADC2025Corollary721MaximalIndex I ⊕
    HeADC2025Corollary721NonmaximalIndex K I

namespace HeADC2025Corollary721Index

variable {I : Type u} [Fintype I] (U : I -> Kˣ)

/-- The published odd ambient-table row attached to a catalogue index. -/
def ambientIndex : HeADC2025Corollary721Index K I ->
    HeHuPublishedOddTestingIndex I
  | .inl (.inl (.inl p)) => .inl p
  | .inl (.inl (.inr i)) => .inr (i, true)
  | .inl (.inr i) => .inr (i, false)
  | .inr (.inl (_, j)) => j
  | .inr (.inr (.inl p)) => .inl p
  | .inr (.inr (.inr i)) => .inr (i, true)

/-- The column `nu in {1,2}` attached to a published odd ambient row. -/
def publishedColumn : HeHuPublishedOddTestingIndex I -> HeADC716Column
  | .inl _ => .one
  | .inr _ => .two

/-- The scalar parameter attached to a published odd ambient row. -/
noncomputable def publishedParameter : HeHuPublishedOddTestingIndex I -> Kˣ
  | .inl p => HeHuPublishedSquareClassIndex.parameter (K := K) U p
  | .inr p => HeHuPublishedSquareClassIndex.parameter (K := K) U p

/-- The column `nu in {1,2}` attached to a catalogue index. -/
def column (x : HeADC2025Corollary721Index K I) : HeADC716Column :=
  publishedColumn (ambientIndex (K := K) x)

/-- The normalized scalar parameter attached to a catalogue index. -/
noncomputable def parameter (x : HeADC2025Corollary721Index K I) : Kˣ :=
  publishedParameter (K := K) U (ambientIndex (K := K) x)

/-- The row `r in {0,...,e}` attached to a catalogue index. -/
noncomputable def row : HeADC2025Corollary721Index K I -> Nat
  | .inl (.inl _) => ramificationIndex K
  | .inl (.inr _) => ramificationIndex K - 1
  | .inr (.inl (r, _)) => r.val
  | .inr (.inr _) => ramificationIndex K - 1

omit [Fintype I] in
theorem row_le (x : HeADC2025Corollary721Index K I) :
    row (K := K) x <= ramificationIndex K := by
  rcases x with (x | x)
  · rcases x with (x | i)
    · exact le_rfl
    · exact Nat.sub_le _ _
  · rcases x with (x | x)
    · exact (Nat.lt_of_lt_of_le x.1.isLt (Nat.sub_le _ _)).le
    · exact Nat.sub_le _ _

theorem parameter_order
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (x : HeADC2025Corollary721Index K I) :
    ordUnit K (parameter (K := K) U x) = 0 ∨
      ordUnit K (parameter (K := K) U x) = 1 := by
  unfold parameter
  cases ambientIndex (K := K) x with
  | inl p =>
      exact BONG.GoodBONG.heADC2025Theorem72_publishedParameterOrder U hU p
  | inr p =>
      exact BONG.GoodBONG.heADC2025Theorem72_publishedParameterOrder U hU p

theorem not_exceptional
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (x : HeADC2025Corollary721Index K I) :
    ¬ (column (K := K) x = HeADC716Column.two ∧
      row (K := K) x = ramificationIndex K ∧
      ordUnit K (parameter (K := K) U x) = 0) := by
  rcases x with (x | x)
  · rcases x with (x | i)
    · rcases x with (p | i)
      · simp [column, publishedColumn, ambientIndex]
      · intro h
        have horder : ordUnit K
            (parameter (K := K) U
              (.inl (.inl (.inr i)) : HeADC2025Corollary721Index K I)) = 1 := by
          change ordUnit K (U i * uniformizerPowerUnit K (1 : Int)) = 1
          rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
            (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
          norm_num
        rw [horder] at h
        omega
    · intro h
      simp [row] at h
      have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
      omega
  · rcases x with (x | x)
    · intro h
      have hlt : x.1.val < ramificationIndex K :=
        x.1.isLt.trans_le (Nat.sub_le _ _)
      simp [row] at h
      omega
    · intro h
      simp [row] at h
      have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
      omega

/-- Every catalogue index denotes an inhabited Definition 7.16 class. -/
theorem isDefined
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    BONG.GoodBONG.HeADC2025Definition716IsDefined k
      (row (K := K) x) (column (K := K) x)
      (parameter (K := K) U x) :=
  BONG.GoodBONG.heADC2025Lemma720_defined_of_not_exception
    k (row (K := K) x) (column (K := K) x)
      (parameter (K := K) U x) (row_le (K := K) x) (parameter_order U hU x)
        (not_exceptional U hU x)

/-- A chosen bundled representative of the class denoted by an index. -/
noncomputable def model
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    Lattice.QuadraticLatticeModel (K := K) :=
  Classical.choose (isDefined U hU k x)

theorem exists_goodBONG_definition
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    let X := model U hU k x
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    ∃ a : BONG.GoodBONG X.form X.lattice (2 * k + 5),
      a.HeADC2025Definition716 k (row (K := K) x)
        (column (K := K) x) (parameter (K := K) U x) := by
  exact Classical.choose_spec (isDefined U hU k x)

/-- A chosen good BONG witnessing the Definition 7.16 class of `model`. -/
noncomputable def goodBONG
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    let X := model U hU k x
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    BONG.GoodBONG X.form X.lattice (2 * k + 5) :=
  Classical.choose (exists_goodBONG_definition U hU k x)

theorem goodBONG_definition
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    let X := model U hU k x
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    (goodBONG U hU k x).HeADC2025Definition716 k
      (row (K := K) x) (column (K := K) x)
      (parameter (K := K) U x) :=
  Classical.choose_spec (exists_goodBONG_definition U hU k x)

/-- Integral isometry between two bundled representatives in the catalogue. -/
def IsIntegrallyIsometric
    (X Y : Lattice.QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.IsIsometric X.form Y.form X.lattice Y.lattice

/-- Every chosen representative has the rank printed in Corollary 7.21. -/
theorem model_rank
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    (model U hU k x).rank = 2 * k + 5 := by
  let X := model U hU k x
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hlength := (goodBONG U hU k x).toBONG.length_eq_finrank
  simpa only [Lattice.QuadraticLatticeModel.rank, X] using hlength.symm

/-- Every chosen representative is `(2k+3)`-ADC. -/
theorem model_isNADC
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    (model U hU k x).IsNADC (2 * k + 3) := by
  let X := model U hU k x
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact (goodBONG_definition U hU k x).nADC

omit [Fintype I] in
/-- The pair `(r, ambient row)` remembers the catalogue index. -/
theorem eq_of_row_eq_ambientIndex_eq
    {x y : HeADC2025Corollary721Index K I}
    (hrow : row (K := K) x = row (K := K) y)
    (hambient : ambientIndex (K := K) x = ambientIndex (K := K) y) :
    x = y := by
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  rcases x with (((p | i) | j) | (⟨r, a⟩ | (q | l))) <;>
    rcases y with (((p' | i') | j') | (⟨r', a'⟩ | (q' | l'))) <;>
    simp [row, ambientIndex] at hrow hambient ⊢ <;>
    try omega
  exact ⟨Fin.ext hrow, hambient⟩

omit [Fintype I] in
/-- The ambient form selected by a catalogue index is literally the form of
the corresponding row in the published odd maximal table. -/
theorem publishedModel_form_eq (pairs : Nat)
    (j : HeHuPublishedOddTestingIndex I) :
    (HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) j).form =
      BONG.coefficientDiagonalSpace
        ((publishedColumn j).coefficients pairs
          (publishedParameter (K := K) U j)) := by
  rcases j with (p | p) <;> rfl

/-- Every nonexceptional pair consisting of a row and a published odd ambient
row occurs exactly once in the partitioned catalogue. -/
theorem exists_index_of_not_exception
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (rIndex : Nat) (hr : rIndex <= ramificationIndex K)
    (j : HeHuPublishedOddTestingIndex I)
    (hnot : ¬ (publishedColumn j = HeADC716Column.two ∧
      rIndex = ramificationIndex K ∧
      ordUnit K (publishedParameter (K := K) U j) = 0)) :
    ∃ x : HeADC2025Corollary721Index K I,
      row (K := K) x = rIndex ∧ ambientIndex (K := K) x = j := by
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  rcases lt_or_eq_of_le hr with hrlt | hre
  · by_cases hlast : rIndex = ramificationIndex K - 1
    · subst rIndex
      rcases j with p | p
      · refine ⟨.inr (.inr (.inl p)), ?_, ?_⟩ <;> rfl
      · rcases p with ⟨i, parity⟩
        cases parity with
        | false =>
            refine ⟨.inl (.inr i), ?_, ?_⟩ <;> rfl
        | true =>
            refine ⟨.inr (.inr (.inr i)), ?_, ?_⟩ <;> rfl
    · have hrEarly : rIndex < ramificationIndex K - 1 := by omega
      let r : Fin (ramificationIndex K - 1) := ⟨rIndex, hrEarly⟩
      refine ⟨.inr (.inl (r, j)), ?_, ?_⟩ <;> rfl
  · subst rIndex
    rcases j with p | p
    · exact ⟨.inl (.inl (.inl p)), rfl, rfl⟩
    · rcases p with ⟨i, parity⟩
      cases parity with
      | false =>
          exfalso
          apply hnot
          refine ⟨rfl, rfl, ?_⟩
          exact (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)
      | true =>
          exact ⟨.inl (.inl (.inr i)), rfl, rfl⟩

/-- Different catalogue indices give different integral isometry classes. -/
theorem model_eq_of_isIntegrallyIsometric
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) {x y : HeADC2025Corollary721Index K I}
    (hiso : IsIntegrallyIsometric (model U hU k x) (model U hU k y)) :
    x = y := by
  let X := model U hU k x
  let Y := model U hU k y
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  let a := goodBONG U hU k x
  let b := goodBONG U hU k y
  have A := goodBONG_definition U hU k x
  have B := goodBONG_definition U hU k y
  have hclass := (a.heADC2025Lemma715 k b A.nADC B.nADC).mp hiso
  have hrow : row (K := K) x = row (K := K) y := by
    rw [A.penultimate, B.penultimate] at hclass
    omega
  have hambient : ambientIndex (K := K) x = ambientIndex (K := K) y := by
    let P := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := k + 1) (ambientIndex (K := K) x)
    let Q := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := k + 1) (ambientIndex (K := K) y)
    letI : AddCommGroup P.Carrier := P.addCommGroup
    letI : Module K P.Carrier := P.module
    letI : AddCommGroup Q.Carrier := Q.addCommGroup
    letI : Module K Q.Carrier := Q.module
    apply Lattice.QuadraticLatticeModel.heHuPublishedOdd_model_eq_of_ambientlyIsometric
      U hU
    change P.form.IsIsometric Q.form
    dsimp only [P, Q]
    rw [publishedModel_form_eq (K := K) U (k + 1),
      publishedModel_form_eq (K := K) U (k + 1)]
    exact ⟨(Classical.choice A.ambient).symm.trans
      ((Classical.choice hclass.1).trans (Classical.choice B.ambient))⟩
  exact eq_of_row_eq_ambientIndex_eq (K := K) hrow hambient

/-- Completeness of the catalogue: every `(2k+3)`-ADC lattice of rank
`2k+5` is integrally isometric to one of the chosen representatives. -/
theorem exists_index_isIntegrallyIsometric
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (X : Lattice.QuadraticLatticeModel (K := K))
    (hRank : X.rank = 2 * k + 5)
    (hADC : X.IsNADC (2 * k + 3)) :
    ∃ x : HeADC2025Corollary721Index K I,
      IsIntegrallyIsometric X (model U hU k x) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : BONGStructuralLaws.{u, u} K := bongStructuralLawsProved K
  have hlength : finrank K X.Carrier = 2 * k + 5 := by
    simpa only [Lattice.QuadraticLatticeModel.rank] using hRank
  let a := (BONG.GoodBONG.ofLattice X.form X.lattice).castLength hlength
  change Lattice.IsNADC.{u, u, u} X.form X.lattice (2 * k + 3) at hADC
  obtain ⟨nu, rIndex, c, A⟩ := a.heADC2025Remark717_exhaustion k hADC
  have hRank' : X.rank = 2 * (k + 1) + 3 := by omega
  obtain ⟨j, hj⟩ :=
    Lattice.QuadraticLatticeModel.exists_publishedOddIndex_for_model
      U hU (k + 1) X hRank'
  let P := HeHuPublishedOddTestingIndex.model
    (K := K) (U := U) (pairs := k + 1) j
  letI : AddCommGroup P.Carrier := P.addCommGroup
  letI : Module K P.Carrier := P.module
  have hambient : X.form.IsIsometric P.form := hj
  dsimp only [P] at hambient
  rw [publishedModel_form_eq (K := K) U (k + 1) j] at hambient
  have hparameter :
      ordUnit K (publishedParameter (K := K) U j) = 0 ∨
        ordUnit K (publishedParameter (K := K) U j) = 1 := by
    rcases j with p | p
    · exact BONG.GoodBONG.heADC2025Theorem72_publishedParameterOrder U hU p
    · exact BONG.GoodBONG.heADC2025Theorem72_publishedParameterOrder U hU p
  have C : a.HeADC2025Definition716 k rIndex (publishedColumn j)
      (publishedParameter (K := K) U j) :=
    { indexBound := A.indexBound
      parameterOrder := hparameter
      nADC := hADC
      ambient := hambient
      penultimate := A.penultimate }
  have hnot : ¬ (publishedColumn j = HeADC716Column.two ∧
      rIndex = ramificationIndex K ∧
      ordUnit K (publishedParameter (K := K) U j) = 0) := by
    apply (BONG.GoodBONG.heADC2025Lemma720_defined_iff k rIndex
      (publishedColumn j) (publishedParameter (K := K) U j)
        C.indexBound C.parameterOrder).1
    exact C.isDefined
  obtain ⟨x, hrow, hambientIndex⟩ :=
    exists_index_of_not_exception U hU rIndex C.indexBound j hnot
  let Y := model U hU k x
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  let b := goodBONG U hU k x
  have B := goodBONG_definition U hU k x
  have B' : b.HeADC2025Definition716 k rIndex (publishedColumn j)
      (publishedParameter (K := K) U j) := by
    simpa only [hrow, column, hambientIndex, parameter] using B
  exact ⟨x, a.heADC2025Remark717_unique k rIndex (publishedColumn j)
    (publishedParameter (K := K) U j) b C B'⟩

/-- Every index in the left summand denotes an `O`-maximal lattice. -/
theorem model_isOMaximal_of_maximalIndex
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (m : HeADC2025Corollary721MaximalIndex I) :
    (model U hU k (.inl m)).IsOMaximal := by
  let X := model U hU k (.inl m)
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  let a := goodBONG U hU k (.inl m)
  have A := goodBONG_definition U hU k (.inl m)
  rcases m with top | i
  · apply a.heADC2025Lemma715_isOMaximal_of_penultimate k A.nADC
    simpa only [row] using A.penultimate
  · have hiOrder : ordUnit K (U i) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)
    have A' : a.HeADC2025Definition716 k (ramificationIndex K - 1)
        HeADC716Column.two (U i) := by
      simpa only [row, column, ambientIndex, publishedColumn, parameter,
        publishedParameter,
        HeHuPublishedSquareClassIndex.parameter_unit] using A
    have hisometric :=
      BONG.GoodBONG.heADC2025Lemma720ii_isometricNamed k (U i) a hiOrder A'
    exact (heHuOMaximalLattice_isOMaximal
      (heADCW2Odd (K := K) (k + 1) (U i))).of_latticeIsometry
        (Classical.choice hisometric).symm

/-- A maximal class below the top row is forced to be precisely the
second-column unit overlap in Lemma 7.20(ii). -/
theorem lower_maximal_index_characterization
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I)
    (hrowLt : row (K := K) x < ramificationIndex K)
    (hmaximal : (model U hU k x).IsOMaximal) :
    row (K := K) x = ramificationIndex K - 1 ∧
      ∃ i : I, ambientIndex (K := K) x = .inr (i, false) := by
  let X := model U hU k x
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  let a := goodBONG U hU k x
  have A := goodBONG_definition U hU k x
  let d : Int := 2 * (row (K := K) x : Int) + 1
  have hdLt : d < 2 * (ramificationIndex K : Int) := by
    dsimp only [d]
    omega
  have horder : a.order ⟨2 * k + 3, by omega⟩ = 1 - d := by
    rw [A.penultimate]
    dsimp only [d]
    ring
  obtain ⟨epsilon, hepsilon, hambientEpsilon⟩ :=
    a.heADC2025Theorem72_maximalProductAmbientSecond k d hdLt horder hmaximal
  obtain ⟨i, s, _hsUnit, hepsilonFactor⟩ :=
    hU.complete epsilon hepsilon
  have hnormalize :=
    BONG.GoodBONG.heADC2025Theorem72_secondOddIsometric_of_mul_square
      k epsilon (U i) s hepsilonFactor
  have hambientUnit : X.form.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) (U i))) :=
    ⟨(Classical.choice hambientEpsilon).trans
      (Classical.choice hnormalize).toQuadraticSpaceIsometry⟩
  have hambientIndex : ambientIndex (K := K) x = .inr (i, false) := by
    let P := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := k + 1) (ambientIndex (K := K) x)
    let Q := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := k + 1) (.inr (i, false))
    letI : AddCommGroup P.Carrier := P.addCommGroup
    letI : Module K P.Carrier := P.module
    letI : AddCommGroup Q.Carrier := Q.addCommGroup
    letI : Module K Q.Carrier := Q.module
    apply Lattice.QuadraticLatticeModel.heHuPublishedOdd_model_eq_of_ambientlyIsometric
      U hU
    change P.form.IsIsometric Q.form
    dsimp only [P, Q]
    rw [publishedModel_form_eq (K := K) U (k + 1),
      publishedModel_form_eq (K := K) U (k + 1)]
    exact ⟨(Classical.choice A.ambient).symm.trans
      (Classical.choice hambientUnit)⟩
  have hiOrder : ordUnit K (U i) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)
  let b := heADCMaximalGoodBONG (heADCW2Odd (K := K) (k + 1) (U i))
  have B := BONG.GoodBONG.heADC2025Lemma720ii k (U i) hiOrder
  have hisometric : Lattice.IsIsometric X.form
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) (U i)))
      X.lattice (heADCN2Odd (k + 1) (U i)).lattice :=
    Lattice.oMaximal_isIsometric_of_isometric hmaximal
      (heHuOMaximalLattice_isOMaximal (heADCW2Odd (k + 1) (U i)))
        hambientUnit
  have hclass := (a.heADC2025Lemma715 k b A.nADC B.nADC).mp hisometric
  have hrow : row (K := K) x = ramificationIndex K - 1 := by
    rw [A.penultimate, B.penultimate] at hclass
    omega
  exact ⟨hrow, i, hambientIndex⟩

/-- Every index in the right summand denotes a genuinely nonmaximal lattice. -/
theorem model_not_isOMaximal_of_nonmaximalIndex
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (m : HeADC2025Corollary721NonmaximalIndex K I) :
    ¬ (model U hU k (.inr m)).IsOMaximal := by
  intro hmaximal
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  rcases m with early | last
  · have hrowLt : row (K := K)
        (.inr (.inl early) : HeADC2025Corollary721Index K I) <
        ramificationIndex K := by
      exact early.1.isLt.trans_le (Nat.sub_le _ _)
    have H := lower_maximal_index_characterization U hU k
      (.inr (.inl early) : HeADC2025Corollary721Index K I)
        hrowLt hmaximal
    simp only [row] at H
    exact (not_lt_of_ge H.1.ge) early.1.isLt
  · have hrowLt : row (K := K)
        (.inr (.inr last) : HeADC2025Corollary721Index K I) <
        ramificationIndex K := by
      simp only [row]
      omega
    obtain ⟨_hrow, i, hambient⟩ := lower_maximal_index_characterization
      U hU k (.inr (.inr last) : HeADC2025Corollary721Index K I)
        hrowLt hmaximal
    rcases last with p | j
    · simp [ambientIndex] at hambient
    · simp [ambientIndex] at hambient

/-- Maximality is exactly membership in the left summand of the catalogue. -/
theorem model_isOMaximal_iff
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (x : HeADC2025Corollary721Index K I) :
    (model U hU k x).IsOMaximal ↔
      ∃ m : HeADC2025Corollary721MaximalIndex I, x = .inl m := by
  rcases x with m | m
  · exact ⟨fun _ ↦ ⟨m, rfl⟩,
      fun _ ↦ model_isOMaximal_of_maximalIndex U hU k m⟩
  · constructor
    · exact fun h ↦ (model_not_isOMaximal_of_nonmaximalIndex U hU k m h).elim
    · rintro ⟨m', h⟩
      cases h

/-- A finite family is an exact catalogue of the odd-corank-two `n`-ADC
isometry classes when it has the right rank, consists of `n`-ADC lattices,
is complete, and has no repeated integral-isometry class. -/
structure IsExactNADCIsometryCatalogue
    {J : Type u} (k : Nat)
    (family : J -> Lattice.QuadraticLatticeModel (K := K)) : Prop where
  rank (j : J) : (family j).rank = 2 * k + 5
  nADC (j : J) : (family j).IsNADC (2 * k + 3)
  complete (X : Lattice.QuadraticLatticeModel (K := K)) :
    X.rank = 2 * k + 5 -> X.IsNADC (2 * k + 3) ->
      ∃ j : J, IsIntegrallyIsometric X (family j)
  irredundant {i j : J} :
    IsIntegrallyIsometric (family i) (family j) -> i = j

/-- The chosen family is a complete and irredundant set of representatives,
which is the formal meaning of the phrase "up to isometry" in Corollary
7.21. -/
theorem isExactNADCIsometryCatalogue
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    IsExactNADCIsometryCatalogue k (model U hU k) :=
  { rank := model_rank U hU k
    nADC := model_isNADC U hU k
    complete := exists_index_isIntegrallyIsometric U hU k
    irredundant := model_eq_of_isIntegrallyIsometric U hU k }

/-- The four maximal rows in Corollary 7.21: three from Lemma 7.20(i) and
one from Lemma 7.20(ii). -/
theorem card_maximalIndex :
    Fintype.card (HeADC2025Corollary721MaximalIndex I) =
      4 * Fintype.card I := by
  simp [HeADC2025Corollary721MaximalIndex,
    HeADC2025Corollary721TopIndex, HeHuPublishedSquareClassIndex]
  ring

/-- The `(4e-1)|U|` indices left after the maximal overlap is removed from
the `4e|U|` lower rows. -/
theorem card_nonmaximalIndex :
    Fintype.card (HeADC2025Corollary721NonmaximalIndex K I) =
      (4 * ramificationIndex K - 1) * Fintype.card I := by
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  have hcoefficient :
      4 * (ramificationIndex K - 1) + 3 =
        4 * ramificationIndex K - 1 := by
    omega
  simp only [HeADC2025Corollary721NonmaximalIndex,
    HeADC2025Corollary721LastNonmaximalIndex,
    HeHuPublishedOddTestingIndex, HeHuPublishedSquareClassIndex,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  calc
    (ramificationIndex K - 1) *
          (Fintype.card I * 2 + Fintype.card I * 2) +
        (Fintype.card I * 2 + Fintype.card I) =
        (4 * (ramificationIndex K - 1) + 3) * Fintype.card I := by ring
    _ = (4 * ramificationIndex K - 1) * Fintype.card I := by
      rw [hcoefficient]

/-- The complete catalogue has `(4e+3)|U|` indices. -/
theorem card_index :
    Fintype.card (HeADC2025Corollary721Index K I) =
      (4 * ramificationIndex K + 3) * Fintype.card I := by
  rw [Fintype.card_sum, card_maximalIndex,
    card_nonmaximalIndex (K := K)]
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  have hcoefficient :
      4 + (4 * ramificationIndex K - 1) =
        4 * ramificationIndex K + 3 := by
    omega
  calc
    4 * Fintype.card I +
        (4 * ramificationIndex K - 1) * Fintype.card I =
      (4 + (4 * ramificationIndex K - 1)) * Fintype.card I := by ring
    _ = (4 * ramificationIndex K + 3) * Fintype.card I := by
      rw [hcoefficient]

/-- The four maximal rows contribute `8 * (N p)^e` classes after applying
the proved unit square-class count of O'Meara 63:9. -/
theorem card_maximalIndex_published
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeADC2025Corollary721MaximalIndex I) =
      8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_maximalIndex,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

/-- The nonmaximal rows contribute `(8e-2) * (N p)^e` classes. -/
theorem card_nonmaximalIndex_published
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeADC2025Corollary721NonmaximalIndex K I) =
      (8 * ramificationIndex K - 2) *
        heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_nonmaximalIndex,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  have hcoefficient :
      2 * (4 * ramificationIndex K - 1) =
        8 * ramificationIndex K - 2 := by
    omega
  calc
    (4 * ramificationIndex K - 1) *
          (2 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K) =
        (2 * (4 * ramificationIndex K - 1)) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by ring
    _ = (8 * ramificationIndex K - 2) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
      rw [hcoefficient]

/-- The complete catalogue contains `(8e+6) * (N p)^e` classes. -/
theorem card_index_published
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeADC2025Corollary721Index K I) =
      (8 * ramificationIndex K + 6) *
        heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_index,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

/-- Corollary 7.21: the displayed family is the exact isometry catalogue,
maximality is precisely its left summand, and the total and nonmaximal counts
are the two numerical formulas printed in the paper. -/
theorem heADC2025Corollary721
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    IsExactNADCIsometryCatalogue k (model U hU k) ∧
      (∀ x : HeADC2025Corollary721Index K I,
        (model U hU k x).IsOMaximal ↔
          ∃ m : HeADC2025Corollary721MaximalIndex I, x = .inl m) ∧
      Fintype.card (HeADC2025Corollary721Index K I) =
        (8 * ramificationIndex K + 6) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K ∧
      Fintype.card (HeADC2025Corollary721NonmaximalIndex K I) =
        (8 * ramificationIndex K - 2) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  exact ⟨isExactNADCIsometryCatalogue U hU k,
    model_isOMaximal_iff U hU k,
    card_index_published U hU,
    card_nonmaximalIndex_published U hU⟩

end HeADC2025Corollary721Index

end Bong
