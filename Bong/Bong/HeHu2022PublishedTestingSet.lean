/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Theorem12
import Bong.Bong.HeHu2022Remark38
import Bong.Bong.BeliUniversalPreliminaries
import Bong.Bong.Beli2009FinalRemarksProof

/-!
# He--Hu (2024), finite representative-system form of Theorem 1.2

`HeHu2022Theorem12` proves the classification and minimality theorem with
the determinant square class allowed to range over all nonzero scalars.
This file supplies the finite presentation printed in the published paper:
a finite complete system `U` of unit square-class representatives, followed
by the two valuation parities `delta` and `delta*pi`.

The hypotheses on `U` say exactly that it is a complete system of
representatives for `O_F^times/O_F^{times 2}` and that its elements satisfy
the normalization in Remark 3.8.  No classification or universality fact is
included in the representative-system hypothesis.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The assumptions on the finite set `U` in Theorem 1.2, represented by a
finite indexing type.  `complete` is existence modulo a square of a
valuation unit; `irredundant` says that distinct indices give distinct unit
square classes. -/
structure IsHeHuCompleteUnitRepresentativeSystem
    {I : Type u} [Fintype I] (U : I -> Kˣ) : Prop where
  isUnit (i : I) : IsValuationUnit K (U i : K)
  normalized (i : I) :
    IsHeHuNormalizedUnitRepresentative (K := K) (U i) (U i)
  complete (epsilon : Kˣ) (hUnit : IsValuationUnit K (epsilon : K)) :
    exists i : I, exists s : Kˣ,
      IsValuationUnit K (s : K) ∧ epsilon = U i * s ^ 2
  irredundant {i j : I} : IsSquare (U i * U j) -> i = j

/-- The two representatives `delta` and `delta*pi` attached to an element
of the published unit representative system. -/
abbrev HeHuPublishedSquareClassIndex (I : Type u) := I × Bool

namespace HeHuPublishedSquareClassIndex

/-- The scalar represented by a row index: `U i` for `false` and
`U i * pi` for `true`. -/
noncomputable def parameter {I : Type u} (U : I -> Kˣ)
    (p : HeHuPublishedSquareClassIndex I) : Kˣ :=
  if p.2 then U p.1 * uniformizerPowerUnit K (1 : Int) else U p.1

@[simp] theorem parameter_unit {I : Type u} (U : I -> Kˣ) (i : I) :
    parameter (K := K) U (i, false) = U i := by
  simp [parameter]

@[simp] theorem parameter_uniformizer {I : Type u} (U : I -> Kˣ) (i : I) :
    parameter (K := K) U (i, true) =
      U i * uniformizerPowerUnit K (1 : Int) := by
  simp [parameter]

/-- Every field square class is represented by exactly one of the two
valuation-parity rows, at least at the existence level needed for the
testing theorem. -/
theorem exists_parameter_mul_square
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (c : Kˣ) :
    exists p : HeHuPublishedSquareClassIndex I, exists s : Kˣ,
      c = parameter (K := K) U p * s ^ 2 := by
  obtain ⟨b, z, hbOrder, hc⟩ :=
    exists_order_zero_or_one_mul_square_any (K := K) c
  rcases hbOrder with hbZero | hbOne
  · have hbUnit : IsValuationUnit K (b : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K b).2 hbZero
    obtain ⟨i, t, _htUnit, hbt⟩ := hU.complete b hbUnit
    refine ⟨(i, false), t * z, ?_⟩
    rw [hc, hbt, parameter_unit]
    simp only [pow_two]
    ac_rfl
  · let epsilon := normalizedUnitPart K b
    have hepsilonUnit : IsValuationUnit K (epsilon : K) := by
      simpa only [epsilon] using normalizedUnitPart_isValuationUnit K b
    obtain ⟨i, t, _htUnit, het⟩ := hU.complete epsilon hepsilonUnit
    have hbRecover :
        uniformizerPowerUnit K (1 : Int) * epsilon = b := by
      simpa only [epsilon, hbOne] using
        (uniformizerPower_mul_normalizedUnitPart K b)
    refine ⟨(i, true), t * z, ?_⟩
    rw [hc, ← hbRecover, het, parameter_uniformizer]
    simp only [pow_two]
    ac_rfl

end HeHuPublishedSquareClassIndex

/-- The finite even-dimensional Table 2 index.  The left summand is the
first column and the right summand is the defined part of the second
column; this removes exactly `N_2^2(1)` in the binary square class. -/
abbrev HeHuPublishedEvenTestingIndex {I : Type u} (U : I -> Kˣ)
    (pairs : Nat) :=
  HeHuPublishedSquareClassIndex I ⊕
    {p : HeHuPublishedSquareClassIndex I //
      HeHuEvenSecondDefined pairs
        (HeHuPublishedSquareClassIndex.parameter (K := K) U p)}

/-- The finite odd-dimensional Table 2 index, with both columns defined. -/
abbrev HeHuPublishedOddTestingIndex (I : Type u) :=
  HeHuPublishedSquareClassIndex I ⊕ HeHuPublishedSquareClassIndex I

/-- The even published table is a genuinely finite type.  The subtype in
the second summand needs no decidability assumption for this existence
instance. -/
noncomputable instance heHuPublishedEvenTestingIndexFintype
    {I : Type u} [Fintype I] (U : I -> Kˣ) (pairs : Nat) :
    Fintype (HeHuPublishedEvenTestingIndex (K := K) U pairs) :=
  Fintype.ofFinite _

/-- The odd published table contains four rows for each element of `U`:
two valuation parities in each of two columns. -/
theorem card_heHuPublishedOddTestingIndex
    (I : Type u) [Fintype I] :
    Fintype.card (HeHuPublishedOddTestingIndex I) =
      4 * Fintype.card I := by
  simp [HeHuPublishedOddTestingIndex, HeHuPublishedSquareClassIndex]
  omega

/-- In every even rank above two, both columns are defined, so the
published table again contains four rows for every element of `U`. -/
theorem card_heHuPublishedEvenTestingIndex_of_pos
    {I : Type u} [Fintype I] (U : I -> Kˣ) {pairs : Nat}
    (hpairs : 0 < pairs) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U pairs) =
      4 * Fintype.card I := by
  classical
  let P := HeHuPublishedSquareClassIndex I
  let e : HeHuPublishedEvenTestingIndex (K := K) U pairs ≃ P ⊕ P :=
    { toFun := fun x => match x with
        | .inl p => .inl p
        | .inr p => .inr p.1
      invFun := fun x => match x with
        | .inl p => .inl p
        | .inr p => .inr ⟨p, Or.inl hpairs⟩
      left_inv := by
        intro x
        cases x with
        | inl p => rfl
        | inr p => simp
      right_inv := by
        intro x
        cases x <;> rfl }
  rw [Fintype.card_congr e]
  simp [P, HeHuPublishedSquareClassIndex]
  omega

private theorem even_ordUnit_of_isSquare_published (a : Kˣ)
    (ha : IsSquare a) : Even (ordUnit K a) := by
  rcases ha with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

/-- A complete irredundant unit representative system has exactly one
square parameter among all `delta` and `delta*pi`: the unit-parity
representative of the trivial square class. -/
theorem existsUnique_isSquare_publishedParameter
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    ∃! p : HeHuPublishedSquareClassIndex I,
      IsSquare (HeHuPublishedSquareClassIndex.parameter (K := K) U p) := by
  have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
    simp [IsValuationUnit]
  obtain ⟨i, s, _hsUnit, his⟩ := hU.complete 1 honeUnit
  have hUiEq : U i = s⁻¹ ^ 2 := by
    calc
      U i = (U i * s ^ 2) * s⁻¹ ^ 2 := by group
      _ = s⁻¹ ^ 2 := by rw [← his]; simp
  have hUiSquare : IsSquare (U i) := by
    refine ⟨s⁻¹, ?_⟩
    simpa only [pow_two] using hUiEq
  refine ⟨(i, false), by simpa using hUiSquare, ?_⟩
  intro p hp
  rcases p with ⟨j, parity⟩
  cases parity with
  | false =>
      have hUjSquare : IsSquare (U j) := by
        simpa using hp
      have hji : j = i := hU.irredundant (hUjSquare.mul hUiSquare)
      subst j
      rfl
  | true =>
      have horder : ordUnit K
          (HeHuPublishedSquareClassIndex.parameter
            (K := K) U (j, true)) = 1 := by
        rw [HeHuPublishedSquareClassIndex.parameter_uniformizer,
          ordUnit_mul, ordUnit_uniformizerPowerUnit,
          (isValuationUnit_iff_ordUnit_eq_zero K (U j)).1 (hU.isUnit j)]
        norm_num
      have heven := even_ordUnit_of_isSquare_published
        (HeHuPublishedSquareClassIndex.parameter
          (K := K) U (j, true)) hp
      rw [horder] at heven
      rcases heven with ⟨z, hz⟩
      omega

/-- In rank two, precisely the second-column trivial square-class row is
undefined, so Table 2 has `4*|U|-1` entries. -/
theorem card_heHuPublishedEvenTestingIndex_zero
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U 0) =
      4 * Fintype.card I - 1 := by
  classical
  let P := HeHuPublishedSquareClassIndex I
  let squarePred : P -> Prop := fun p =>
    IsSquare (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
  letI : Fintype {p : P // squarePred p} := Fintype.ofFinite _
  letI : Fintype {p : P // ¬ squarePred p} := Fintype.ofFinite _
  let e : HeHuPublishedEvenTestingIndex (K := K) U 0 ≃
      P ⊕ {p : P // ¬ squarePred p} :=
    { toFun := fun x => match x with
        | .inl p => .inl p
        | .inr p => .inr ⟨p.1, by
            dsimp only [squarePred]
            exact p.2.resolve_left (by omega)⟩
      invFun := fun x => match x with
        | .inl p => .inl p
        | .inr p => .inr ⟨p.1, by
            right
            simpa only [squarePred] using p.2⟩
      left_inv := by
        intro x
        cases x with
        | inl p => rfl
        | inr p => simp
      right_inv := by
        intro x
        cases x with
        | inl p => rfl
        | inr p => simp }
  have hsquareCard : Fintype.card {p : P // squarePred p} = 1 := by
    rw [Fintype.card_eq_one_iff]
    obtain ⟨p, hp, hpUnique⟩ :=
      existsUnique_isSquare_publishedParameter U hU
    refine ⟨⟨p, hp⟩, ?_⟩
    intro y
    apply Subtype.ext
    exact hpUnique y.1 y.2
  rw [Fintype.card_congr e, Fintype.card_sum,
    Fintype.card_subtype_compl squarePred, hsquareCard]
  simp [P, HeHuPublishedSquareClassIndex]
  omega

namespace HeHuPublishedEvenTestingIndex

/-- Forget that a Table 2 parameter came from the finite representative
system. -/
noncomputable def toGeneral {I : Type u} {U : I -> Kˣ} {pairs : Nat} :
    HeHuPublishedEvenTestingIndex (K := K) U pairs ->
      HeHuEvenTestingIndex (K := K) pairs
  | .inl p => .first
      (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
  | .inr p => .second
      (HeHuPublishedSquareClassIndex.parameter (K := K) U p.1) p.2

/-- The maximal lattice in the corresponding row of the published table. -/
noncomputable def model {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedEvenTestingIndex (K := K) U pairs) :
    Lattice.QuadraticLatticeModel (K := K) :=
  (toGeneral (K := K) i).model

@[simp] theorem model_rank {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedEvenTestingIndex (K := K) U pairs) :
    (model (K := K) i).rank = 2 * pairs + 2 :=
  HeHuEvenTestingIndex.model_rank _

theorem model_isOMaximal {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedEvenTestingIndex (K := K) U pairs) :
    (model (K := K) i).IsOMaximal :=
  HeHuEvenTestingIndex.model_isOMaximal _

end HeHuPublishedEvenTestingIndex

namespace HeHuPublishedOddTestingIndex

noncomputable def toGeneral {I : Type u} {U : I -> Kˣ} {pairs : Nat} :
    HeHuPublishedOddTestingIndex I -> HeHuOddTestingIndex (K := K) pairs
  | .inl p => .first
      (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
  | .inr p => .second
      (HeHuPublishedSquareClassIndex.parameter (K := K) U p)

noncomputable def model {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedOddTestingIndex I) :
    Lattice.QuadraticLatticeModel (K := K) :=
  (toGeneral (K := K) (U := U) (pairs := pairs) i).model

@[simp] theorem model_rank {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedOddTestingIndex I) :
    (model (K := K) (U := U) (pairs := pairs) i).rank = 2 * pairs + 3 :=
  HeHuOddTestingIndex.model_rank _

theorem model_isOMaximal {I : Type u} {U : I -> Kˣ} {pairs : Nat}
    (i : HeHuPublishedOddTestingIndex I) :
    (model (K := K) (U := U) (pairs := pairs) i).IsOMaximal :=
  HeHuOddTestingIndex.model_isOMaximal _

end HeHuPublishedOddTestingIndex

namespace Lattice.QuadraticLatticeModel

/-- Literal deletion-minimality: after removing any one index, some
integral witness still represents all remaining tests but misses that one.
For an irredundant representative system this is the paper's phrase "none
of its proper subsets is sufficient" without quotienting duplicate
presentations. -/
def IsLiteralMinimalUniversalityTestingFamily {J : Type u}
    (family : J -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  IsUniversalityTestingFamily family n ∧
    ∀ i, ∃ M : QuadraticLatticeModel (K := K),
      M.IsIntegral ∧ ¬ M.Represents (family i) ∧
        ∀ j, j ≠ i -> M.Represents (family j)

theorem heHuBinaryFirst_represents_of_mul_square
    (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuBinaryFirst c))
      (diagonalUnitCoefficients (heHuBinaryFirst d)) := by
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heHuBinaryFirst c) (heHuBinaryFirst d) ![1, s]
  intro i
  fin_cases i
  · simp [heHuBinaryFirst]
  · simp [heHuBinaryFirst, h]

theorem heHuOddFirstTail_represents_of_mul_square
    (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirstTail c))
      (diagonalUnitCoefficients (heHuOddFirstTail d)) := by
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heHuOddFirstTail c) (heHuOddFirstTail d) ![1, 1, s]
  intro i
  fin_cases i
  · simp [heHuOddFirstTail]
  · simp [heHuOddFirstTail]
  · simp [heHuOddFirstTail, h]

theorem heHuEvenFirst_represents_of_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenFirst pairs c))
      (diagonalUnitCoefficients (heHuEvenFirst pairs d)) := by
  cases pairs with
  | zero =>
      simpa [heHuEvenFirst] using
        heHuBinaryFirst_represents_of_mul_square c d s h
  | succ pairs =>
      have hbinary := heHuBinaryFirst_represents_of_mul_square c d s h
      have hpair : DiagonalRepresents
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) :=
        diagonalRepresents_refl _
      have htail : DiagonalRepresents
          (diagonalUnitCoefficients (heHuEvenFirstTail c))
          (diagonalUnitCoefficients (heHuEvenFirstTail d)) := by
        simpa only [heHuEvenFirstTail,
          diagonalUnitCoefficients_append] using
          DiagonalRepresents.appendBoth hpair hbinary
      have hhead : DiagonalRepresents
          (diagonalUnitCoefficients
            (standardHyperbolicEndpointTower (K := K) pairs))
          (diagonalUnitCoefficients
            (standardHyperbolicEndpointTower (K := K) pairs)) :=
        diagonalRepresents_refl _
      have hfull := DiagonalRepresents.appendBoth hhead htail
      apply (diagonalRepresents_heHuFinFamilyCast_iff
        (by omega : 2 * pairs + 4 = 2 * (pairs + 1) + 2)
        (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuEvenFirstTail c))
        (Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuEvenFirstTail d))).2
      simpa only [diagonalUnitCoefficients_append] using hfull

theorem heHuOddFirst_represents_of_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst pairs c))
      (diagonalUnitCoefficients (heHuOddFirst pairs d)) := by
  have hhead : DiagonalRepresents
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) pairs))
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) pairs)) :=
    diagonalRepresents_refl _
  have htail := heHuOddFirstTail_represents_of_mul_square c d s h
  simpa only [heHuOddFirst, diagonalUnitCoefficients_append] using
    DiagonalRepresents.appendBoth hhead htail

/-- In a fixed determinant square class, the non-first member of a
two-class package is unique. -/
theorem HeHuSpacePairProperties.second_represents_second
    {n : Nat} {firstC secondC firstD secondD : Fin n -> Kˣ}
    (PC : HeHuSpacePairProperties firstC secondC)
    (PD : HeHuSpacePairProperties firstD secondD)
    (hfirst : DiagonalRepresents
      (diagonalUnitCoefficients firstC)
      (diagonalUnitCoefficients firstD)) :
    DiagonalRepresents
      (diagonalUnitCoefficients secondC)
      (diagonalUnitCoefficients secondD) := by
  have hfirstDet :=
    DiagonalIsometryInvariantLaws.determinant_square firstC firstD hfirst
  have hsecondDet : IsSquare
      (diagonalUnitDeterminant secondC *
        diagonalUnitDeterminant firstD) :=
    isSquare_mul_trans
      (diagonalUnitDeterminant secondC)
      (diagonalUnitDeterminant firstC)
      (diagonalUnitDeterminant firstD)
      PC.determinantSquare hfirstDet
  rcases PD.exhaustive secondC hsecondDet with htoFirst | htoSecond
  · exact False.elim <| PC.nonisometric <|
      htoFirst.trans hfirst.symm_of_sameRank
  · exact htoSecond

theorem heHuEvenSecondDefined_of_mul_square
    {pairs : Nat} {c d s : Kˣ}
    (hc : HeHuEvenSecondDefined pairs c) (h : c = d * s ^ 2) :
    HeHuEvenSecondDefined pairs d := by
  cases pairs with
  | zero =>
      right
      intro hd
      apply hc.resolve_left (by omega)
      rw [h]
      exact hd.mul ⟨s, pow_two s⟩
  | succ pairs => exact Or.inl (by omega)

theorem heHuEvenSecond_represents_of_mul_square
    (pairs : Nat) (c d s : Kˣ)
    (hc : HeHuEvenSecondDefined pairs c) (h : c = d * s ^ 2) :
    let hd := heHuEvenSecondDefined_of_mul_square hc h
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenSecond pairs c hc))
      (diagonalUnitCoefficients (heHuEvenSecond pairs d hd)) := by
  dsimp only
  apply HeHuSpacePairProperties.second_represents_second
    (heHu2022Definition34Proposition35Even pairs c hc)
    (heHu2022Definition34Proposition35Even pairs d
      (heHuEvenSecondDefined_of_mul_square hc h))
  exact heHuEvenFirst_represents_of_mul_square pairs c d s h

theorem heHuOddSecond_represents_of_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond pairs c))
      (diagonalUnitCoefficients (heHuOddSecond pairs d)) := by
  apply HeHuSpacePairProperties.second_represents_second
    (heHu2022Definition34Proposition35Odd pairs c)
    (heHu2022Definition34Proposition35Odd pairs d)
  exact heHuOddFirst_represents_of_mul_square pairs c d s h

private def evenGeneralParameter {pairs : Nat} :
    HeHuEvenTestingIndex (K := K) pairs -> Kˣ
  | .first c => c
  | .second c _ => c

private def oddGeneralParameter {pairs : Nat} :
    HeHuOddTestingIndex (K := K) pairs -> Kˣ
  | .first c => c
  | .second c => c

private theorem evenGeneral_determinantSquare_first {pairs : Nat}
    (i : HeHuEvenTestingIndex (K := K) pairs) :
    IsSquare
      (diagonalUnitDeterminant i.coefficients *
        diagonalUnitDeterminant
          (heHuEvenFirst pairs (evenGeneralParameter i))) := by
  cases i with
  | first c =>
      change IsSquare
        (diagonalUnitDeterminant (heHuEvenFirst pairs c) *
          diagonalUnitDeterminant (heHuEvenFirst pairs c))
      exact ⟨diagonalUnitDeterminant (heHuEvenFirst pairs c), rfl⟩
  | second c hc =>
      exact (heHu2022Definition34Proposition35Even pairs c hc).determinantSquare

private theorem oddGeneral_determinantSquare_first {pairs : Nat}
    (i : HeHuOddTestingIndex (K := K) pairs) :
    IsSquare
      (diagonalUnitDeterminant i.coefficients *
        diagonalUnitDeterminant
          (heHuOddFirst pairs (oddGeneralParameter i))) := by
  cases i with
  | first c =>
      change IsSquare
        (diagonalUnitDeterminant (heHuOddFirst pairs c) *
          diagonalUnitDeterminant (heHuOddFirst pairs c))
      exact ⟨diagonalUnitDeterminant (heHuOddFirst pairs c), rfl⟩
  | second c =>
      exact (heHu2022Definition34Proposition35Odd pairs c).determinantSquare

private theorem evenGeneral_parametersSquare_of_represents {pairs : Nat}
    (i j : HeHuEvenTestingIndex (K := K) pairs)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients i.coefficients)
      (diagonalUnitCoefficients j.coefficients)) :
    IsSquare (evenGeneralParameter i * evenGeneralParameter j) := by
  have hij :=
    DiagonalIsometryInvariantLaws.determinant_square
      i.coefficients j.coefficients hrep
  have hi := evenGeneral_determinantSquare_first i
  have hj := evenGeneral_determinantSquare_first j
  have hfirstIToJ : IsSquare
      (diagonalUnitDeterminant
          (heHuEvenFirst pairs (evenGeneralParameter i)) *
        diagonalUnitDeterminant j.coefficients) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant i.coefficients) _
      (by simpa only [mul_comm] using hi) hij
  have hfirstBoth : IsSquare
      (diagonalUnitDeterminant
          (heHuEvenFirst pairs (evenGeneralParameter i)) *
        diagonalUnitDeterminant
          (heHuEvenFirst pairs (evenGeneralParameter j))) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant j.coefficients) _
      hfirstIToJ hj
  rw [diagonalUnitDeterminant_heHuEvenFirst,
    diagonalUnitDeterminant_heHuEvenFirst] at hfirstBoth
  let sign : Kˣ := (-1 : Kˣ) ^ (pairs + 1)
  have hsign : IsSquare (sign ^ 2) := ⟨sign, pow_two sign⟩
  have hquot := hfirstBoth.div hsign
  have heq :
      ((sign * evenGeneralParameter i) *
        (sign * evenGeneralParameter j)) / sign ^ 2 =
          evenGeneralParameter i * evenGeneralParameter j := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign]
  rw [heq] at hquot
  exact hquot

private theorem oddGeneral_parametersSquare_of_represents {pairs : Nat}
    (i j : HeHuOddTestingIndex (K := K) pairs)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients i.coefficients)
      (diagonalUnitCoefficients j.coefficients)) :
    IsSquare (oddGeneralParameter i * oddGeneralParameter j) := by
  have hij :=
    DiagonalIsometryInvariantLaws.determinant_square
      i.coefficients j.coefficients hrep
  have hi := oddGeneral_determinantSquare_first i
  have hj := oddGeneral_determinantSquare_first j
  have hfirstIToJ : IsSquare
      (diagonalUnitDeterminant
          (heHuOddFirst pairs (oddGeneralParameter i)) *
        diagonalUnitDeterminant j.coefficients) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant i.coefficients) _
      (by simpa only [mul_comm] using hi) hij
  have hfirstBoth : IsSquare
      (diagonalUnitDeterminant
          (heHuOddFirst pairs (oddGeneralParameter i)) *
        diagonalUnitDeterminant
          (heHuOddFirst pairs (oddGeneralParameter j))) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant j.coefficients) _
      hfirstIToJ hj
  rw [diagonalUnitDeterminant_heHuOddFirst,
    diagonalUnitDeterminant_heHuOddFirst] at hfirstBoth
  let sign : Kˣ := (-1 : Kˣ) ^ (pairs + 1)
  have hsign : IsSquare (sign ^ 2) := ⟨sign, pow_two sign⟩
  have hquot := hfirstBoth.div hsign
  have heq :
      ((sign * oddGeneralParameter i) *
        (sign * oddGeneralParameter j)) / sign ^ 2 =
          oddGeneralParameter i * oddGeneralParameter j := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign]
  rw [heq] at hquot
  exact hquot

private theorem diagonalRepresents_of_heHuOMaximalModel_ambientlyIsometric
    {n : Nat} (a b : Fin n -> Kˣ)
    (h : (heHuOMaximalModel a).IsAmbientlyIsometric
      (heHuOMaximalModel b)) :
    DiagonalRepresents (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b) := by
  let A := heHuOMaximalModel a
  let B := heHuOMaximalModel b
  letI : AddCommGroup A.Carrier := A.addCommGroup
  letI : Module K A.Carrier := A.module
  letI : AddCommGroup B.Carrier := B.addCommGroup
  letI : Module K B.Carrier := B.module
  rcases h with ⟨f⟩
  have hBA : B.Represents A := by
    apply ((heHuOMaximalModel_isOMaximal b).represents_iff_ambient
      (heHuOMaximalModel_isOMaximal a)).2
    exact ⟨f.toRepresentation⟩
  exact (heHuOMaximalModel_represents_iff b a).mp hBA

private theorem publishedParameter_eq_of_square
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {p q : HeHuPublishedSquareClassIndex I}
    (hpq : IsSquare
      (HeHuPublishedSquareClassIndex.parameter (K := K) U p *
        HeHuPublishedSquareClassIndex.parameter (K := K) U q)) :
    p = q := by
  rcases p with ⟨i, piParity⟩
  rcases q with ⟨j, pjParity⟩
  cases piParity <;> cases pjParity
  · have hij : i = j := hU.irredundant (by simpa using hpq)
    subst j
    rfl
  · have horder : ordUnit K
        (HeHuPublishedSquareClassIndex.parameter (K := K) U (i, false) *
          HeHuPublishedSquareClassIndex.parameter (K := K) U (j, true)) = 1 := by
      rw [HeHuPublishedSquareClassIndex.parameter_unit,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        ordUnit_mul, ordUnit_mul, ordUnit_uniformizerPowerUnit,
        (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i),
        (isValuationUnit_iff_ordUnit_eq_zero K (U j)).1 (hU.isUnit j)]
      norm_num
    have heven := even_ordUnit_of_isSquare_published _ hpq
    rw [horder] at heven
    rcases heven with ⟨z, hz⟩
    omega
  · have horder : ordUnit K
        (HeHuPublishedSquareClassIndex.parameter (K := K) U (i, true) *
          HeHuPublishedSquareClassIndex.parameter (K := K) U (j, false)) = 1 := by
      rw [HeHuPublishedSquareClassIndex.parameter_unit,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        ordUnit_mul, ordUnit_mul, ordUnit_uniformizerPowerUnit,
        (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i),
        (isValuationUnit_iff_ordUnit_eq_zero K (U j)).1 (hU.isUnit j)]
      norm_num
    have heven := even_ordUnit_of_isSquare_published _ hpq
    rw [horder] at heven
    rcases heven with ⟨z, hz⟩
    omega
  · let uniformizer := uniformizerPowerUnit K (1 : Int)
    have hpiSquare : IsSquare (uniformizer ^ 2) :=
      ⟨uniformizer, pow_two uniformizer⟩
    have hunitProduct : IsSquare (U i * U j) := by
      have hquot := hpq.div hpiSquare
      have heq :
          ((U i * uniformizer) * (U j * uniformizer)) /
              uniformizer ^ 2 = U i * U j := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero uniformizer]
      simpa only [HeHuPublishedSquareClassIndex.parameter_uniformizer,
        uniformizer, heq] using hquot
    have hij : i = j := hU.irredundant hunitProduct
    subst j
    rfl

/-- Distinct indices in the published even table give distinct ambient
isometry classes. -/
theorem heHuPublishedEven_model_eq_of_ambientlyIsometric
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat} {i j : HeHuPublishedEvenTestingIndex (K := K) U pairs}
    (hiso : (HeHuPublishedEvenTestingIndex.model (K := K) i).IsAmbientlyIsometric
      (HeHuPublishedEvenTestingIndex.model (K := K) j)) :
    i = j := by
  let gi := HeHuPublishedEvenTestingIndex.toGeneral (K := K) i
  let gj := HeHuPublishedEvenTestingIndex.toGeneral (K := K) j
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients gi.coefficients)
      (diagonalUnitCoefficients gj.coefficients) := by
    apply diagonalRepresents_of_heHuOMaximalModel_ambientlyIsometric
    simpa only [gi, gj, HeHuPublishedEvenTestingIndex.model,
      HeHuEvenTestingIndex.model] using hiso
  have hparameter := evenGeneral_parametersSquare_of_represents gi gj hdiag
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          have hpq : p = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          rfl
      | inr q =>
          have hpq : p = q.1 := publishedParameter_eq_of_square U hU hparameter
          subst p
          exact False.elim <|
            (heHu2022Definition34Proposition35Even pairs
              (HeHuPublishedSquareClassIndex.parameter (K := K) U q.1) q.2).nonisometric
              hdiag.symm_of_sameRank
  | inr p =>
      cases j with
      | inl q =>
          have hpq : p.1 = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          exact False.elim <|
            (heHu2022Definition34Proposition35Even pairs
              (HeHuPublishedSquareClassIndex.parameter (K := K) U p.1) p.2).nonisometric
              hdiag
      | inr q =>
          have hpq : p.1 = q.1 := publishedParameter_eq_of_square U hU hparameter
          have hpqSubtype : p = q := Subtype.ext hpq
          subst q
          rfl

/-- Distinct indices in the published odd table give distinct ambient
isometry classes. -/
theorem heHuPublishedOdd_model_eq_of_ambientlyIsometric
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat} {i j : HeHuPublishedOddTestingIndex I}
    (hiso : (HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) i).IsAmbientlyIsometric
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) j)) :
    i = j := by
  let gi := HeHuPublishedOddTestingIndex.toGeneral
    (K := K) (U := U) (pairs := pairs) i
  let gj := HeHuPublishedOddTestingIndex.toGeneral
    (K := K) (U := U) (pairs := pairs) j
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients gi.coefficients)
      (diagonalUnitCoefficients gj.coefficients) := by
    apply diagonalRepresents_of_heHuOMaximalModel_ambientlyIsometric
    simpa only [gi, gj, HeHuPublishedOddTestingIndex.model,
      HeHuOddTestingIndex.model] using hiso
  have hparameter := oddGeneral_parametersSquare_of_represents gi gj hdiag
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          have hpq : p = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          rfl
      | inr q =>
          have hpq : p = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          exact False.elim <|
            (heHu2022Definition34Proposition35Odd pairs
              (HeHuPublishedSquareClassIndex.parameter (K := K) U p)).nonisometric
              hdiag.symm_of_sameRank
  | inr p =>
      cases j with
      | inl q =>
          have hpq : p = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          exact False.elim <|
            (heHu2022Definition34Proposition35Odd pairs
              (HeHuPublishedSquareClassIndex.parameter (K := K) U p)).nonisometric
              hdiag
      | inr q =>
          have hpq : p = q := publishedParameter_eq_of_square U hU hparameter
          subst q
          rfl

/-- Every general even Table 1 presentation is isometric to a row whose
parameter is literally `delta` or `delta*pi` with `delta` in `U`. -/
theorem exists_publishedEvenIndex_ambientlyIsometric
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (i : HeHuEvenTestingIndex (K := K) pairs) :
    exists j : HeHuPublishedEvenTestingIndex (K := K) U pairs,
      i.model.IsAmbientlyIsometric
        (HeHuPublishedEvenTestingIndex.model (K := K) j) := by
  cases i with
  | first c =>
      obtain ⟨p, s, hfactor⟩ :=
        HeHuPublishedSquareClassIndex.exists_parameter_mul_square
          U hU c
      let j : HeHuPublishedEvenTestingIndex (K := K) U pairs := .inl p
      refine ⟨j, ?_⟩
      apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      simpa only [j, HeHuPublishedEvenTestingIndex.model,
        HeHuPublishedEvenTestingIndex.toGeneral,
        HeHuEvenTestingIndex.coefficients] using
        heHuEvenFirst_represents_of_mul_square pairs c
          (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
          s hfactor
  | second c hc =>
      obtain ⟨p, s, hfactor⟩ :=
        HeHuPublishedSquareClassIndex.exists_parameter_mul_square
          U hU c
      have hp := heHuEvenSecondDefined_of_mul_square hc hfactor
      let j : HeHuPublishedEvenTestingIndex (K := K) U pairs :=
        .inr ⟨p, hp⟩
      refine ⟨j, ?_⟩
      apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      simpa only [j, HeHuPublishedEvenTestingIndex.model,
        HeHuPublishedEvenTestingIndex.toGeneral,
        HeHuEvenTestingIndex.coefficients] using
        heHuEvenSecond_represents_of_mul_square pairs c
          (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
          s hc hfactor

/-- Every general odd Table 1 presentation is isometric to a row whose
parameter is literally `delta` or `delta*pi` with `delta` in `U`. -/
theorem exists_publishedOddIndex_ambientlyIsometric
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (i : HeHuOddTestingIndex (K := K) pairs) :
    exists j : HeHuPublishedOddTestingIndex I,
      i.model.IsAmbientlyIsometric
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := pairs) j) := by
  cases i with
  | first c =>
      obtain ⟨p, s, hfactor⟩ :=
        HeHuPublishedSquareClassIndex.exists_parameter_mul_square U hU c
      let j : HeHuPublishedOddTestingIndex I := .inl p
      refine ⟨j, ?_⟩
      apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      simpa only [j, HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.coefficients] using
        heHuOddFirst_represents_of_mul_square pairs c
          (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
          s hfactor
  | second c =>
      obtain ⟨p, s, hfactor⟩ :=
        HeHuPublishedSquareClassIndex.exists_parameter_mul_square U hU c
      let j : HeHuPublishedOddTestingIndex I := .inr p
      refine ⟨j, ?_⟩
      apply heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      simpa only [j, HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.coefficients] using
        heHuOddSecond_represents_of_mul_square pairs c
          (HeHuPublishedSquareClassIndex.parameter (K := K) U p)
          s hfactor

/-- The published finite even table is complete on ambient quadratic
spaces of the required rank. -/
theorem exists_publishedEvenIndex_for_model
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hRank : X.rank = 2 * pairs + 2) :
    exists j : HeHuPublishedEvenTestingIndex (K := K) U pairs,
      X.IsAmbientlyIsometric
        (HeHuPublishedEvenTestingIndex.model (K := K) j) := by
  obtain ⟨i, hXi⟩ := exists_evenTestingIndex_ambientlyIsometric pairs X hRank
  obtain ⟨j, hij⟩ :=
    exists_publishedEvenIndex_ambientlyIsometric U hU pairs i
  exact ⟨j, hXi.trans hij⟩

/-- The published finite odd table is complete on ambient quadratic
spaces of the required rank. -/
theorem exists_publishedOddIndex_for_model
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hRank : X.rank = 2 * pairs + 3) :
    exists j : HeHuPublishedOddTestingIndex I,
      X.IsAmbientlyIsometric
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := pairs) j) := by
  obtain ⟨i, hXi⟩ := exists_oddTestingIndex_ambientlyIsometric pairs X hRank
  obtain ⟨j, hij⟩ :=
    exists_publishedOddIndex_ambientlyIsometric U hU pairs i
  exact ⟨j, hXi.trans hij⟩

/-- He--Hu, Theorem 1.2(i), in the literal finite representative-system
form printed in the published paper. -/
theorem heHu2022Theorem12PublishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    IsMinimalUniversalityTestingFamily
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := pairs))
      (2 * pairs + 2) := by
  refine ⟨completeMaximalFamily_isUniversalityTestingFamily _ _
    HeHuPublishedEvenTestingIndex.model_isOMaximal
    (exists_publishedEvenIndex_for_model U hU pairs), ?_⟩
  intro i
  let gi := HeHuPublishedEvenTestingIndex.toGeneral (K := K) i
  let W := heHuOMaximalModel gi.excludingTarget
  letI : AddCommGroup W.Carrier := W.addCommGroup
  letI : Module K W.Carrier := W.module
  have hWmaximal : W.IsOMaximal :=
    heHuOMaximalModel_isOMaximal gi.excludingTarget
  refine ⟨W, hWmaximal.isIntegral, ?_, ?_⟩
  · intro hrep
    apply gi.excludingTarget_exact.misses
    apply (heHuOMaximalModel_represents_iff
      gi.excludingTarget gi.coefficients).mp
    simpa only [W, gi, HeHuPublishedEvenTestingIndex.model,
      HeHuEvenTestingIndex.model] using hrep
  · intro j hnotIso
    let gj := HeHuPublishedEvenTestingIndex.toGeneral (K := K) j
    have hdiag : DiagonalRepresents
        (diagonalUnitCoefficients gj.coefficients)
        (diagonalUnitCoefficients gi.excludingTarget) := by
      apply gi.excludingTarget_exact.represents_other
      intro hji
      apply hnotIso
      simpa only [HeHuPublishedEvenTestingIndex.model,
        HeHuEvenTestingIndex.model, gi, gj] using
        heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
          gj.coefficients gi.coefficients hji
    have hrep := (heHuOMaximalModel_represents_iff
      gi.excludingTarget gj.coefficients).mpr hdiag
    simpa only [W, gi, gj, HeHuPublishedEvenTestingIndex.model,
      HeHuEvenTestingIndex.model] using hrep

/-- He--Hu, Theorem 1.2(ii), in the literal finite representative-system
form printed in the published paper. -/
theorem heHu2022Theorem12PublishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    IsMinimalUniversalityTestingFamily
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs))
      (2 * pairs + 3) := by
  refine ⟨completeMaximalFamily_isUniversalityTestingFamily _ _
    HeHuPublishedOddTestingIndex.model_isOMaximal
    (exists_publishedOddIndex_for_model U hU pairs), ?_⟩
  intro i
  let gi := HeHuPublishedOddTestingIndex.toGeneral
    (K := K) (U := U) (pairs := pairs) i
  let W := heHuOMaximalModel gi.excludingTarget
  letI : AddCommGroup W.Carrier := W.addCommGroup
  letI : Module K W.Carrier := W.module
  have hWmaximal : W.IsOMaximal :=
    heHuOMaximalModel_isOMaximal gi.excludingTarget
  refine ⟨W, hWmaximal.isIntegral, ?_, ?_⟩
  · intro hrep
    apply gi.excludingTarget_exact.misses
    apply (heHuOMaximalModel_represents_iff
      gi.excludingTarget gi.coefficients).mp
    simpa only [W, gi, HeHuPublishedOddTestingIndex.model,
      HeHuOddTestingIndex.model] using hrep
  · intro j hnotIso
    let gj := HeHuPublishedOddTestingIndex.toGeneral
      (K := K) (U := U) (pairs := pairs) j
    have hdiag : DiagonalRepresents
        (diagonalUnitCoefficients gj.coefficients)
        (diagonalUnitCoefficients gi.excludingTarget) := by
      apply gi.excludingTarget_exact.represents_other
      intro hji
      apply hnotIso
      simpa only [HeHuPublishedOddTestingIndex.model,
        HeHuOddTestingIndex.model, gi, gj] using
        heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
          gj.coefficients gi.coefficients hji
    have hrep := (heHuOMaximalModel_represents_iff
      gi.excludingTarget gj.coefficients).mpr hdiag
    simpa only [W, gi, gj, HeHuPublishedOddTestingIndex.model,
      HeHuOddTestingIndex.model] using hrep

/-- The literal deletion-minimal form of Theorem 1.2(i).  Irredundancy of
`U` upgrades isometry-class minimality to the paper's proper-subset
formulation. -/
theorem heHu2022Theorem12PublishedEvenLiteral
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    IsLiteralMinimalUniversalityTestingFamily
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := pairs))
      (2 * pairs + 2) := by
  have hminimal := heHu2022Theorem12PublishedEven U hU pairs
  refine ⟨hminimal.1, ?_⟩
  intro i
  obtain ⟨M, hMIntegral, hmiss, hothers⟩ := hminimal.2 i
  refine ⟨M, hMIntegral, hmiss, ?_⟩
  intro j hji
  apply hothers j
  intro hiso
  exact hji (heHuPublishedEven_model_eq_of_ambientlyIsometric
    U hU hiso)

/-- The literal deletion-minimal form of Theorem 1.2(ii). -/
theorem heHu2022Theorem12PublishedOddLiteral
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    IsLiteralMinimalUniversalityTestingFamily
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs))
      (2 * pairs + 3) := by
  have hminimal := heHu2022Theorem12PublishedOdd U hU pairs
  refine ⟨hminimal.1, ?_⟩
  intro i
  obtain ⟨M, hMIntegral, hmiss, hothers⟩ := hminimal.2 i
  refine ⟨M, hMIntegral, hmiss, ?_⟩
  intro j hji
  apply hothers j
  intro hiso
  exact hji (heHuPublishedOdd_model_eq_of_ambientlyIsometric
    U hU hiso)

end Lattice.QuadraticLatticeModel

end Bong
