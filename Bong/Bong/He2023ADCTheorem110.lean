/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankOne
import Bong.Bong.He2023ADCQuaternaryCatalogue
import Bong.Bong.He2023ADCSectionFour
import Bong.Bong.He2023ADCTheorem62Stable
import Bong.Bong.He2023ADCTheorem71

/-!
# He (2025), Theorem 1.10 over dyadic local fields

This file turns the classification theorems used by Theorem 1.10 into exact
finite integral-isometry catalogues.  Thus the numerical formulas below do
not merely count a parameter type: every representative has the stated rank
and is `n`-ADC, every such lattice occurs, and no integral-isometry class is
repeated.

The equal-rank and corank-one cases, and the stable even corank-two case, are
the published maximal tables.  The odd corank-two case is the exact catalogue
of Corollary 7.21.  The exceptional binary corank-two case is deliberately
kept in `He2023ADCQuaternaryCatalogue`, where the printed `+1` is refuted and
the corrected `+2` is proved.

The final substitution `|U| = 2 * (N p)^e` is supplied by the proved
principal-unit filtration count corresponding to O'Meara 63:9, so none of
the numerical conclusions carries an external counting premise.
-/

namespace Bong

open Dyadic Module Lattice.QuadraticLatticeModel

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Integral isometry between two bundled lattice models. -/
abbrev HeADC2025IsIntegrallyIsometric :=
  HeADC2025Corollary721Index.IsIntegrallyIsometric (K := K)

/-- A family is an exact catalogue of rank-`m`, `n`-ADC lattices when its
members have the right rank and property, it is complete, and it has no
repeated integral-isometry class. -/
structure HeADC2025IsExactNADCIsometryCatalogue
    {J : Type u} (n m : Nat)
    (family : J → Lattice.QuadraticLatticeModel (K := K)) : Prop where
  rank (j : J) : (family j).rank = m
  nADC (j : J) : (family j).IsNADC n
  complete (X : Lattice.QuadraticLatticeModel (K := K)) :
    X.rank = m → X.IsNADC n →
      ∃ j : J, HeADC2025IsIntegrallyIsometric X (family j)
  irredundant {i j : J} :
    HeADC2025IsIntegrallyIsometric (family i) (family j) → i = j

namespace Lattice.QuadraticLatticeModel

/-- The finite even maximal table is an exact `n`-ADC catalogue whenever
the relevant rank branch of the classification says that every `n`-ADC
lattice is maximal. -/
theorem heADC2025PublishedEven_exactCatalogue_of_isOMaximal
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs n : Nat)
    (hmaximal : ∀ X : QuadraticLatticeModel (K := K),
      X.rank = 2 * pairs + 2 → X.IsNADC n → X.IsOMaximal) :
    HeADC2025IsExactNADCIsometryCatalogue n (2 * pairs + 2)
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := pairs)) where
  rank := HeHuPublishedEvenTestingIndex.model_rank
  nADC i := (HeHuPublishedEvenTestingIndex.model_isOMaximal i).isNADC n
  complete X hRank hADC := by
    obtain ⟨i, hambient⟩ :=
      exists_publishedEvenIndex_for_model U hU pairs X hRank
    let Y := HeHuPublishedEvenTestingIndex.model (K := K) i
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup Y.Carrier := Y.addCommGroup
    letI : Module K Y.Carrier := Y.module
    exact ⟨i, Lattice.oMaximal_isIsometric_of_isometric
      (hmaximal X hRank hADC)
      (HeHuPublishedEvenTestingIndex.model_isOMaximal i) hambient⟩
  irredundant {i j} hisometric := by
    let X := HeHuPublishedEvenTestingIndex.model (K := K) i
    let Y := HeHuPublishedEvenTestingIndex.model (K := K) j
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup Y.Carrier := Y.addCommGroup
    letI : Module K Y.Carrier := Y.module
    rcases hisometric with ⟨f⟩
    exact heHuPublishedEven_model_eq_of_ambientlyIsometric U hU
      ⟨f.toQuadraticSpaceIsometry⟩

/-- The finite odd maximal table is an exact `n`-ADC catalogue whenever
the relevant rank branch of the classification says that every `n`-ADC
lattice is maximal. -/
theorem heADC2025PublishedOdd_exactCatalogue_of_isOMaximal
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs n : Nat)
    (hmaximal : ∀ X : QuadraticLatticeModel (K := K),
      X.rank = 2 * pairs + 3 → X.IsNADC n → X.IsOMaximal) :
    HeADC2025IsExactNADCIsometryCatalogue n (2 * pairs + 3)
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs)) where
  rank := HeHuPublishedOddTestingIndex.model_rank
  nADC i := (HeHuPublishedOddTestingIndex.model_isOMaximal i).isNADC n
  complete X hRank hADC := by
    obtain ⟨i, hambient⟩ :=
      exists_publishedOddIndex_for_model U hU pairs X hRank
    let Y := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) i
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup Y.Carrier := Y.addCommGroup
    letI : Module K Y.Carrier := Y.module
    exact ⟨i, Lattice.oMaximal_isIsometric_of_isometric
      (hmaximal X hRank hADC)
      (HeHuPublishedOddTestingIndex.model_isOMaximal i) hambient⟩
  irredundant {i j} hisometric := by
    let X := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) i
    let Y := HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) j
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    letI : AddCommGroup Y.Carrier := Y.addCommGroup
    letI : Module K Y.Carrier := Y.module
    rcases hisometric with ⟨f⟩
    exact heHuPublishedOdd_model_eq_of_ambientlyIsometric U hU
      ⟨f.toQuadraticSpaceIsometry⟩

end Lattice.QuadraticLatticeModel

/-! ## Exact catalogue branches of Theorem 1.10 -/

/-- Equal even rank: Proposition 4.15 makes the published even table an
exact catalogue of `(2k+2)`-ADC lattices of rank `2k+2`. -/
theorem heADC2025Theorem110EqualRankEvenCatalogue
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 2)
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := k)) := by
  apply heADC2025PublishedEven_exactCatalogue_of_isOMaximal U hU
  intro X hRank hADC
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsNADC.isOMaximal_of_finrank_eq hADC hRank

/-- Equal odd rank: Proposition 4.15 makes the published odd table an exact
catalogue of `(2k+3)`-ADC lattices of rank `2k+3`. -/
theorem heADC2025Theorem110EqualRankOddCatalogue
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 3)
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := k)) := by
  apply heADC2025PublishedOdd_exactCatalogue_of_isOMaximal U hU
  intro X hRank hADC
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsNADC.isOMaximal_of_finrank_eq hADC hRank

/-- Even `n`, corank one: Theorem 6.1 makes the published odd-rank table an
exact catalogue. -/
theorem heADC2025Theorem110EvenCorankOneCatalogue
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 3)
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := k)) := by
  apply heADC2025PublishedOdd_exactCatalogue_of_isOMaximal U hU
  intro X hRank hADC
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact (Lattice.heADC2025Theorem61 X.form X.lattice (2 * k + 2)
    (by omega) (by exact ⟨k + 1, by omega⟩) hRank).mp hADC

/-- Odd `n`, corank one: Theorem 7.1 makes the published even-rank table an
exact catalogue. -/
theorem heADC2025Theorem110OddCorankOneCatalogue
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 4)
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := k + 1)) := by
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
    (heADC2025PublishedEven_exactCatalogue_of_isOMaximal
      U hU (k + 1) (2 * k + 3) (by
        intro X hRank hADC
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        change finrank K X.Carrier = 2 * (k + 1) + 2 at hRank
        have hAmbientRank : finrank K X.Carrier = 2 * k + 4 := by
          omega
        apply (Lattice.heADC2025Theorem71 X.form X.lattice (2 * k + 3)
          (by omega) (by exact ⟨k + 1, by omega⟩) hAmbientRank).mp
        exact hADC))

/-- Even `n >= 4`, corank two: the corrected stable Theorem 6.2 makes the
published even table an exact catalogue. -/
theorem heADC2025Theorem110EvenCorankTwoCatalogue
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (hk : 0 < k) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 4)
      (HeHuPublishedEvenTestingIndex.model
        (K := K) (U := U) (pairs := k + 1)) := by
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
    (heADC2025PublishedEven_exactCatalogue_of_isOMaximal
      U hU (k + 1) (2 * k + 2) (by
        intro X hRank hADC
        letI : AddCommGroup X.Carrier := X.addCommGroup
        letI : Module K X.Carrier := X.module
        change finrank K X.Carrier = 2 * (k + 1) + 2 at hRank
        have hAmbientRank : finrank K X.Carrier = 2 * k + 4 := by
          omega
        exact (Lattice.heADC2025Theorem62_of_four_le k hk hAmbientRank).mp hADC))

/-! ## Cardinalities in the notation of the published theorem -/

/-- The binary equal-rank branch has `8 * (N p)^e - 1` classes. -/
theorem heADC2025Theorem110EqualRankBinaryCount
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U 0) =
      8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K - 1 := by
  rw [card_heHuPublishedEvenTestingIndex_zero U hU,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  omega

/-- Every positive even-table level has `8 * (N p)^e` classes. -/
theorem heADC2025Theorem110EvenTableCount
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (hpairs : 0 < pairs) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U pairs) =
      8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_heHuPublishedEvenTestingIndex_of_pos U hpairs,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

/-- Every odd-table level has `8 * (N p)^e` classes. -/
theorem heADC2025Theorem110OddTableCount
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeHuPublishedOddTestingIndex I) =
      8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_heHuPublishedOddTestingIndex I,
    HeADC2025Corollary721CountingLaw.card_unit_representatives
      (K := K) U hU]
  ring

/-- Exact catalogue and printed count in the binary equal-rank branch. -/
theorem heADC2025Theorem110EqualRankBinary
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    HeADC2025IsExactNADCIsometryCatalogue 2 2
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := 0)) ∧
      Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U 0) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K - 1 :=
  ⟨heADC2025Theorem110EqualRankEvenCatalogue U hU 0,
    heADC2025Theorem110EqualRankBinaryCount U hU⟩

/-- Exact catalogue and printed count for positive even equal ranks. -/
theorem heADC2025Theorem110EqualRankEven
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (hk : 0 < k) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 2)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U k) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K :=
  ⟨heADC2025Theorem110EqualRankEvenCatalogue U hU k,
    heADC2025Theorem110EvenTableCount U hU k hk⟩

/-- Exact catalogue and printed count for odd equal ranks. -/
theorem heADC2025Theorem110EqualRankOdd
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 3)
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedOddTestingIndex I) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K :=
  ⟨heADC2025Theorem110EqualRankOddCatalogue U hU k,
    heADC2025Theorem110OddTableCount U hU⟩

/-- Exact catalogue and printed count for even `n` in corank one. -/
theorem heADC2025Theorem110EvenCorankOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 3)
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedOddTestingIndex I) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K :=
  ⟨heADC2025Theorem110EvenCorankOneCatalogue U hU k,
    heADC2025Theorem110OddTableCount U hU⟩

/-- Exact catalogue and printed count for odd `n` in corank one. -/
theorem heADC2025Theorem110OddCorankOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 4)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k + 1)) ∧
      Fintype.card
          (HeHuPublishedEvenTestingIndex (K := K) U (k + 1)) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K :=
  ⟨heADC2025Theorem110OddCorankOneCatalogue U hU k,
    heADC2025Theorem110EvenTableCount U hU (k + 1) (by omega)⟩

/-- Exact catalogue and printed count for even `n >= 4` in corank two. -/
theorem heADC2025Theorem110EvenCorankTwo
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (k : Nat) (hk : 0 < k) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 4)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k + 1)) ∧
      Fintype.card
          (HeHuPublishedEvenTestingIndex (K := K) U (k + 1)) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K :=
  ⟨heADC2025Theorem110EvenCorankTwoCatalogue U hU k hk,
    heADC2025Theorem110EvenTableCount U hU (k + 1) (by omega)⟩

/-! ## One exhaustive dyadic endpoint -/

/-- The corrected dyadic content of Theorem 1.10, split into its exhaustive
parity, rank, and binary-boundary branches.  The binary corank-two field is
the corrected six-family catalogue; the following field separately records
the formal refutation of the publisher's five-family `+1` count. -/
structure HeADC2025Theorem110DyadicCorrectedConclusion
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) : Prop where
  equalRankBinary :
    HeADC2025IsExactNADCIsometryCatalogue 2 2
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := 0)) ∧
      Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U 0) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K - 1
  equalRankEven (k : Nat) (hk : 0 < k) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 2)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U k) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K
  equalRankOdd (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 3)
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedOddTestingIndex I) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K
  evenCorankOne (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 3)
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := k)) ∧
      Fintype.card (HeHuPublishedOddTestingIndex I) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K
  oddCorankOne (k : Nat) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 3) (2 * k + 4)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k + 1)) ∧
      Fintype.card
          (HeHuPublishedEvenTestingIndex (K := K) U (k + 1)) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K
  evenCorankTwo (k : Nat) (hk : 0 < k) :
    HeADC2025IsExactNADCIsometryCatalogue (2 * k + 2) (2 * k + 4)
        (HeHuPublishedEvenTestingIndex.model
          (K := K) (U := U) (pairs := k + 1)) ∧
      Fintype.card
          (HeHuPublishedEvenTestingIndex (K := K) U (k + 1)) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K
  binaryCorankTwoCorrected :
    HeADC2025QuaternaryCatalogue.IsExactIsometryCatalogue
        (K := K) (HeADC2025QuaternaryCatalogue.model (K := K) U) ∧
      Fintype.card (HeADC2025QuaternaryCatalogue.Index (K := K) U) =
        8 * heADC2025ResidueNorm (K := K) ^ ramificationIndex K + 2
  binaryPublishedCountFalse :
    ¬ HeADC2025QuaternaryCatalogue.HeADC2025Theorem110BinaryCountStatement
      (K := K) U
  oddCorankTwo (k : Nat) :
    HeADC2025Corollary721Index.IsExactNADCIsometryCatalogue k
        (HeADC2025Corollary721Index.model U hU k) ∧
      (∀ x : HeADC2025Corollary721Index K I,
        (HeADC2025Corollary721Index.model U hU k x).IsOMaximal ↔
          ∃ m : HeADC2025Corollary721MaximalIndex I, x = .inl m) ∧
      Fintype.card (HeADC2025Corollary721Index K I) =
        (8 * ramificationIndex K + 6) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K ∧
      Fintype.card (HeADC2025Corollary721NonmaximalIndex K I) =
        (8 * ramificationIndex K - 2) *
          heADC2025ResidueNorm (K := K) ^ ramificationIndex K

/-- Complete corrected dyadic Theorem 1.10.  Every branch is backed by an
exact integral-isometry catalogue, rather than only a cardinal identity. -/
theorem heADC2025Theorem110DyadicCorrected
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    HeADC2025Theorem110DyadicCorrectedConclusion U hU where
  equalRankBinary := heADC2025Theorem110EqualRankBinary U hU
  equalRankEven := heADC2025Theorem110EqualRankEven U hU
  equalRankOdd := heADC2025Theorem110EqualRankOdd U hU
  evenCorankOne := heADC2025Theorem110EvenCorankOne U hU
  oddCorankOne := heADC2025Theorem110OddCorankOne U hU
  evenCorankTwo := heADC2025Theorem110EvenCorankTwo U hU
  binaryCorankTwoCorrected :=
    ⟨HeADC2025QuaternaryCatalogue.isExactIsometryCatalogue U hU,
      HeADC2025QuaternaryCatalogue.card_index_corrected U hU⟩
  binaryPublishedCountFalse :=
    HeADC2025QuaternaryCatalogue.not_heADC2025Theorem110BinaryCountStatement
      U hU
  oddCorankTwo := HeADC2025Corollary721Index.heADC2025Corollary721 U hU

end Bong
