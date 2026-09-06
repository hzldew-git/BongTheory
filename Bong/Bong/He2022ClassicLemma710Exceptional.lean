/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma77
import Bong.Bong.He2022ClassicLemma79
import Bong.Bong.He2022ClassicPublishedTestingSet

/-!
# He (2024), Lemma 7.10(i)--(ii): the exceptional-row witnesses

This file upgrades Lemmas 7.5, 7.7--7.9 to the exact bundled models in the
published even-rank testing table.  It first proves the four uniform
`P(omega)`-to-`C` representation statements used when `e = 1`, then packages
the two exceptional deletion witnesses from Lemma 7.10(ii).
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-! ## Lemma 7.10(ii): the two `P(omega)` sources represent every `C` row -/

/-- The first `P(omega)` source integrally represents every first-column
target whose determinant parameter has defect zero or one. -/
theorem he2022ClassicLemma710ii_P1Omega_represents_C1
    (pairs : Nat) (c : Kˣ) (hc : 0 <= ordUnit K c)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1)
    (heOne : ramificationIndex K = 1) :
    (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (heClassicEvenC1Model (K := K) pairs c hc) := by
  let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hBClassic := heClassicEvenC1_isClassicIntegral (K := K)
    pairs c hc
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP1 (K := K) pairs
          (heClassicOmega (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC1 (K := K) pairs c)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenP1 (K := K) pairs
        (heClassicOmega (K := K)))).2
          (he2022ClassicLemma75i_C1_represents_P1
            (K := K) pairs (heClassicOmega (K := K)) c hcDefect)
  have hnoncentral := he2022ClassicLemma78i_P1Omega
    (K := K) pairs b hBClassic heOne
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hnoncentral.1
  · exact hnoncentral.2.1
  · exact he2022ClassicLemma78ii_C1_of_zero_profile
      (K := K) pairs a
        (heClassicEvenP1OmegaGoodBONG_order_zero pairs) c hc
  · exact hnoncentral.2.2

/-- The first `P(omega)` source integrally represents every second-column
target whose determinant parameter has defect zero or one. -/
theorem he2022ClassicLemma710ii_P1Omega_represents_C2
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 <= ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1)
    (heOne : ramificationIndex K = 1) :
    (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp) := by
  let a := heClassicEvenP1OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hBClassic := heClassicEvenC2_isClassicIntegral (K := K)
    pairs c cSharp hc hcSharp
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP1 (K := K) pairs
          (heClassicOmega (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC2 (K := K) pairs c cSharp)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC2 (K := K) pairs c cSharp)
      (heClassicEvenP1 (K := K) pairs
        (heClassicOmega (K := K)))).2
          (he2022ClassicLemma75i_C2_represents_P1
            (K := K) pairs (heClassicOmega (K := K)) c cSharp hcDefect)
  have hnoncentral := he2022ClassicLemma78i_P1Omega
    (K := K) pairs b hBClassic heOne
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hnoncentral.1
  · exact hnoncentral.2.1
  · exact he2022ClassicLemma78ii_C2_of_zero_profile
      (K := K) pairs a
        (heClassicEvenP1OmegaGoodBONG_order_zero pairs)
          c cSharp hc hcSharp
  · exact hnoncentral.2.2

/-- The second `P(omega)` source integrally represents every first-column
target whose determinant parameter has defect zero or one. -/
theorem he2022ClassicLemma710ii_P2Omega_represents_C1
    (pairs : Nat) (c : Kˣ) (hc : 0 <= ordUnit K c)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1)
    (heOne : ramificationIndex K = 1) :
    (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (heClassicEvenC1Model (K := K) pairs c hc) := by
  let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  have hBClassic := heClassicEvenC1_isClassicIntegral (K := K)
    pairs c hc
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC1 (K := K) pairs c)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenP2 (K := K) pairs
        (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)))).2
          (he2022ClassicLemma75i_C1_represents_P2
            (K := K) pairs (heClassicOmega (K := K))
              (heClassicOmegaSharp (K := K)) c hcDefect)
  have hnoncentral := he2022ClassicLemma78i_P2Omega
    (K := K) pairs b hBClassic heOne
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hnoncentral.1
  · exact hnoncentral.2.1
  · exact he2022ClassicLemma78ii_C1_of_zero_profile
      (K := K) pairs a
        (heClassicEvenP2OmegaGoodBONG_order_zero pairs) c hc
  · exact hnoncentral.2.2

/-- The second `P(omega)` source integrally represents every second-column
target whose determinant parameter has defect zero or one. -/
theorem he2022ClassicLemma710ii_P2Omega_represents_C2
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 <= ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0)
    (hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1)
    (heOne : ramificationIndex K = 1) :
    (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp) := by
  let a := heClassicEvenP2OmegaGoodBONG (K := K) pairs
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  have hBClassic := heClassicEvenC2_isClassicIntegral (K := K)
    pairs c cSharp hc hcSharp
  have hAmbient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenP2 (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))).Represents
        (BONG.coefficientDiagonalSpace
          (heClassicEvenC2 (K := K) pairs c cSharp)) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heClassicEvenC2 (K := K) pairs c cSharp)
      (heClassicEvenP2 (K := K) pairs
        (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)))).2
          (he2022ClassicLemma75i_C2_represents_P2
            (K := K) pairs (heClassicOmega (K := K))
              (heClassicOmegaSharp (K := K)) c cSharp hcDefect)
  have hnoncentral := he2022ClassicLemma78i_P2Omega
    (K := K) pairs b hBClassic heOne
  apply a.he2022ClassicRepresents_of_pointwisePrime b (by omega) hAmbient
  · exact hnoncentral.1
  · exact hnoncentral.2.1
  · exact he2022ClassicLemma78ii_C2_of_zero_profile
      (K := K) pairs a
        (heClassicEvenP2OmegaGoodBONG_order_zero pairs)
          c cSharp hc hcSharp
  · exact hnoncentral.2.2

/-! ## The two exceptional indices when `e = 1` -/

/-- The published exceptional row `H_e^n(1)`. -/
def heClassicExceptionalOneIndex (e : Nat) : HeClassicExceptionalIndex e :=
  ⟨false, Or.inl rfl⟩

/-- The second exceptional row `H_1^n(Delta)`. -/
def heClassicExceptionalDiscriminantIndex {e : Nat} (he : e = 1) :
    HeClassicExceptionalIndex e :=
  ⟨true, Or.inr he⟩

@[simp] theorem heClassicExceptionalOneIndex_parameter (e : Nat) :
    HeClassicExceptionalIndex.parameter (K := K)
      (heClassicExceptionalOneIndex e) = 1 := by
  simp [HeClassicExceptionalIndex.parameter,
    heClassicExceptionalOneIndex]

@[simp] theorem heClassicExceptionalDiscriminantIndex_parameter
    {e : Nat} (he : e = 1) :
    HeClassicExceptionalIndex.parameter (K := K)
      (heClassicExceptionalDiscriminantIndex he) =
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := by
  simp [HeClassicExceptionalIndex.parameter,
    heClassicExceptionalDiscriminantIndex]

theorem heClassicExceptionalOneIndex_ne_discriminant
    {e : Nat} (he : e = 1) :
    heClassicExceptionalOneIndex e ≠
      heClassicExceptionalDiscriminantIndex he := by
  intro h
  have := congrArg Subtype.val h
  simp [heClassicExceptionalOneIndex,
    heClassicExceptionalDiscriminantIndex] at this

@[simp] theorem heClassicPublishedEven_model_exceptional_one
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inl (heClassicExceptionalOneIndex (ramificationIndex K))) =
      heClassicEvenHOneModel (K := K) pairs := by
  simp [HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenHOneModel]

@[simp] theorem heClassicPublishedEven_model_exceptional_discriminant
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inl (heClassicExceptionalDiscriminantIndex heOne)) =
      heClassicEvenHDiscriminantModel (K := K) pairs := by
  simp [HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenHDiscriminantModel]

/-! ## Rowwise representation of the finite published `C` table -/

private theorem he2022Classic_unitRepresentative_order_zero
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i : I) : ordUnit K (U i) = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)

private theorem he2022Classic_oddParameter_order_one
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i : I) :
    ordUnit K (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
  rw [ordUnit_mul, he2022Classic_unitRepresentative_order_zero U hU i,
    ordUnit_uniformizerPowerUnit]
  norm_num

private theorem he2022Classic_defectOrder_zero_of_order_one
    (c : Kˣ) (hc : ordUnit K c = 1) :
    BONG.GoodBONG.defectOrder (K := K) c = 0 := by
  unfold BONG.GoodBONG.defectOrder
  rw [quadraticDefect_eq_zero_of_odd_ordUnit c (by rw [hc]; norm_num)]
  rfl

/-! ## Lemma 7.10(i): the `P₂(Delta)` source when `e > 1` -/

/-- The `P₂(Delta)` source represents every nonexceptional entry of the
literal published even table. -/
theorem he2022ClassicLemma710i_P2Discriminant_represents_publishedC
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (j : (HeClassicDefectOneIndex (K := K) U × Bool) ⊕ (I × Bool)) :
    (heClassicEvenP2DiscriminantModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inr j)) := by
  rcases j with j | i
  · rcases j with ⟨j, column⟩
    have hcZero := he2022Classic_unitRepresentative_order_zero U hU j.1
    have hcNonnegative : 0 ≤ ordUnit K (U j.1) := by rw [hcZero]
    have hcOrder : ordUnit K (U j.1) = 1 - (1 : Int) := by
      rw [hcZero]
      norm_num
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma77_C1_represents
          (K := K) pairs (U j.1) hcNonnegative 1 (Or.inr rfl)
            hcOrder j.2
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma77_C2_represents
          (K := K) pairs (U j.1)
            (heClassicDefectOneSharp (K := K) (U j.1) j.2)
              hcNonnegative (heClassicDefectOneSharp_order (U j.1) j.2)
                1 (Or.inr rfl) hcOrder j.2
  · rcases i with ⟨i, column⟩
    let c := U i * uniformizerPowerUnit K (1 : Int)
    have hcOne : ordUnit K c = 1 :=
      he2022Classic_oddParameter_order_one U hU i
    have hcNonnegative : 0 ≤ ordUnit K c := by rw [hcOne]; norm_num
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 :=
      he2022Classic_defectOrder_zero_of_order_one c hcOne
    have hcOrder : ordUnit K c = 1 - (0 : Int) := by simpa using hcOne
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdelta : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma77_C1_represents
          (K := K) pairs c hcNonnegative 0 (Or.inl rfl)
            hcOrder (by simpa using hcDefect)
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma77_C2_represents
          (K := K) pairs c delta hcNonnegative hdelta 0 (Or.inl rfl)
            hcOrder (by simpa using hcDefect)

/-- When `e > 1`, the only exceptional row in the published even table is
`H_e^n(1)`. -/
theorem heClassicExceptionalIndex_eq_one_of_one_lt
    (he : 1 < ramificationIndex K)
    (h : HeClassicExceptionalIndex (ramificationIndex K)) :
    h = heClassicExceptionalOneIndex (ramificationIndex K) := by
  apply Subtype.ext
  rcases h.2 with hb | heOne
  · simpa [heClassicExceptionalOneIndex] using hb
  · omega

/-- Literal form of Lemma 7.10(i): for `e > 1`, `P₂(Delta)` represents
every published row other than `H_e^n(1)`. -/
theorem he2022ClassicLemma710i_P2Discriminant_represents_all_except_HOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (he : 1 < ramificationIndex K)
    (j : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K))
    (hj : j ≠ .inl
      (heClassicExceptionalOneIndex (ramificationIndex K))) :
    (heClassicEvenP2DiscriminantModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  rcases j with h | j
  · have hh := heClassicExceptionalIndex_eq_one_of_one_lt
      (K := K) he h
    subst h
    exact (hj rfl).elim
  · exact he2022ClassicLemma710i_P2Discriminant_represents_publishedC
      (K := K) U hU pairs j

/-- The Lemma 7.10(i) source misses its unique exceptional row. -/
theorem he2022ClassicLemma710i_P2Discriminant_not_represents_published_HOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    ¬ (heClassicEvenP2DiscriminantModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inl (heClassicExceptionalOneIndex (ramificationIndex K)))) := by
  intro hrep
  change Lattice.Represents
    (BONG.coefficientDiagonalSpace
      (heClassicEvenP2 (K := K) pairs
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int))))
    (BONG.coefficientDiagonalSpace
      (heClassicEvenH (K := K) pairs 1)) _ _ at hrep
  apply he2022ClassicLemma75ii_evenHOne_not_represents_P2Discriminant
    (K := K) pairs
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (heClassicEvenH (K := K) pairs 1)
    (heClassicEvenP2 (K := K) pairs
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      (uniformizerPowerUnit K (1 : Int)))).1
  exact hrep.ambient

/-- Lemma 7.10(i), the literal deletion witness for the unique exceptional
row when `e > 1`. -/
theorem he2022ClassicLemma710i_publishedHOne_deletionWitness
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (he : 1 < ramificationIndex K) :
    ∃ X : Lattice.QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧
      ¬ X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
          (.inl
            (heClassicExceptionalOneIndex (ramificationIndex K)))) ∧
      ∀ j : HeClassicPublishedEvenTestingIndex (K := K) U
          (ramificationIndex K),
        j ≠ .inl
            (heClassicExceptionalOneIndex (ramificationIndex K)) →
          X.Represents
            (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  refine ⟨heClassicEvenP2DiscriminantModel (K := K) pairs, ?_, ?_, ?_⟩
  · exact heClassicEvenP2DiscriminantModel_isClassicIntegral pairs
  · exact
      he2022ClassicLemma710i_P2Discriminant_not_represents_published_HOne
        (K := K) U hU pairs
  · intro j hj
    exact
      he2022ClassicLemma710i_P2Discriminant_represents_all_except_HOne
        (K := K) U hU pairs he j hj

/-- At `e = 1`, the first auxiliary row represents every nonexceptional
entry of the literal published even table. -/
theorem he2022ClassicLemma710ii_P1Omega_represents_publishedC
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1)
    (j : (HeClassicDefectOneIndex (K := K) U × Bool) ⊕ (I × Bool)) :
    (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inr j)) := by
  rcases j with j | i
  · rcases j with ⟨j, column⟩
    have hcZero := he2022Classic_unitRepresentative_order_zero U hU j.1
    have hcNonnegative : 0 <= ordUnit K (U j.1) := by rw [hcZero]
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P1Omega_represents_C1
          (K := K) pairs (U j.1) hcNonnegative (Or.inr j.2) heOne
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P1Omega_represents_C2
          (K := K) pairs (U j.1)
            (heClassicDefectOneSharp (K := K) (U j.1) j.2)
              hcNonnegative (heClassicDefectOneSharp_order (U j.1) j.2)
                (Or.inr j.2) heOne
  · rcases i with ⟨i, column⟩
    let c := U i * uniformizerPowerUnit K (1 : Int)
    have hcOne : ordUnit K c = 1 :=
      he2022Classic_oddParameter_order_one U hU i
    have hcNonnegative : 0 <= ordUnit K c := by rw [hcOne]; norm_num
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 :=
      he2022Classic_defectOrder_zero_of_order_one c hcOne
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdelta : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P1Omega_represents_C1
          (K := K) pairs c hcNonnegative (Or.inl hcDefect) heOne
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P1Omega_represents_C2
          (K := K) pairs c delta hcNonnegative hdelta
            (Or.inl hcDefect) heOne

/-- At `e = 1`, the second auxiliary row represents every nonexceptional
entry of the literal published even table. -/
theorem he2022ClassicLemma710ii_P2Omega_represents_publishedC
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1)
    (j : (HeClassicDefectOneIndex (K := K) U × Bool) ⊕ (I × Bool)) :
    (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inr j)) := by
  rcases j with j | i
  · rcases j with ⟨j, column⟩
    have hcZero := he2022Classic_unitRepresentative_order_zero U hU j.1
    have hcNonnegative : 0 <= ordUnit K (U j.1) := by rw [hcZero]
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P2Omega_represents_C1
          (K := K) pairs (U j.1) hcNonnegative (Or.inr j.2) heOne
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P2Omega_represents_C2
          (K := K) pairs (U j.1)
            (heClassicDefectOneSharp (K := K) (U j.1) j.2)
              hcNonnegative (heClassicDefectOneSharp_order (U j.1) j.2)
                (Or.inr j.2) heOne
  · rcases i with ⟨i, column⟩
    let c := U i * uniformizerPowerUnit K (1 : Int)
    have hcOne : ordUnit K c = 1 :=
      he2022Classic_oddParameter_order_one U hU i
    have hcNonnegative : 0 <= ordUnit K c := by rw [hcOne]; norm_num
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 :=
      he2022Classic_defectOrder_zero_of_order_one c hcOne
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdelta : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)
    cases column
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P2Omega_represents_C1
          (K := K) pairs c hcNonnegative (Or.inl hcDefect) heOne
    · simpa [HeClassicPublishedEvenTestingIndex.model] using
        he2022ClassicLemma710ii_P2Omega_represents_C2
          (K := K) pairs c delta hcNonnegative hdelta
            (Or.inl hcDefect) heOne

theorem heClassicExceptionalIndex_eq_one_or_discriminant
    (heOne : ramificationIndex K = 1)
    (h : HeClassicExceptionalIndex (ramificationIndex K)) :
    h = heClassicExceptionalOneIndex (ramificationIndex K) ∨
      h = heClassicExceptionalDiscriminantIndex heOne := by
  cases hb : h.1
  · left
    apply Subtype.ext
    simpa [heClassicExceptionalOneIndex] using hb
  · right
    apply Subtype.ext
    simpa [heClassicExceptionalDiscriminantIndex] using hb

/-- Literal form of Lemma 7.10(ii), first witness: `P₁(omega)` represents
every published row other than `H₁(Delta)`. -/
theorem he2022ClassicLemma710ii_P1Omega_represents_all_except_HDiscriminant
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1)
    (j : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K))
    (hj : j ≠ .inl (heClassicExceptionalDiscriminantIndex heOne)) :
    (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  rcases j with h | j
  · rcases heClassicExceptionalIndex_eq_one_or_discriminant
      (K := K) heOne h with hOne | hDiscriminant
    · subst h
      simpa using he2022ClassicLemma79iii_P1Omega_represents_HOne
        (K := K) pairs heOne
    · subst h
      exact (hj rfl).elim
  · exact he2022ClassicLemma710ii_P1Omega_represents_publishedC
      (K := K) U hU pairs heOne j

/-- Literal form of Lemma 7.10(ii), second witness: `P₂(omega)` represents
every published row other than `H₁(1)`. -/
theorem he2022ClassicLemma710ii_P2Omega_represents_all_except_HOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1)
    (j : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K))
    (hj : j ≠ .inl
      (heClassicExceptionalOneIndex (ramificationIndex K))) :
    (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  rcases j with h | j
  · rcases heClassicExceptionalIndex_eq_one_or_discriminant
      (K := K) heOne h with hOne | hDiscriminant
    · subst h
      exact (hj rfl).elim
    · subst h
      simpa using he2022ClassicLemma79iii_P2Omega_represents_HDiscriminant
        (K := K) pairs heOne
  · exact he2022ClassicLemma710ii_P2Omega_represents_publishedC
      (K := K) U hU pairs heOne j

/-- The first Lemma 7.10(ii) source misses its stated exceptional row. -/
theorem he2022ClassicLemma710ii_P1Omega_not_represents_published_HDiscriminant
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ¬ (heClassicEvenP1OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inl (heClassicExceptionalDiscriminantIndex heOne))) := by
  simpa using he2022ClassicLemma79iii_P1Omega_not_represents_HDiscriminant
    (K := K) pairs heOne

/-- The second Lemma 7.10(ii) source misses its stated exceptional row. -/
theorem he2022ClassicLemma710ii_P2Omega_not_represents_published_HOne
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ¬ (heClassicEvenP2OmegaModel (K := K) pairs).Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
        (.inl (heClassicExceptionalOneIndex (ramificationIndex K)))) := by
  simpa using he2022ClassicLemma79iii_P2Omega_not_represents_HOne
    (K := K) pairs heOne

@[simp] theorem heClassicEvenP1OmegaModel_isClassicIntegral
    (pairs : Nat) :
    (heClassicEvenP1OmegaModel (K := K) pairs).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace
      (heClassicEvenP1 (K := K) pairs (heClassicOmega (K := K))))
    (heHuExactRealization
      (heClassicEvenP1 (K := K) pairs (heClassicOmega (K := K)))
      (heClassicEvenP1_adjacentAdmissible pairs _
        (heClassicOmega_order (K := K)))
      (heClassicEvenP1_weakTwoStep pairs _
        (heClassicOmega_order (K := K)))).lattice
  exact heClassicEvenP1_isClassicIntegral (K := K) pairs _
    (heClassicOmega_order (K := K))

@[simp] theorem heClassicEvenP2OmegaModel_isClassicIntegral
    (pairs : Nat) :
    (heClassicEvenP2OmegaModel (K := K) pairs).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace
      (heClassicEvenP2 (K := K) pairs (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K))))
    (heHuExactRealization
      (heClassicEvenP2 (K := K) pairs (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)))
      (heClassicEvenP2_adjacentAdmissible pairs _ _
        (heClassicOmega_order (K := K)) (by
          rw [heClassicOmegaSharp_order (K := K)]))
      (heClassicEvenP2_weakTwoStep pairs _ _
        (heClassicOmega_order (K := K)) (by
          rw [heClassicOmegaSharp_order (K := K)]))).lattice
  exact heClassicEvenP2_isClassicIntegral (K := K) pairs _ _
    (heClassicOmega_order (K := K)) (by
      rw [heClassicOmegaSharp_order (K := K)])

/-- Lemma 7.10(ii), first literal deletion witness in the published finite
table. -/
theorem he2022ClassicLemma710ii_publishedHDiscriminant_deletionWitness
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ∃ X : Lattice.QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧
      ¬ X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
          (.inl (heClassicExceptionalDiscriminantIndex heOne))) ∧
      ∀ j : HeClassicPublishedEvenTestingIndex (K := K) U
          (ramificationIndex K),
        j ≠ .inl (heClassicExceptionalDiscriminantIndex heOne) →
          X.Represents
            (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  refine ⟨heClassicEvenP1OmegaModel (K := K) pairs, ?_, ?_, ?_⟩
  · exact heClassicEvenP1OmegaModel_isClassicIntegral pairs
  · exact
      he2022ClassicLemma710ii_P1Omega_not_represents_published_HDiscriminant
        (K := K) U hU pairs heOne
  · intro j hj
    exact he2022ClassicLemma710ii_P1Omega_represents_all_except_HDiscriminant
      (K := K) U hU pairs heOne j hj

/-- Lemma 7.10(ii), second literal deletion witness in the published finite
table. -/
theorem he2022ClassicLemma710ii_publishedHOne_deletionWitness
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    ∃ X : Lattice.QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧
      ¬ X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs
          (.inl
            (heClassicExceptionalOneIndex (ramificationIndex K)))) ∧
      ∀ j : HeClassicPublishedEvenTestingIndex (K := K) U
          (ramificationIndex K),
        j ≠ .inl
            (heClassicExceptionalOneIndex (ramificationIndex K)) →
          X.Represents
            (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs j) := by
  refine ⟨heClassicEvenP2OmegaModel (K := K) pairs, ?_, ?_, ?_⟩
  · exact heClassicEvenP2OmegaModel_isClassicIntegral pairs
  · exact he2022ClassicLemma710ii_P2Omega_not_represents_published_HOne
      (K := K) U hU pairs heOne
  · intro j hj
    exact he2022ClassicLemma710ii_P2Omega_represents_all_except_HOne
      (K := K) U hU pairs heOne j hj

end Bong
