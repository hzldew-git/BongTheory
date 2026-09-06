/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma43

/-!
# He (2024), irredundancy of the even published testing table

This file proves that the nested finite index used for Definition 2.6 is an
irredundant list of ambient quadratic-space classes.  The proof first forgets
the `C₁/C₂` column and identifies determinant parameters, then uses the
two-class packages of He--Hu Proposition 3.5 to separate the columns.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The determinant-parameter rows underlying the even classic table, with
the `C₁/C₂` column forgotten. -/
abbrev HeClassicEvenParameterIndex {I : Type u} (U : I → Kˣ) (e : Nat) :=
  HeClassicExceptionalIndex e ⊕
    (HeClassicDefectOneIndex (K := K) U ⊕ I)

namespace HeClassicEvenParameterIndex

/-- The determinant parameter carried by an underlying even table row. -/
noncomputable def parameter {I : Type u} (U : I → Kˣ) {e : Nat} :
    HeClassicEvenParameterIndex (K := K) U e → Kˣ
  | .inl h => HeClassicExceptionalIndex.parameter (K := K) h
  | .inr (.inl i) => U i.1
  | .inr (.inr i) => U i * uniformizerPowerUnit K (1 : Int)

end HeClassicEvenParameterIndex

namespace HeClassicPublishedEvenTestingIndex

/-- Forget the `C₁/C₂` column while retaining the determinant parameter. -/
def parameterIndex {I : Type u} {U : I → Kˣ} {e : Nat} :
    HeClassicPublishedEvenTestingIndex (K := K) U e →
      HeClassicEvenParameterIndex (K := K) U e
  | .inl h => .inl h
  | .inr (.inl (i, _)) => .inr (.inl i)
  | .inr (.inr (i, _)) => .inr (.inr i)

/-- The determinant parameter of an even published testing-table entry. -/
noncomputable def parameter {I : Type u} (U : I → Kˣ) {e : Nat}
    (i : HeClassicPublishedEvenTestingIndex (K := K) U e) : Kˣ :=
  HeClassicEvenParameterIndex.parameter (K := K) U (parameterIndex i)

/-- A square has even normalized valuation. -/
private theorem even_ordUnit_of_isSquare (x : Kˣ) (hx : IsSquare x) :
    Even (ordUnit K x) := by
  rcases hx with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

private theorem not_isSquare_of_orders_zero_one (x y : Kˣ)
    (hx : ordUnit K x = 0) (hy : ordUnit K y = 1) :
    ¬ IsSquare (x * y) := by
  intro hsquare
  have heven := even_ordUnit_of_isSquare (K := K) (x * y) hsquare
  rw [ordUnit_mul, hx, hy] at heven
  rcases heven with ⟨z, hz⟩
  omega

private theorem exceptional_parameter_defect_ne_one
    (h : HeClassicExceptionalIndex (ramificationIndex K)) :
    defectOrder (K := K) (HeClassicExceptionalIndex.parameter (K := K) h) ≠
      (1 : WithTop ℚ) := by
  intro heq
  cases hb : h.1
  · simp [HeClassicExceptionalIndex.parameter, hb,
      defectOrder_one] at heq
  · have he : ramificationIndex K = 1 := by
      simpa [hb] using h.2
    simp [HeClassicExceptionalIndex.parameter, hb,
      defectOrder_discriminantUnit, he] at heq

private theorem exceptional_eq_of_parameter_square
    (h k : HeClassicExceptionalIndex (ramificationIndex K))
    (hsquare : IsSquare
      (HeClassicExceptionalIndex.parameter (K := K) h *
        HeClassicExceptionalIndex.parameter (K := K) k)) :
    h = k := by
  apply Subtype.ext
  cases hh : h.1 <;> cases hk : k.1
  · rfl
  · have hdef := heHuLemma45_defectOrder_eq_of_mul_isSquare
      (K := K) (HeClassicExceptionalIndex.parameter (K := K) h)
      (HeClassicExceptionalIndex.parameter (K := K) k) hsquare
    simp [HeClassicExceptionalIndex.parameter, hh, hk,
      defectOrder_one, defectOrder_discriminantUnit] at hdef
    exact (WithTop.top_ne_coe hdef).elim
  · have hdef := heHuLemma45_defectOrder_eq_of_mul_isSquare
      (K := K) (HeClassicExceptionalIndex.parameter (K := K) h)
      (HeClassicExceptionalIndex.parameter (K := K) k) hsquare
    simp [HeClassicExceptionalIndex.parameter, hh, hk,
      defectOrder_one, defectOrder_discriminantUnit] at hdef
    exact (WithTop.coe_ne_top hdef).elim
  · rfl

private theorem odd_parameter_eq_of_square
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (i j : I)
    (hsquare : IsSquare
      ((U i * uniformizerPowerUnit K (1 : Int)) *
        (U j * uniformizerPowerUnit K (1 : Int)))) :
    i = j := by
  let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
  have hpiSquare : IsSquare (pi ^ 2) := ⟨pi, pow_two pi⟩
  have hunitProduct : IsSquare (U i * U j) := by
    have hquot := hsquare.div hpiSquare
    have heq : ((U i * pi) * (U j * pi)) / pi ^ 2 = U i * U j := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero pi]
    simpa only [pi, heq] using hquot
  exact hU.irredundant hunitProduct

/-- Square-equivalent determinant parameters identify the underlying row of
the published even table before the `C₁/C₂` column is considered. -/
theorem parameterIndex_eq_of_parameter_mul_isSquare
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (p q : HeClassicEvenParameterIndex
      (K := K) U (ramificationIndex K))
    (hsquare : IsSquare
      (HeClassicEvenParameterIndex.parameter (K := K) U p *
        HeClassicEvenParameterIndex.parameter (K := K) U q)) :
    p = q := by
  rcases p with h | p
  · rcases q with k | q
    · exact congrArg Sum.inl (exceptional_eq_of_parameter_square h k hsquare)
    · rcases q with j | j
      · have hdef := heHuLemma45_defectOrder_eq_of_mul_isSquare
          (K := K) (HeClassicExceptionalIndex.parameter (K := K) h)
          (U j.1) (by
            simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)
        exact (exceptional_parameter_defect_ne_one (K := K) h
          (hdef.trans j.2)).elim
      · have hzero := HeClassicExceptionalIndex.parameter_order (K := K) h
        have hone : ordUnit K
            (U j * uniformizerPowerUnit K (1 : Int)) = 1 := by
          rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
            (isValuationUnit_iff_ordUnit_eq_zero K (U j)).1 (hU.isUnit j)]
          norm_num
        exact (not_isSquare_of_orders_zero_one
          (HeClassicExceptionalIndex.parameter (K := K) h)
          (U j * uniformizerPowerUnit K (1 : Int)) hzero hone (by
            simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)).elim
  · rcases p with i | i
    · rcases q with h | q
      · have hdef := heHuLemma45_defectOrder_eq_of_mul_isSquare
          (K := K) (U i.1)
          (HeClassicExceptionalIndex.parameter (K := K) h) (by
            simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)
        exact (exceptional_parameter_defect_ne_one (K := K) h
          (hdef.symm.trans i.2)).elim
      · rcases q with j | j
        · have hij : i.1 = j.1 := hU.irredundant (by
            simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)
          have hijSubtype : i = j := Subtype.ext hij
          cases hijSubtype
          rfl
        · have hzero : ordUnit K (U i.1) = 0 :=
            (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i.1)
          have hone : ordUnit K
              (U j * uniformizerPowerUnit K (1 : Int)) = 1 := by
            rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
              (isValuationUnit_iff_ordUnit_eq_zero K (U j)).1 (hU.isUnit j)]
            norm_num
          exact (not_isSquare_of_orders_zero_one (U i.1)
            (U j * uniformizerPowerUnit K (1 : Int)) hzero hone (by
              simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)).elim
    · rcases q with h | q
      · have hzero := HeClassicExceptionalIndex.parameter_order (K := K) h
        have hone : ordUnit K
            (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
          rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
            (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
          norm_num
        have hcomm : IsSquare
            (HeClassicExceptionalIndex.parameter (K := K) h *
              (U i * uniformizerPowerUnit K (1 : Int))) := by
          simpa only [HeClassicEvenParameterIndex.parameter, mul_comm] using hsquare
        exact (not_isSquare_of_orders_zero_one
          (HeClassicExceptionalIndex.parameter (K := K) h)
          (U i * uniformizerPowerUnit K (1 : Int)) hzero hone hcomm).elim
      · rcases q with j | j
        · have hzero : ordUnit K (U j.1) = 0 :=
            (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit j.1)
          have hone : ordUnit K
              (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
            rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
              (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
            norm_num
          have hcomm : IsSquare
              (U j.1 * (U i * uniformizerPowerUnit K (1 : Int))) := by
            simpa only [HeClassicEvenParameterIndex.parameter, mul_comm] using hsquare
          exact (not_isSquare_of_orders_zero_one (U j.1)
            (U i * uniformizerPowerUnit K (1 : Int)) hzero hone hcomm).elim
        · have hij := odd_parameter_eq_of_square U hU i j (by
            simpa only [HeClassicEvenParameterIndex.parameter] using hsquare)
          subst j
          rfl

/-- The displayed coefficient family attached to an even table index. -/
noncomputable def coefficients
    {I : Type u} [Fintype I] (U : I → Kˣ) (pairs : Nat) :
    HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) →
      Fin (2 * pairs + 2) → Kˣ
  | .inl h =>
      heClassicEvenH (K := K) pairs
        (HeClassicExceptionalIndex.parameter (K := K) h)
  | .inr (.inl (j, column)) =>
      if column then
        heClassicEvenC2 (K := K) pairs (U j.1)
          (heClassicDefectOneSharp (K := K) (U j.1) j.2)
      else
        heClassicEvenC1 (K := K) pairs (U j.1)
  | .inr (.inr (i, column)) =>
      let c := U i * uniformizerPowerUnit K (1 : Int)
      if column then
        heClassicEvenC2 (K := K) pairs c
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      else
        heClassicEvenC1 (K := K) pairs c

private theorem diagonalUnitDeterminant_heClassicEvenC1
    (pairs : Nat) (c : Kˣ) :
    diagonalUnitDeterminant (heClassicEvenC1 (K := K) pairs c) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
  rw [heClassicEvenC1_eq_heHuEvenFirst,
    diagonalUnitDeterminant_heHuEvenFirst]

private theorem diagonalUnitDeterminant_heClassicEvenH
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    diagonalUnitDeterminant (heClassicEvenH (K := K) pairs c) =
      (-1 : Kˣ) ^ (pairs + 1) * c := by
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  have hvalues : b.prefixValueUnits (2 * pairs + 2) le_rfl =
      heClassicEvenH (K := K) pairs c := by
    funext i
    change b.valueUnit i = heClassicEvenH (K := K) pairs c i
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_valueUnit]
  calc
    diagonalUnitDeterminant (heClassicEvenH (K := K) pairs c) =
        diagonalUnitDeterminant
          (b.prefixValueUnits (2 * pairs + 2) le_rfl) := by rw [hvalues]
    _ = b.prefixProduct (2 * pairs + 2) :=
      b.diagonalUnitDeterminant_prefixValueUnits (2 * pairs + 2) le_rfl
    _ = (-1 : Kˣ) ^ (pairs + 1) * c :=
      heClassicEvenH_prefixProduct_full pairs c hcClass hcOrder

private theorem heClassicEvenC_oddOrder_pairProperties
    [HilbertSymbolLaws K]
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit) := by
  let delta :=
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
  have hnegative : hilbertSymbol K delta c = -1 := by
    simpa only [delta] using
      (hilbertSymbol_discriminant_eq_neg_one_of_odd_order c hodd)
  have hclassification := heHuBinaryTwist_classification c delta hnegative
  have hbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinaryTwist c delta) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact hclassification.1
    · exact hclassification.2.1
  have hpair := hbinary.append
    (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [delta, heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinaryTwist] using hpair

/-- Every displayed coefficient row has the determinant square class of the
first `C` row carrying the same parameter. -/
theorem coefficients_determinantSquare_first
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    IsSquare
      (diagonalUnitDeterminant (coefficients (K := K) U pairs i) *
        diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs (parameter (K := K) U i))) := by
  rcases i with h | i
  · simp only [coefficients, parameter, parameterIndex,
      HeClassicEvenParameterIndex.parameter]
    rw [diagonalUnitDeterminant_heClassicEvenH pairs
        (HeClassicExceptionalIndex.parameter (K := K) h)
        (HeClassicExceptionalIndex.parameter_class (K := K) h)
        (HeClassicExceptionalIndex.parameter_order (K := K) h),
      diagonalUnitDeterminant_heClassicEvenC1]
    exact ⟨(-1 : Kˣ) ^ (pairs + 1) *
      HeClassicExceptionalIndex.parameter (K := K) h, rfl⟩
  · rcases i with j | i
    · rcases j with ⟨j, column⟩
      cases column
      · exact ⟨diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs (U j.1)), rfl⟩
      · simpa only [coefficients, parameter, parameterIndex,
          HeClassicEvenParameterIndex.parameter, if_true] using
          (heClassicEvenC_pairProperties (K := K) pairs (U j.1) j.2).determinantSquare
    · rcases i with ⟨i, column⟩
      let c := U i * uniformizerPowerUnit K (1 : Int)
      have hcOrder : ordUnit K c = 1 := by
        dsimp only [c]
        rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
          (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
        norm_num
      have hcOdd : Odd (ordUnit K c) := by
        rw [hcOrder]
        exact odd_one
      cases column
      · exact ⟨diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c), by
            rfl⟩
      · simpa only [coefficients, parameter, parameterIndex,
          HeClassicEvenParameterIndex.parameter, if_true, c] using
          (heClassicEvenC_oddOrder_pairProperties
            (K := K) pairs c hcOdd).determinantSquare

/-- A same-rank representation between displayed rows forces their
determinant parameters to differ by a square. -/
theorem parametersSquare_of_diagonalRepresents_coefficients
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat}
    {i j : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)}
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients (coefficients (K := K) U pairs i))
      (diagonalUnitCoefficients (coefficients (K := K) U pairs j))) :
    IsSquare (parameter (K := K) U i * parameter (K := K) U j) := by
  have hij := DiagonalIsometryInvariantLaws.determinant_square
    (coefficients (K := K) U pairs i)
    (coefficients (K := K) U pairs j) hrep
  have hi := coefficients_determinantSquare_first U hU pairs i
  have hj := coefficients_determinantSquare_first U hU pairs j
  have hfirstIToJ : IsSquare
      (diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs (parameter (K := K) U i)) *
        diagonalUnitDeterminant (coefficients (K := K) U pairs j)) :=
    isSquare_mul_trans _
      (diagonalUnitDeterminant (coefficients (K := K) U pairs i)) _
      (by simpa only [mul_comm] using hi) hij
  have hfirstBoth : IsSquare
      (diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs (parameter (K := K) U i)) *
        diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs (parameter (K := K) U j))) :=
    isSquare_mul_trans _
      (diagonalUnitDeterminant (coefficients (K := K) U pairs j)) _
      hfirstIToJ hj
  rw [diagonalUnitDeterminant_heClassicEvenC1,
    diagonalUnitDeterminant_heClassicEvenC1] at hfirstBoth
  let sign : Kˣ := (-1 : Kˣ) ^ (pairs + 1)
  have hsign : IsSquare (sign ^ 2) := ⟨sign, pow_two sign⟩
  have hquot := hfirstBoth.div hsign
  have heq :
      ((sign * parameter (K := K) U i) *
        (sign * parameter (K := K) U j)) / sign ^ 2 =
          parameter (K := K) U i * parameter (K := K) U j := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero sign]
  rw [heq] at hquot
  exact hquot

/-- Distinct indices in the published even classic table give distinct
ambient quadratic-space classes. -/
theorem eq_of_diagonalRepresents_coefficients
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat}
    {i j : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)}
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients (coefficients (K := K) U pairs i))
      (diagonalUnitCoefficients (coefficients (K := K) U pairs j))) :
    i = j := by
  have hsquare := parametersSquare_of_diagonalRepresents_coefficients
    U hU hrep
  have hrow := parameterIndex_eq_of_parameter_mul_isSquare U hU
    (parameterIndex i) (parameterIndex j) (by
      simpa only [parameter] using hsquare)
  rcases i with h | i
  · rcases j with k | j
    · have hk : h = k := by
        change (Sum.inl h : HeClassicEvenParameterIndex
          (K := K) U (ramificationIndex K)) = Sum.inl k at hrow
        exact Sum.inl_injective hrow
      subst k
      rfl
    · rcases j with j | j
      · change (Sum.inl h : HeClassicEvenParameterIndex
          (K := K) U (ramificationIndex K)) = Sum.inr (Sum.inl j.1) at hrow
        cases hrow
      · change (Sum.inl h : HeClassicEvenParameterIndex
          (K := K) U (ramificationIndex K)) = Sum.inr (Sum.inr j.1) at hrow
        cases hrow
  · rcases i with di | oi
    · rcases di with ⟨di, ci⟩
      rcases j with h | j
      · change (Sum.inr (Sum.inl di) : HeClassicEvenParameterIndex
          (K := K) U (ramificationIndex K)) = Sum.inl h at hrow
        cases hrow
      · rcases j with dj | oj
        · rcases dj with ⟨dj, cj⟩
          have hd : di = dj := by
            change (Sum.inr (Sum.inl di) : HeClassicEvenParameterIndex
              (K := K) U (ramificationIndex K)) =
                Sum.inr (Sum.inl dj) at hrow
            exact Sum.inl_injective (Sum.inr_injective hrow)
          subst dj
          cases ci <;> cases cj
          · rfl
          · have hforbidden :=
              (heClassicEvenC_pairProperties
                (K := K) pairs (U di.1) di.2).nonisometric
            exact False.elim (hforbidden (by
              simpa [coefficients] using
                hrep.symm_of_sameRank))
          · have hforbidden :=
              (heClassicEvenC_pairProperties
                (K := K) pairs (U di.1) di.2).nonisometric
            exact False.elim (hforbidden (by
              simpa [coefficients] using hrep))
          · rfl
        · change (Sum.inr (Sum.inl di) : HeClassicEvenParameterIndex
            (K := K) U (ramificationIndex K)) =
              Sum.inr (Sum.inr oj.1) at hrow
          cases hrow
    · rcases oi with ⟨oi, ci⟩
      rcases j with h | j
      · change (Sum.inr (Sum.inr oi) : HeClassicEvenParameterIndex
          (K := K) U (ramificationIndex K)) = Sum.inl h at hrow
        cases hrow
      · rcases j with dj | oj
        · change (Sum.inr (Sum.inr oi) : HeClassicEvenParameterIndex
            (K := K) U (ramificationIndex K)) =
              Sum.inr (Sum.inl dj.1) at hrow
          cases hrow
        · rcases oj with ⟨oj, cj⟩
          have ho : oi = oj := by
            change (Sum.inr (Sum.inr oi) : HeClassicEvenParameterIndex
              (K := K) U (ramificationIndex K)) =
                Sum.inr (Sum.inr oj) at hrow
            exact Sum.inr_injective (Sum.inr_injective hrow)
          subst oj
          let c := U oi * uniformizerPowerUnit K (1 : Int)
          have hcOrder : ordUnit K c = 1 := by
            dsimp only [c]
            rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
              (isValuationUnit_iff_ordUnit_eq_zero K (U oi)).1 (hU.isUnit oi)]
            norm_num
          have hcOdd : Odd (ordUnit K c) := by
            rw [hcOrder]
            exact odd_one
          cases ci <;> cases cj
          · rfl
          · have hforbidden :=
              (heClassicEvenC_oddOrder_pairProperties
                (K := K) pairs c hcOdd).nonisometric
            exact False.elim (hforbidden (by
              simpa [coefficients, c] using
                hrep.symm_of_sameRank))
          · have hforbidden :=
              (heClassicEvenC_oddOrder_pairProperties
                (K := K) pairs c hcOdd).nonisometric
            exact False.elim (hforbidden (by
              simpa [coefficients, c] using hrep))
          · rfl

/-- Contrapositive form used by literal deletion witnesses. -/
theorem not_diagonalRepresents_coefficients_of_ne
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat}
    {i j : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)} (hne : i ≠ j) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (coefficients (K := K) U pairs i))
      (diagonalUnitCoefficients (coefficients (K := K) U pairs j)) := by
  intro hrep
  exact hne (eq_of_diagonalRepresents_coefficients U hU hrep)

/-- The literal coefficient row satisfies Beli's adjacent admissibility
criterion. -/
theorem coefficients_adjacentAdmissible
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    BONG.CoefficientAdjacentAdmissible (coefficients (K := K) U pairs i) := by
  rcases i with h | i
  · exact heClassicEvenH_adjacentAdmissible pairs
      (HeClassicExceptionalIndex.parameter (K := K) h)
      (HeClassicExceptionalIndex.parameter_class (K := K) h)
  · rcases i with j | i
    · rcases j with ⟨j, column⟩
      have hc : 0 ≤ ordUnit K (U j.1) := by
        rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit j.1)]
      cases column
      · exact heClassicEvenC1_adjacentAdmissible pairs (U j.1) hc
      · exact heClassicEvenC2_adjacentAdmissible pairs (U j.1)
          (heClassicDefectOneSharp (K := K) (U j.1) j.2) hc
          (heClassicDefectOneSharp_order (U j.1) j.2)
    · rcases i with ⟨i, column⟩
      let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : 0 ≤ ordUnit K c := by
        dsimp only [c]
        rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
          (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
        norm_num
      let delta :=
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit
      have hdelta : ordUnit K delta = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminant_isValuationUnit
      cases column
      · exact heClassicEvenC1_adjacentAdmissible pairs c hc
      · exact heClassicEvenC2_adjacentAdmissible pairs c delta hc hdelta

/-- The literal coefficient row satisfies Beli's weak two-step criterion. -/
theorem coefficients_weakTwoStep
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    BONG.CoefficientWeakTwoStep (K := K)
      (coefficients (K := K) U pairs i) := by
  rcases i with h | i
  · exact heClassicEvenH_weakTwoStep pairs
      (HeClassicExceptionalIndex.parameter (K := K) h)
      (HeClassicExceptionalIndex.parameter_order (K := K) h)
  · rcases i with j | i
    · rcases j with ⟨j, column⟩
      have hc : 0 ≤ ordUnit K (U j.1) := by
        rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit j.1)]
      cases column
      · exact heClassicEvenC1_weakTwoStep pairs (U j.1) hc
      · exact heClassicEvenC2_weakTwoStep pairs (U j.1)
          (heClassicDefectOneSharp (K := K) (U j.1) j.2) hc
          (heClassicDefectOneSharp_order (U j.1) j.2)
    · rcases i with ⟨i, column⟩
      let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : 0 ≤ ordUnit K c := by
        dsimp only [c]
        rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
          (isValuationUnit_iff_ordUnit_eq_zero K (U i)).1 (hU.isUnit i)]
        norm_num
      let delta :=
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit
      have hdelta : ordUnit K delta = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminant_isValuationUnit
      cases column
      · exact heClassicEvenC1_weakTwoStep pairs c hc
      · exact heClassicEvenC2_weakTwoStep pairs c delta hc hdelta

/-- Exact model reconstructed uniformly from the displayed coefficient row. -/
noncomputable def exactModel
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (coefficients (K := K) U pairs i)
    (coefficients_adjacentAdmissible U hU pairs i)
    (coefficients_weakTwoStep U hU pairs i)

/-- The uniform reconstruction is the model already attached to the table. -/
theorem exactModel_eq_model
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    exactModel (K := K) U hU pairs i = model (K := K) U hU pairs i := by
  rcases i with h | i
  · rfl
  · rcases i with j | i
    · rcases j with ⟨j, column⟩
      cases column <;> rfl
    · rcases i with ⟨i, column⟩
      cases column <;> rfl

/-- The canonical good BONG reconstructed from a displayed even table row. -/
noncomputable def exactModelGoodBONG
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K)) :
    BONG.GoodBONG
      (BONG.coefficientDiagonalSpace (coefficients (K := K) U pairs i))
      (heHuExactRealization (coefficients (K := K) U pairs i)
        (coefficients_adjacentAdmissible U hU pairs i)
        (coefficients_weakTwoStep U hU pairs i)).lattice
      (2 * pairs + 2) :=
  heHuExactGoodBONG (coefficients (K := K) U pairs i)
    (coefficients_adjacentAdmissible U hU pairs i)
    (coefficients_weakTwoStep U hU pairs i)

end HeClassicPublishedEvenTestingIndex

end Bong
