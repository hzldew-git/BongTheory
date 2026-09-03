/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma29
import Bong.Bong.HeHu2022PublishedTestingSet
import Bong.Bong.HeHu2022Lemma45
import Bong.Dyadic.ResidueArtinSchreier

/-!
# He (2024), Definition 2.6 and Proposition 2.8: the finite published table

This file gives a literal finite index for the set `C_e^n` displayed in
Definition 2.6 of Zilong He, *On classic n-universal quadratic forms over
dyadic local fields*, manuscripta math. 174 (2024), 559--595.

For even rank the three summands are, in the order printed in the paper:

* the exceptional `H_e` row (one entry, or two when `e = 1`);
* the two `C_1/C_2` columns for unit classes of defect one;
* the two `C_1/C_2` columns for the parameters `delta*pi`.

For odd rank there are two valuation parities and two columns for every
unit square class.  The cardinality input quoted in the paper from O'Meara
63:5 and 63:9 is isolated in `HeClassicPublishedCountingLaws`; it contains
no lattice-classification or universality assertion.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The residue-field norm `N p` occurring in Proposition 2.8(ii). -/
noncomputable def heClassicResidueNorm : Nat := by
  letI := Fintype.ofFinite (normalizedResidueField K)
  exact Fintype.card (normalizedResidueField K)

/-- The subset `U_1` of the published unit representatives: precisely the
classes whose relative quadratic defect is one. -/
abbrev HeClassicDefectOneIndex {I : Type u} (U : I -> Kˣ) :=
  {i : I // defectOrder (K := K) (U i) = (1 : WithTop ℚ)}

/-- O'Meara 63:5 and 63:9, in exactly the two finite-cardinality forms used
in the proof of He, Proposition 2.8(ii).  The second equality says that the
defect-one representatives together with the `2 (N p)^(e-1)` classes of
defect greater than one exhaust `U`.

This interface deliberately stops at field square-class counting; it does
not assume any statement about classic maximal lattices, testing sets, or
universality. -/
class HeClassicPublishedCountingLaws : Prop where
  card_unit_representatives
      {I : Type u} [Fintype I] (U : I -> Kˣ)
      (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card I =
      2 * heClassicResidueNorm (K := K) ^ ramificationIndex K
  card_defect_one_balance
      {I : Type u} [Fintype I] (U : I -> Kˣ)
      (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    letI := Fintype.ofFinite (HeClassicDefectOneIndex (K := K) U)
    Fintype.card (HeClassicDefectOneIndex (K := K) U) +
        2 * heClassicResidueNorm (K := K) ^ (ramificationIndex K - 1) =
      2 * heClassicResidueNorm (K := K) ^ ramificationIndex K

/-- The exceptional even-rank row.  `false` is `H_e^n(1)` and `true` is
`H_1^n(Delta)`, which is present only when `e = 1`. -/
abbrev HeClassicExceptionalIndex (e : Nat) :=
  {b : Bool // b = false ∨ e = 1}

/-- The finite even-rank table `C_e^n`. -/
abbrev HeClassicPublishedEvenTestingIndex {I : Type u}
    (U : I -> Kˣ) (e : Nat) :=
  HeClassicExceptionalIndex e ⊕
    ((HeClassicDefectOneIndex (K := K) U × Bool) ⊕ (I × Bool))

/-- The finite odd-rank table `C_e^n`: valuation parity, then column. -/
abbrev HeClassicPublishedOddTestingIndex (I : Type u) :=
  (I × Bool) × Bool

noncomputable instance heClassicDefectOneIndexFintype
    {I : Type u} [Fintype I] (U : I -> Kˣ) :
    Fintype (HeClassicDefectOneIndex (K := K) U) :=
  Fintype.ofFinite _

noncomputable instance heClassicExceptionalIndexFintype (e : Nat) :
    Fintype (HeClassicExceptionalIndex e) :=
  Fintype.ofFinite _

/-- When `e = 1`, both exceptional rows are present. -/
noncomputable def heClassicExceptionalEquivBool {e : Nat} (he : e = 1) :
    HeClassicExceptionalIndex e ≃ Bool where
  toFun x := x.1
  invFun b := ⟨b, by simp [he]⟩
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl

/-- When `e != 1`, only `H_e^n(1)` is present. -/
noncomputable def heClassicExceptionalEquivUnit {e : Nat} (he : e ≠ 1) :
    HeClassicExceptionalIndex e ≃ Unit where
  toFun _ := Unit.unit
  invFun _ := ⟨false, Or.inl rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x.2 with hx | hx
    · exact hx.symm
    · exact (he hx).elim
  right_inv _ := rfl

theorem card_heClassicExceptionalIndex (e : Nat) :
    Fintype.card (HeClassicExceptionalIndex e) =
      if e = 1 then 2 else 1 := by
  classical
  by_cases he : e = 1
  · rw [if_pos he, Fintype.card_congr (heClassicExceptionalEquivBool he)]
    decide
  · rw [if_neg he,
      Fintype.card_congr (heClassicExceptionalEquivUnit he)]
    decide

/-- The combinatorial cardinality of the even published table, before
substituting the two local square-class counts. -/
theorem card_heClassicPublishedEvenTestingIndex
    {I : Type u} [Fintype I] (U : I -> Kˣ) (e : Nat) :
    Fintype.card (HeClassicPublishedEvenTestingIndex (K := K) U e) =
      (if e = 1 then 2 else 1) +
        2 * Fintype.card (HeClassicDefectOneIndex (K := K) U) +
        2 * Fintype.card I := by
  classical
  simp only [HeClassicPublishedEvenTestingIndex, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_bool]
  rw [card_heClassicExceptionalIndex]
  omega

/-- Proposition 2.8(ii), even rank and `e > 1`. -/
theorem he2022ClassicProposition28ii_even_gt_one
    [HeClassicPublishedCountingLaws (K := K)]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (he : 1 < ramificationIndex K) :
    Fintype.card
        (HeClassicPublishedEvenTestingIndex (K := K) U
          (ramificationIndex K)) =
      8 * heClassicResidueNorm (K := K) ^ ramificationIndex K -
        4 * heClassicResidueNorm (K := K) ^ (ramificationIndex K - 1) + 1 := by
  classical
  rw [card_heClassicPublishedEvenTestingIndex]
  have hene : ramificationIndex K ≠ 1 := by omega
  rw [if_neg hene]
  have hUcard :=
    HeClassicPublishedCountingLaws.card_unit_representatives
      (K := K) U hU
  have hU1card :=
    HeClassicPublishedCountingLaws.card_defect_one_balance
      (K := K) U hU
  omega

/-- Proposition 2.8(ii), even rank and `e = 1`. -/
theorem he2022ClassicProposition28ii_even_eq_one
    [HeClassicPublishedCountingLaws (K := K)]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (he : ramificationIndex K = 1) :
    Fintype.card
        (HeClassicPublishedEvenTestingIndex (K := K) U
          (ramificationIndex K)) =
      8 * heClassicResidueNorm (K := K) ^ ramificationIndex K -
        4 * heClassicResidueNorm (K := K) ^ (ramificationIndex K - 1) + 2 := by
  classical
  rw [card_heClassicPublishedEvenTestingIndex, if_pos he]
  have hUcard :=
    HeClassicPublishedCountingLaws.card_unit_representatives
      (K := K) U hU
  have hU1card :=
    HeClassicPublishedCountingLaws.card_defect_one_balance
      (K := K) U hU
  omega

/-- The odd table has four entries for each element of `U`. -/
theorem card_heClassicPublishedOddTestingIndex
    (I : Type u) [Fintype I] :
    Fintype.card (HeClassicPublishedOddTestingIndex I) =
      4 * Fintype.card I := by
  simp [HeClassicPublishedOddTestingIndex]
  omega

/-- Proposition 2.8(ii), odd rank. -/
theorem he2022ClassicProposition28ii_odd
    [HeClassicPublishedCountingLaws (K := K)]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeClassicPublishedOddTestingIndex I) =
      8 * heClassicResidueNorm (K := K) ^ ramificationIndex K := by
  rw [card_heClassicPublishedOddTestingIndex,
    HeClassicPublishedCountingLaws.card_unit_representatives
      (K := K) U hU]
  ring

/-! ## Exact bundled models for the six displayed coefficient rows -/

namespace Lattice.QuadraticLatticeModel

/-- Classic integrality of a bundled lattice. -/
def IsClassicIntegral (X : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsClassicIntegral X.form X.lattice

end Lattice.QuadraticLatticeModel

/-- Bundle the exact good-BONG realization of `C_1^(2p+2)(c)`. -/
noncomputable def heClassicEvenC1Model
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC1_adjacentAdmissible pairs c hc)
    (heClassicEvenC1_weakTwoStep pairs c hc)

/-- Bundle the exact good-BONG realization of `C_2^(2p+2)(c)`. -/
noncomputable def heClassicEvenC2Model
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicEvenC2 (K := K) pairs c cSharp)
    (heClassicEvenC2_adjacentAdmissible pairs c cSharp hc hcSharp)
    (heClassicEvenC2_weakTwoStep pairs c cSharp hc hcSharp)

/-- Bundle the exact good-BONG realization of `C_1^(2p+3)(c)`. -/
noncomputable def heClassicOddC1Model
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicOddC1 (K := K) pairs c)
    (heClassicOddC1_adjacentAdmissible pairs c hc)
    (heClassicOddC1_weakTwoStep pairs c hc)

/-- Bundle the exact odd-order realization of `C_2^(2p+3)(c)`. -/
noncomputable def heClassicOddC2OddModel
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicOddC2Odd (K := K) pairs c)
    (heClassicOddC2Odd_adjacentAdmissible pairs c hc)
    (heClassicOddC2Odd_weakTwoStep pairs c hc)

/-- Bundle the exact even-order realization of `C_2^(2p+3)(c)`. -/
noncomputable def heClassicOddC2EvenModel
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel
    (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
    (heClassicOddC2Even_adjacentAdmissible pairs c omega omegaSharp hc
      homega homegaSharp)
    (heClassicOddC2Even_weakTwoStep pairs c omega omegaSharp hc homega
      homegaSharp)

/-- Bundle the exact exceptional `H_e` realization. -/
noncomputable def heClassicEvenHModel
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuExactModel (heClassicEvenH (K := K) pairs c)
    (heClassicEvenH_adjacentAdmissible pairs c hcClass)
    (heClassicEvenH_weakTwoStep pairs c hcOrder)

@[simp] theorem heClassicEvenC1Model_rank
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicEvenC1Model (K := K) pairs c hc).rank = 2 * pairs + 2 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicEvenC2Model_rank
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp).rank =
      2 * pairs + 2 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicOddC1Model_rank
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicOddC1Model (K := K) pairs c hc).rank = 2 * pairs + 3 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicOddC2OddModel_rank
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicOddC2OddModel (K := K) pairs c hc).rank = 2 * pairs + 3 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicOddC2EvenModel_rank
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    (heClassicOddC2EvenModel (K := K) pairs c omega omegaSharp hc homega
      homegaSharp).rank = 2 * pairs + 3 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicEvenHModel_rank
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    (heClassicEvenHModel (K := K) pairs c hcClass hcOrder).rank =
      2 * pairs + 2 :=
  heHuExactModel_rank _ _ _

@[simp] theorem heClassicEvenC1Model_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicEvenC1Model (K := K) pairs c hc).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace (heClassicEvenC1 (K := K) pairs c))
    (heHuExactRealization (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC1_adjacentAdmissible pairs c hc)
      (heClassicEvenC1_weakTwoStep pairs c hc)).lattice
  exact heClassicEvenC1_isClassicIntegral (K := K) pairs c hc

@[simp] theorem heClassicEvenC2Model_isClassicIntegral
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    (heClassicEvenC2Model (K := K) pairs c cSharp hc hcSharp).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (heHuExactRealization (heClassicEvenC2 (K := K) pairs c cSharp)
      (heClassicEvenC2_adjacentAdmissible pairs c cSharp hc hcSharp)
      (heClassicEvenC2_weakTwoStep pairs c cSharp hc hcSharp)).lattice
  exact heClassicEvenC2_isClassicIntegral (K := K) pairs c cSharp hc
    hcSharp

@[simp] theorem heClassicOddC1Model_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicOddC1Model (K := K) pairs c hc).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace (heClassicOddC1 (K := K) pairs c))
    (heHuExactRealization (heClassicOddC1 (K := K) pairs c)
      (heClassicOddC1_adjacentAdmissible pairs c hc)
      (heClassicOddC1_weakTwoStep pairs c hc)).lattice
  exact heClassicOddC1_isClassicIntegral (K := K) pairs c hc

@[simp] theorem heClassicOddC2OddModel_isClassicIntegral
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    (heClassicOddC2OddModel (K := K) pairs c hc).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace (heClassicOddC2Odd (K := K) pairs c))
    (heHuExactRealization (heClassicOddC2Odd (K := K) pairs c)
      (heClassicOddC2Odd_adjacentAdmissible pairs c hc)
      (heClassicOddC2Odd_weakTwoStep pairs c hc)).lattice
  exact heClassicOddC2Odd_isClassicIntegral (K := K) pairs c hc

@[simp] theorem heClassicOddC2EvenModel_isClassicIntegral
    (pairs : Nat) (c omega omegaSharp : Kˣ)
    (hc : ordUnit K c = 0) (homega : ordUnit K omega = 0)
    (homegaSharp : ordUnit K omegaSharp = 0) :
    (heClassicOddC2EvenModel (K := K) pairs c omega omegaSharp hc homega
      homegaSharp).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp))
    (heHuExactRealization
      (heClassicOddC2Even (K := K) pairs c omega omegaSharp)
      (heClassicOddC2Even_adjacentAdmissible pairs c omega omegaSharp hc
        homega homegaSharp)
      (heClassicOddC2Even_weakTwoStep pairs c omega omegaSharp hc homega
        homegaSharp)).lattice
  exact heClassicOddC2Even_isClassicIntegral (K := K) pairs c omega
    omegaSharp hc homega homegaSharp

@[simp] theorem heClassicEvenHModel_isClassicIntegral
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    (heClassicEvenHModel (K := K) pairs c hcClass hcOrder).IsClassicIntegral := by
  change Lattice.IsClassicIntegral
    (BONG.coefficientDiagonalSpace (heClassicEvenH (K := K) pairs c))
    (heHuExactRealization (heClassicEvenH (K := K) pairs c)
      (heClassicEvenH_adjacentAdmissible pairs c hcClass)
      (heClassicEvenH_weakTwoStep pairs c hcOrder)).lattice
  exact heClassicEvenH_isClassicIntegral (K := K) pairs c hcClass hcOrder

/-! ## Canonical sharp choices and the literal finite families -/

/-- A defect-one unit lies in the domain of the sharp construction (2.9).
The strict inequality is automatic from dyadicity, since `e >= 1`. -/
theorem heClassicSharpDomain_of_defect_one (c : Kˣ)
    (hc : defectOrder (K := K) c = (1 : WithTop ℚ)) :
    HeHuSharpDomain c := by
  apply heHuLemma45_sharpDomain_of_defect_lt_twoE c 1
  · simpa using hc
  · have he := ramificationIndex_pos (K := K)
    omega

/-- The `c#` used in the defect-one row of Definition 2.6. -/
noncomputable def heClassicDefectOneSharp (c : Kˣ)
    (hc : defectOrder (K := K) c = (1 : WithTop ℚ)) : Kˣ :=
  heHuSharp c (heClassicSharpDomain_of_defect_one c hc)

theorem heClassicDefectOneSharp_order (c : Kˣ)
    (hc : defectOrder (K := K) c = (1 : WithTop ℚ)) :
    ordUnit K (heClassicDefectOneSharp (K := K) c hc) = 0 := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K _).1
  exact (heHu2022Proposition32 c
    (heClassicSharpDomain_of_defect_one c hc)).1

/-- The two distinguished units `omega = 1+pi` and
`omega# = 1+4*rho*pi^(-1)` from Definition 2.6, together with exactly the
properties used in Sections 2 and 7.  The value equalities prevent an
arbitrary defect-one pair from being substituted for the printed choices. -/
structure HeClassicOmegaData where
  omega : Kˣ
  omegaSharp : Kˣ
  omega_value : (omega : K) = 1 + uniformizer K
  omegaSharp_value :
    (omegaSharp : K) =
      1 + 4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹
  omega_order : ordUnit K omega = 0
  omegaSharp_order : ordUnit K omegaSharp = 0
  omega_defect : defectOrder (K := K) omega = (1 : WithTop ℚ)

namespace HeClassicExceptionalIndex

/-- The determinant parameter of an exceptional row. -/
noncomputable def parameter {e : Nat} (i : HeClassicExceptionalIndex e) : Kˣ :=
  if i.1 then
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  else 1

theorem parameter_class {e : Nat} (i : HeClassicExceptionalIndex e) :
    parameter (K := K) i = 1 ∨
      parameter (K := K) i =
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit := by
  cases h : i.1 <;> simp [parameter, h]

theorem parameter_order {e : Nat} (i : HeClassicExceptionalIndex e) :
    ordUnit K (parameter (K := K) i) = 0 := by
  rcases parameter_class (K := K) i with h | h
  · rw [h]
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  · rw [h]
    exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
      ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)

end HeClassicExceptionalIndex

private theorem heClassicUnitRepresentative_order_zero
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i) = 0 :=
  (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)

private theorem heClassicUnitUniformizerParameter_order_one
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) (i : I) :
    ordUnit K (U i * uniformizerPowerUnit K (1 : Int)) = 1 := by
  rw [ordUnit_mul, heClassicUnitRepresentative_order_zero U hU i,
    ordUnit_uniformizerPowerUnit]
  norm_num

namespace HeClassicPublishedEvenTestingIndex

/-- The exact bundled lattice attached to a row of the even table in
Definition 2.6.  `false/true` in either product selects the `C_1/C_2`
column respectively. -/
noncomputable def model {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) :
    HeClassicPublishedEvenTestingIndex (K := K) U (ramificationIndex K) ->
      Lattice.QuadraticLatticeModel (K := K)
  | .inl h =>
      heClassicEvenHModel (K := K) pairs
        (HeClassicExceptionalIndex.parameter (K := K) h)
        (HeClassicExceptionalIndex.parameter_class (K := K) h)
        (HeClassicExceptionalIndex.parameter_order (K := K) h)
  | .inr (.inl (j, column)) =>
      let c := U j.1
      let hc : ordUnit K c = 0 :=
        heClassicUnitRepresentative_order_zero U hU j.1
      let cSharp := heClassicDefectOneSharp (K := K) c j.2
      let hcSharp : ordUnit K cSharp = 0 :=
        heClassicDefectOneSharp_order c j.2
      if column then
        heClassicEvenC2Model (K := K) pairs c cSharp (by omega) hcSharp
      else
        heClassicEvenC1Model (K := K) pairs c (by omega)
  | .inr (.inr (i, column)) =>
      let c := U i * uniformizerPowerUnit K (1 : Int)
      let hc : ordUnit K c = 1 :=
        heClassicUnitUniformizerParameter_order_one U hU i
      let delta :=
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      let hdelta : ordUnit K delta = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1
          ((inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit)
      if column then
        heClassicEvenC2Model (K := K) pairs c delta (by omega) hdelta
      else
        heClassicEvenC1Model (K := K) pairs c (by omega)

@[simp] theorem model_rank {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    (model (K := K) U hU pairs i).rank = 2 * pairs + 2 := by
  rcases i with h | j
  · simp [model]
  · rcases j with j | i
    · rcases j with ⟨j, column⟩
      cases column <;> simp [model]
    · rcases i with ⟨i, column⟩
      cases column <;> simp [model]

/-- Proposition 2.8(iii), simultaneously for every even-rank row. -/
theorem model_isClassicIntegral {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat)
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    (model (K := K) U hU pairs i).IsClassicIntegral := by
  rcases i with h | j
  · simp [model]
  · rcases j with j | i
    · rcases j with ⟨j, column⟩
      cases column <;>
        simp [model]
    · rcases i with ⟨i, column⟩
      cases column <;>
        simp [model]

end HeClassicPublishedEvenTestingIndex

namespace HeClassicPublishedOddTestingIndex

/-- The exact bundled lattice attached to a row of the odd table.  The first
Boolean is valuation parity (`delta` or `delta*pi`) and the second is the
`C_1/C_2` column. -/
noncomputable def model {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat) :
    HeClassicPublishedOddTestingIndex I ->
      Lattice.QuadraticLatticeModel (K := K)
  | ((i, false), false) =>
      heClassicOddC1Model (K := K) pairs (U i)
        (by rw [heClassicUnitRepresentative_order_zero U hU i])
  | ((i, false), true) =>
      heClassicOddC2EvenModel (K := K) pairs (U i)
        omegaData.omega omegaData.omegaSharp
        (heClassicUnitRepresentative_order_zero U hU i)
        omegaData.omega_order omegaData.omegaSharp_order
  | ((i, true), false) =>
      let c := U i * uniformizerPowerUnit K (1 : Int)
      heClassicOddC1Model (K := K) pairs c
        (by rw [heClassicUnitUniformizerParameter_order_one U hU i]
            norm_num)
  | ((i, true), true) =>
      let c := U i * uniformizerPowerUnit K (1 : Int)
      heClassicOddC2OddModel (K := K) pairs c
        (by rw [heClassicUnitUniformizerParameter_order_one U hU i]
            norm_num)

@[simp] theorem model_rank {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    (model (K := K) U hU omegaData pairs i).rank = 2 * pairs + 3 := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  cases parity <;> cases column <;> simp [model]

/-- Proposition 2.8(iii), simultaneously for every odd-rank row. -/
theorem model_isClassicIntegral {I : Type u} [Fintype I]
    (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (i : HeClassicPublishedOddTestingIndex I) :
    (model (K := K) U hU omegaData pairs i).IsClassicIntegral := by
  rcases i with ⟨⟨i, parity⟩, column⟩
  cases parity <;> cases column <;> simp [model]

end HeClassicPublishedOddTestingIndex

end Bong
