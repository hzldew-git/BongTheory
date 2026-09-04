/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma29
import Bong.Bong.Beli2009FinalRemarksProof
import Bong.Bong.HeHu2022PublishedTestingSet
import Bong.Bong.HeHu2022Lemma45
import Bong.Dyadic.ResidueArtinSchreier
import Bong.Dyadic.UnitDefectClassification

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

/-! The paper fixes the two displayed units, rather than merely assuming
that suitable units exist.  The following construction verifies the exact
values directly from the selected uniformizer and discriminant datum. -/

private theorem heClassicOmegaRaw_order :
    ord K (1 + uniformizer K) = 0 := by
  have hstrict : ord K (1 : K) < ord K (uniformizer K) := by
    simp only [ord_one, ord_uniformizer]
    norm_num
  simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hstrict

private theorem heClassicOmegaRaw_ne_zero :
    (1 + uniformizer K : K) ≠ 0 := by
  apply (ord_eq_top_iff K).not.mp
  rw [heClassicOmegaRaw_order (K := K)]
  exact WithTop.coe_ne_top

/-- The literal unit `omega = 1 + pi` from Definition 2.6. -/
noncomputable def heClassicOmega : Kˣ :=
  Units.mk0 (1 + uniformizer K) (heClassicOmegaRaw_ne_zero (K := K))

@[simp] theorem heClassicOmega_value :
    (heClassicOmega (K := K) : K) = 1 + uniformizer K := rfl

theorem heClassicOmega_order :
    ordUnit K (heClassicOmega (K := K)) = 0 := by
  apply WithTop.coe_injective
  rw [coe_ordUnit, heClassicOmega_value,
    heClassicOmegaRaw_order (K := K)]
  norm_num

/-- The exact quadratic defect of `1 + pi` is one.  This is the `d = 1`
specialization of the odd-defect construction in the local-field layer,
retained here with its literal value so Definition 2.6 can be audited. -/
theorem heClassicOmega_quadraticDefect :
    quadraticDefect K (heClassicOmega (K := K)) = (1 : ℕ∞) := by
  let u : Kˣ := heClassicOmega (K := K)
  have huUnit : IsValuationUnit K (u : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).2
      (heClassicOmega_order (K := K))
  have hlower : (1 : ℕ∞) ≤ quadraticDefect K u := by
    apply natCast_le_quadraticDefect K
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / (u : K) =
        uniformizer K / (u : K) := by
      change 1 - (1 : K) ^ 2 / (1 + uniformizer K) =
        uniformizer K / (1 + uniformizer K)
      field_simp [heClassicOmegaRaw_ne_zero (K := K)]
      ring
    rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      huUnit, ord_uniformizer]
    norm_num
  have hupper : quadraticDefect K u ≤ (1 : ℕ∞) := by
    by_contra hnot
    have hstrict : (1 : ℕ∞) < quadraticDefect K u :=
      lt_of_not_ge hnot
    have hnext : (2 : ℕ∞) ≤ quadraticDefect K u := by
      have hadd : (1 : ℕ∞) + 1 ≤ quadraticDefect K u :=
        (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).2 hstrict
      norm_num at hadd ⊢
      exact hadd
    obtain ⟨y, hy⟩ :=
      (isQuadraticApproximation_iff_le_defect K).2 hnext
    have hdeep : ((2 : Int) : WithTop Int) ≤
        ord K ((u : K) - y ^ 2) := by
      have hfield : 1 - y ^ 2 / (u : K) =
          ((u : K) - y ^ 2) / (u : K) := by
        field_simp [Units.ne_zero u]
      rw [hfield, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        huUnit] at hy
      simp only [neg_zero, add_zero] at hy
      exact_mod_cast hy
    have hpiLt : ord K (uniformizer K) <
        ord K ((u : K) - y ^ 2) := by
      rw [ord_uniformizer]
      exact lt_of_lt_of_le (by norm_num) hdeep
    have horder : ord K (1 - y ^ 2) =
        ((1 : Int) : WithTop Int) := by
      have hsub := (ord K).map_sub_eq_of_lt_right hpiLt
      have hfield : ((u : K) - y ^ 2) - uniformizer K =
          1 - y ^ 2 := by
        change (1 + uniformizer K - y ^ 2) - uniformizer K =
          1 - y ^ 2
        ring
      rw [hfield, ord_uniformizer] at hsub
      convert hsub using 1 <;> norm_num
    have he := ramificationIndex_pos (K := K)
    have heven : Even (1 : Int) :=
      even_order_one_sub_sq_of_lt_two_mul_e_proved y (1 : Int) horder
        (by norm_num) (by exact_mod_cast (show 1 < 2 * ramificationIndex K by omega))
    norm_num at heven
  exact le_antisymm hupper hlower

theorem heClassicOmega_defect :
    defectOrder (K := K) (heClassicOmega (K := K)) =
      (1 : WithTop ℚ) := by
  simpa using
    (Beli2009FinalRemarksProof.defectOrder_eq_natCast_of_quadraticDefect_eq
      (K := K) (heClassicOmega (K := K)) 1
        (heClassicOmega_quadraticDefect (K := K)))

private theorem heClassicOmegaSharpCorrection_order :
    ord K (4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹) =
      (((ramificationIndex K : Int) + (ramificationIndex K : Int) -
        (1 : Int) : Int) : WithTop Int) := by
  rw [show (4 : K) = 2 * 2 by norm_num, mul_assoc, ord_mul, ord_mul,
    ord_mul,
    ← ramificationIndex_spec,
    (inferInstance : DyadicDiscriminantClassLaws K).rho_isValuationUnit,
    AddValuation.map_inv, ord_uniformizer]
  norm_cast

private theorem heClassicOmegaSharpRaw_order :
    ord K (1 + 4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹) = 0 := by
  have he := ramificationIndex_pos (K := K)
  have hpositive : (0 : WithTop Int) <
      ord K (4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹) := by
    rw [heClassicOmegaSharpCorrection_order (K := K)]
    norm_cast
    rw [Int.subNatNat_eq_coe]
    omega
  have hstrict : ord K (1 : K) <
      ord K (4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹) := by
    simpa only [ord_one] using hpositive
  simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hstrict

private theorem heClassicOmegaSharpRaw_ne_zero :
    (1 + 4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
      (uniformizer K)⁻¹ : K) ≠ 0 := by
  apply (ord_eq_top_iff K).not.mp
  rw [heClassicOmegaSharpRaw_order (K := K)]
  exact WithTop.coe_ne_top

/-- The literal unit `omega# = 1 + 4 rho pi^(-1)` from Definition 2.6. -/
noncomputable def heClassicOmegaSharp : Kˣ :=
  Units.mk0
    (1 + 4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
      (uniformizer K)⁻¹)
    (heClassicOmegaSharpRaw_ne_zero (K := K))

@[simp] theorem heClassicOmegaSharp_value :
    (heClassicOmegaSharp (K := K) : K) =
      1 + 4 * (inferInstance : DyadicDiscriminantClassLaws K).rho *
        (uniformizer K)⁻¹ := rfl

theorem heClassicOmegaSharp_order :
    ordUnit K (heClassicOmegaSharp (K := K)) = 0 := by
  apply WithTop.coe_injective
  rw [coe_ordUnit, heClassicOmegaSharp_value,
    heClassicOmegaSharpRaw_order (K := K)]
  norm_num

/-- The canonical pair used by every odd-rank row of Definition 2.6. -/
noncomputable def heClassicCanonicalOmegaData :
    HeClassicOmegaData (K := K) where
  omega := heClassicOmega (K := K)
  omegaSharp := heClassicOmegaSharp (K := K)
  omega_value := heClassicOmega_value (K := K)
  omegaSharp_value := heClassicOmegaSharp_value (K := K)
  omega_order := heClassicOmega_order (K := K)
  omegaSharp_order := heClassicOmegaSharp_order (K := K)
  omega_defect := heClassicOmega_defect (K := K)

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
