/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankFourOdd

/-!
# O'Meara 93:18(vi): the determinant-one odd quaternary models

For an odd quaternary unimodular lattice whose refined determinant class is
one, O'Meara 93:18(vi) leaves exactly two integral models:

* `A(a, 0) ⊥ A(b, 0)`, whose space is isotropic;
* `A(a, 4 rho / a) ⊥ A(b, 4 rho / b)`, whose space is anisotropic.

This file constructs the two models with `alpha = 0` from the ordinary
norm/weight ideal data and proves the model dichotomy by the already
formalized diagonal local classification and O'Meara 93:16.  In particular,
there is no new law interface in this statement.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

namespace Omeara9318RankFourModelParameters

/-- Replace the determinant error `alpha` by zero while retaining the two
norm/weight generators.  The ideal hypotheses of the general rank-four
model imply all hypotheses of the determinant-one specialization. -/
noncomputable def zeroDiscriminant
    (P : Omeara9318RankFourModelParameters K) :
    Omeara9318RankFourModelParameters K :=
  omeara9318RankFourModelParametersOfAlphaIdeal
    P.a P.b 0
    (by simp [IsInMaximalIdeal])
    P.a_integral P.b_integral P.bIdeal_le_aIdeal P.twoIdeal_le_bIdeal
    (by rw [principalIdeal]; simp)
    P.odd_orders

@[simp]
theorem zeroDiscriminant_a
    (P : Omeara9318RankFourModelParameters K) :
    P.zeroDiscriminant.a = P.a :=
  rfl

@[simp]
theorem zeroDiscriminant_b
    (P : Omeara9318RankFourModelParameters K) :
    P.zeroDiscriminant.b = P.b :=
  rfl

@[simp]
theorem zeroDiscriminant_alpha
    (P : Omeara9318RankFourModelParameters K) :
    P.zeroDiscriminant.alpha = 0 := by
  simp [zeroDiscriminant,
    omeara9318RankFourModelParametersOfAlphaIdeal]

@[simp]
theorem zeroDiscriminant_d_coe
    (P : Omeara9318RankFourModelParameters K) :
    (P.zeroDiscriminant.d : K) = 1 := by
  simp [Omeara9318RankFourModelParameters.d,
    zeroDiscriminant_alpha, coe_omeara9318DiscriminantUnit]

end Omeara9318RankFourModelParameters

private theorem isSquare_mul_of_squareClass_eq_detOne (x y : Kˣ)
    (h : squareClass K x = squareClass K y) : IsSquare (x * y) := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) x =
    QuotientGroup.mk' (Subgroup.square Kˣ) y at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hxz⟩
  change IsSquare z at hz
  have hxSquare : IsSquare (x ^ 2) := ⟨x, pow_two x⟩
  have hproduct : IsSquare (x ^ 2 * z) := hxSquare.mul hz
  have heq : x * y = x ^ 2 * z := by
    rw [← hxz]
    simpa only [pow_two] using (mul_assoc x x z).symm
  rw [heq]
  exact hproduct

private theorem intUnit_eq_or_eq_neg_detOne (x y : ℤˣ) :
    x = y ∨ x = -y := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy <;>
      simp [hx, hy]

/-- The determinant-one specialization of O'Meara 93:18(vi) in the odd
norm/weight branch.  The shared parameters have literal `alpha = 0`, so the
two outputs are exactly the untwisted and `rho`-twisted displayed models.
-/
structure Omeara9318viOddData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  parameters : Omeara9318RankFourModelParameters K
  parameters_a : parameters.a = a
  parameters_b : parameters.b =
    uniformizerPowerUnit K (weightIdealOrder q L)
  alpha_zero : parameters.alpha = 0
  isometric_j_or_k :
    IsIsometric q parameters.jData.space L parameters.jData.lattice ∨
      IsIsometric q parameters.kData.space L parameters.kData.lattice
  not_both : ¬
    (IsIsometric q parameters.jData.space L parameters.jData.lattice ∧
      IsIsometric q parameters.kData.space L parameters.kData.lattice)

set_option maxHeartbeats 3000000 in

/-- Construct the exact two-model output of 93:18(vi) in the odd branch.
The determinant hypothesis is the refined determinant class used throughout
the integral theory, not a chosen-basis equality. -/
noncomputable def omeara9318viOddData
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L))
    (hdet : determinantClass q L = 1) :
    Omeara9318viOddData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let C := omeara9318RankFourCongruenceData
    hmodular hrank a ha hodd
  let P := C.parameters.zeroDiscriminant
  let actual := q.diagonalUnits
  let j := P.jData.diagonalUnits
  let k := P.kData.diagonalUnits
  let latticeBONG := BONG.ofLattice q L
  have hactualSquareClass :
      squareClass K (diagonalUnitDeterminant actual) = squareClass K (1 : Kˣ) := by
    calc
      squareClass K (diagonalUnitDeterminant actual) =
          squareClass K q.diagonalizingBONG.valueProduct := by
        apply congrArg (squareClass K)
        apply Units.ext
        simp [actual, diagonalUnitDeterminant,
          QuadraticSpace.diagonalUnits]
      _ = squareClass K latticeBONG.valueProduct :=
        (BONG.valueProduct_squareClass_eq
          latticeBONG q.diagonalizingBONG).symm
      _ = unitSquareClassToSquareClass K (determinantClass q L) :=
        (determinantClass_toSquareClass_eq_valueProduct latticeBONG).symm
      _ = unitSquareClassToSquareClass K 1 := by rw [hdet]
      _ = squareClass K (1 : Kˣ) := by
        rfl
  have hjSquareClass :
      squareClass K (diagonalUnitDeterminant j) = squareClass K (1 : Kˣ) := by
    change squareClass K
      (diagonalUnitDeterminant P.jData.diagonalUnits) =
        squareClass K (1 : Kˣ)
    rw [P.jData_diagonalUnits_eq, P.jDiagonalUnitDeterminant_eq_d]
    apply congrArg (squareClass K)
    apply Units.ext
    exact P.zeroDiscriminant_d_coe
  have hdetJ : IsSquare
      (diagonalUnitDeterminant actual * diagonalUnitDeterminant j) :=
    isSquare_mul_of_squareClass_eq_detOne _ _
      (hactualSquareClass.trans hjSquareClass.symm)
  have hdetK : IsSquare
      (diagonalUnitDeterminant actual * diagonalUnitDeterminant k) := by
    apply isSquare_mul_trans
      (diagonalUnitDeterminant actual)
      (diagonalUnitDeterminant j)
      (diagonalUnitDeterminant k)
    · exact hdetJ
    · change IsSquare
        (diagonalUnitDeterminant P.jData.diagonalUnits *
          diagonalUnitDeterminant P.kData.diagonalUnits)
      rw [P.jData_diagonalUnits_eq, P.kData_diagonalUnits_eq]
      exact P.modelDeterminants_product_isSquare
  have hgroupJ : normGroupSet q L =
      normGroupSet P.jData.space P.jData.lattice := by
    calc
      normGroupSet q L =
          integralSquareCoset (a : K)
            (principalIdeal (K := K) (C.parameters.b : K)) :=
        C.normGroupSet_eq_common
      _ = integralSquareCoset (P.a : K)
            (principalIdeal (K := K) (P.b : K)) := by
        have haP : P.a = a :=
          C.parameters.zeroDiscriminant_a.trans C.parameters_a
        have hbP : P.b = C.parameters.b :=
          C.parameters.zeroDiscriminant_b
        rw [haP, hbP]
      _ = normGroupSet P.jData.space P.jData.lattice :=
        P.j_normGroupSet_eq.symm
  have hgroupK : normGroupSet q L =
      normGroupSet P.kData.space P.kData.lattice := by
    calc
      normGroupSet q L =
          integralSquareCoset (a : K)
            (principalIdeal (K := K) (C.parameters.b : K)) :=
        C.normGroupSet_eq_common
      _ = integralSquareCoset (P.a : K)
            (principalIdeal (K := K) (P.b : K)) := by
        have haP : P.a = a :=
          C.parameters.zeroDiscriminant_a.trans C.parameters_a
        have hbP : P.b = C.parameters.b :=
          C.parameters.zeroDiscriminant_b
        rw [haP, hbP]
      _ = normGroupSet P.kData.space P.kData.lattice :=
        P.k_normGroupSet_eq.symm
  have hchoice := intUnit_eq_or_eq_neg_detOne
    (diagonalHasseSymbol K actual)
    (diagonalHasseSymbol K j)
  have hisometric :
      IsIsometric q P.jData.space L P.jData.lattice ∨
        IsIsometric q P.kData.space L P.kData.lattice := by
    rcases hchoice with hj | hj
    · left
      let f := rankFourFieldIsometryOfExplicitDiagonal
        q P.jData.space hrank j P.jData.diagonalizationIsometry
          hdetJ hj
      exact ⟨latticeIsometryToUnimodularModel
        hmodular P.jData.isModular f hgroupJ⟩
    · right
      have hk : diagonalHasseSymbol K actual =
          diagonalHasseSymbol K k := by
        calc
          diagonalHasseSymbol K actual =
              -diagonalHasseSymbol K j := hj
          _ = diagonalHasseSymbol K k := P.k_hasse_eq_neg_j_hasse.symm
      let f := rankFourFieldIsometryOfExplicitDiagonal
        q P.kData.space hrank k P.kData.diagonalizationIsometry
          hdetK hk
      exact ⟨latticeIsometryToUnimodularModel
        hmodular P.kData.isModular f hgroupK⟩
  exact
    { parameters := P
      parameters_a := by
        exact P.zeroDiscriminant_a.trans C.parameters_a
      parameters_b := by
        exact P.zeroDiscriminant_b.trans C.parameters_b
      alpha_zero := P.zeroDiscriminant_alpha
      isometric_j_or_k := hisometric
      not_both := by
        rintro ⟨hj, hk⟩
        exact P.j_not_isometric_k
          ⟨((Classical.choice hj).symm.trans
            (Classical.choice hk)).toQuadraticSpaceIsometry⟩ }

end Lattice

end Bong
