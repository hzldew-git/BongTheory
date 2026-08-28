/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma99Necessity
import Bong.Bong.Beli2019ComplementaryHilbertChoice
import Bong.Bong.Beli2019Lemma95NormalForm
import Bong.Bong.DiagonalOrthogonalBasis
import Bong.Bong.Beli2006SectionTwo

/-!
# Beli (2019), Lemma 9.9: explicit ternary coefficients

The three coefficient lists in the sufficiency proof are instances of the
single family

`[-π^R ξ ε, π^S ξ εη, -π^R ξη]`.

Here `ξ` is the normalized unit part of a reference determinant.  The choices
`(ε, η) = (1, 1)`, `η = 1`, and complementary unit defects respectively give
the even, odd-isotropic, and odd-anisotropic branches of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The unified coefficient list used in all three branches of Lemma 9.9. -/
noncomputable def beli2019Lemma99Values
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) : Fin 3 → Kˣ :=
  ![-(uniformizerPowerUnit K R *
        reference.ternaryDeterminantUnitPart * ε),
    uniformizerPowerUnit K S *
        reference.ternaryDeterminantUnitPart * ε * η,
    -(uniformizerPowerUnit K R *
        reference.ternaryDeterminantUnitPart * η)]

@[simp]
theorem beli2019Lemma99Values_zero
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    reference.beli2019Lemma99Values R S ε η 0 =
      -(uniformizerPowerUnit K R *
        reference.ternaryDeterminantUnitPart * ε) := by
  rfl

@[simp]
theorem beli2019Lemma99Values_one
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    reference.beli2019Lemma99Values R S ε η 1 =
      uniformizerPowerUnit K S *
        reference.ternaryDeterminantUnitPart * ε * η := by
  rfl

@[simp]
theorem beli2019Lemma99Values_two
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    reference.beli2019Lemma99Values R S ε η 2 =
      -(uniformizerPowerUnit K R *
        reference.ternaryDeterminantUnitPart * η) := by
  rfl

/-- Valuation-unit twists leave the prescribed order profile `[R,S,R]`. -/
theorem beli2019Lemma99Values_orders
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ∀ i, ordUnit K (reference.beli2019Lemma99Values R S ε η i) =
      ![R, S, R] i := by
  have hξOrder : ordUnit K reference.ternaryDeterminantUnitPart = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K
      reference.ternaryDeterminantUnitPart).1
      reference.ternaryDeterminantUnitPart_isValuationUnit
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  intro i
  fin_cases i <;>
    simp [beli2019Lemma99Values, ordUnit_neg, ordUnit_mul,
      ordUnit_uniformizerPowerUnit, hξOrder, hεOrder, hηOrder]

/-- Congruence modulo two makes the sum of the two orders even. -/
theorem beli2019Lemma99_evenOrderSum {R S : Int}
    (hparity : Int.ModEq 2 R S) : Even (R + S) := by
  rcases Int.modEq_iff_add_fac.mp hparity with ⟨t, ht⟩
  refine ⟨R + t, ?_⟩
  omega

/-- The first negative adjacent product, before removing square factors. -/
theorem beli2019Lemma99Values_firstAdjacentProduct
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    -(reference.beli2019Lemma99Values R S ε η 0 *
        reference.beli2019Lemma99Values R S ε η 1) =
      uniformizerPowerUnit K (R + S) *
        reference.ternaryDeterminantUnitPart ^ 2 * ε ^ 2 * η := by
  rw [beli2019Lemma99Values_zero, beli2019Lemma99Values_one]
  simp only [neg_mul, neg_neg]
  have hpower : uniformizerPowerUnit K R * uniformizerPowerUnit K S =
      uniformizerPowerUnit K (R + S) := by
    unfold uniformizerPowerUnit
    rw [← zpow_add]
  rw [show (uniformizerPowerUnit K R *
          reference.ternaryDeterminantUnitPart * ε) *
        (uniformizerPowerUnit K S *
          reference.ternaryDeterminantUnitPart * ε * η) =
      (uniformizerPowerUnit K R * uniformizerPowerUnit K S) *
        reference.ternaryDeterminantUnitPart ^ 2 * ε ^ 2 * η by
      simp only [pow_two]
      ac_rfl,
    hpower]

/-- The second negative adjacent product, before removing square factors. -/
theorem beli2019Lemma99Values_secondAdjacentProduct
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    -(reference.beli2019Lemma99Values R S ε η 1 *
        reference.beli2019Lemma99Values R S ε η 2) =
      uniformizerPowerUnit K (R + S) *
        reference.ternaryDeterminantUnitPart ^ 2 * ε * η ^ 2 := by
  rw [beli2019Lemma99Values_one, beli2019Lemma99Values_two]
  simp only [mul_neg, neg_neg]
  have hpower : uniformizerPowerUnit K S * uniformizerPowerUnit K R =
      uniformizerPowerUnit K (R + S) := by
    unfold uniformizerPowerUnit
    rw [← zpow_add]
    congr 1
    omega
  rw [show (uniformizerPowerUnit K S *
          reference.ternaryDeterminantUnitPart * ε * η) *
        (uniformizerPowerUnit K R *
          reference.ternaryDeterminantUnitPart * η) =
      (uniformizerPowerUnit K S * uniformizerPowerUnit K R) *
        reference.ternaryDeterminantUnitPart ^ 2 * ε * η ^ 2 by
      simp only [pow_two]
      ac_rfl,
    hpower]

/-- The first adjacent defect is exactly the defect of `η`. -/
theorem beli2019Lemma99Values_firstAdjacentDefect
    [QuadraticDefectLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S) :
    defectOrder (K := K)
        (-(reference.beli2019Lemma99Values R S ε η 0 *
          reference.beli2019Lemma99Values R S ε η 1)) =
      defectOrder (K := K) η := by
  have hsquare := isSquare_uniformizerPowerUnit_of_even
    (K := K) (R + S) (beli2019Lemma99_evenOrderSum hparity)
  rcases hsquare with ⟨s, hs⟩
  rw [reference.beli2019Lemma99Values_firstAdjacentProduct R S ε η,
    hs]
  have hfactor :
      s * s * reference.ternaryDeterminantUnitPart ^ 2 * ε ^ 2 * η =
        η * (s * reference.ternaryDeterminantUnitPart * ε) ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

/-- The second adjacent defect is exactly the defect of `ε`. -/
theorem beli2019Lemma99Values_secondAdjacentDefect
    [QuadraticDefectLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S) :
    defectOrder (K := K)
        (-(reference.beli2019Lemma99Values R S ε η 1 *
          reference.beli2019Lemma99Values R S ε η 2)) =
      defectOrder (K := K) ε := by
  have hsquare := isSquare_uniformizerPowerUnit_of_even
    (K := K) (R + S) (beli2019Lemma99_evenOrderSum hparity)
  rcases hsquare with ⟨s, hs⟩
  rw [reference.beli2019Lemma99Values_secondAdjacentProduct R S ε η,
    hs]
  have hfactor :
      s * s * reference.ternaryDeterminantUnitPart ^ 2 * ε * η ^ 2 =
        ε * (s * reference.ternaryDeterminantUnitPart * η) ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

/-- The determinant of the unified coefficient list. -/
theorem beli2019Lemma99Values_determinant_eq
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ) :
    diagonalUnitDeterminant
        (reference.beli2019Lemma99Values R S ε η) =
      uniformizerPowerUnit K (2 * R + S) *
        reference.ternaryDeterminantUnitPart ^ 3 * (ε * η) ^ 2 := by
  have hpower :
      uniformizerPowerUnit K R * uniformizerPowerUnit K S *
          uniformizerPowerUnit K R =
        uniformizerPowerUnit K (2 * R + S) := by
    unfold uniformizerPowerUnit
    rw [← zpow_add, ← zpow_add]
    congr 1
    omega
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_three, beli2019Lemma99Values_zero,
    beli2019Lemma99Values_one, beli2019Lemma99Values_two]
  simp only [neg_mul, mul_neg, neg_neg]
  rw [show
      (uniformizerPowerUnit K R *
          reference.ternaryDeterminantUnitPart * ε) *
        (uniformizerPowerUnit K S *
          reference.ternaryDeterminantUnitPart * ε * η) *
        (uniformizerPowerUnit K R *
          reference.ternaryDeterminantUnitPart * η) =
      (uniformizerPowerUnit K R * uniformizerPowerUnit K S *
          uniformizerPowerUnit K R) *
        reference.ternaryDeterminantUnitPart ^ 3 * (ε * η) ^ 2 by
      simp only [pow_succ, pow_zero]
      ac_rfl,
    hpower]

/-- The displayed and reference ternary forms have the same determinant
square class under the two parity hypotheses in Lemma 9.9. -/
theorem beli2019Lemma99Values_determinantSquare
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S)
    (hdeterminant : Int.ModEq 2
      (ordUnit K reference.toBONG.valueProduct) R) :
    IsSquare
      (diagonalUnitDeterminant
          (reference.beli2019Lemma99Values R S ε η) *
        diagonalUnitDeterminant reference.valueUnit) := by
  let T := ordUnit K reference.toBONG.valueProduct
  have hRS : Even (R + S) :=
    beli2019Lemma99_evenOrderSum hparity
  have hTR : Even (T + R) :=
    beli2019Lemma99_evenOrderSum hdeterminant
  have htotal : Even (2 * R + S + T) := by
    rcases hRS with ⟨r, hr⟩
    rcases hTR with ⟨t, ht⟩
    refine ⟨r + t, ?_⟩
    dsimp only [T] at ht ⊢
    omega
  have hsquarePower := isSquare_uniformizerPowerUnit_of_even
    (K := K) (2 * R + S + T) htotal
  rcases hsquarePower with ⟨s, hs⟩
  have hreference :=
    uniformizerPower_mul_normalizedUnitPart K
      reference.toBONG.valueProduct
  change uniformizerPowerUnit K T *
      reference.ternaryDeterminantUnitPart =
        reference.toBONG.valueProduct at hreference
  have hpower :
      uniformizerPowerUnit K (2 * R + S) *
          uniformizerPowerUnit K T =
        uniformizerPowerUnit K (2 * R + S + T) := by
    unfold uniformizerPowerUnit
    rw [← zpow_add]
  rw [reference.beli2019Lemma99Values_determinant_eq R S ε η]
  change
    (uniformizerPowerUnit K (2 * R + S) *
        reference.ternaryDeterminantUnitPart ^ 3 * (ε * η) ^ 2) *
      reference.toBONG.valueProduct |> IsSquare
  rw [← hreference]
  refine ⟨s * reference.ternaryDeterminantUnitPart ^ 2 * (ε * η), ?_⟩
  rw [show
      (uniformizerPowerUnit K (2 * R + S) *
          reference.ternaryDeterminantUnitPart ^ 3 * (ε * η) ^ 2) *
        (uniformizerPowerUnit K T *
          reference.ternaryDeterminantUnitPart) =
      (uniformizerPowerUnit K (2 * R + S) *
          uniformizerPowerUnit K T) *
        reference.ternaryDeterminantUnitPart ^ 4 * (ε * η) ^ 2 by
      simp only [pow_succ, pow_zero]
      ac_rfl,
    hpower, hs]
  simp only [pow_succ, pow_zero]
  ac_rfl

/-- The adjacent Hilbert symbol of the unified list is `(η, ε)`. -/
theorem beli2019Lemma99Values_adjacentHilbert
    [HilbertSymbolLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S) :
    hilbertSymbol K
        (-(reference.beli2019Lemma99Values R S ε η 0 *
          reference.beli2019Lemma99Values R S ε η 1))
        (-(reference.beli2019Lemma99Values R S ε η 1 *
          reference.beli2019Lemma99Values R S ε η 2)) =
      hilbertSymbol K η ε := by
  have hsquare := isSquare_uniformizerPowerUnit_of_even
    (K := K) (R + S) (beli2019Lemma99_evenOrderSum hparity)
  rcases hsquare with ⟨s, hs⟩
  have hfirst :
      -(reference.beli2019Lemma99Values R S ε η 0 *
          reference.beli2019Lemma99Values R S ε η 1) =
        η * (s * reference.ternaryDeterminantUnitPart * ε) ^ 2 := by
    rw [reference.beli2019Lemma99Values_firstAdjacentProduct R S ε η,
      hs]
    simp only [pow_two]
    ac_rfl
  have hsecond :
      -(reference.beli2019Lemma99Values R S ε η 1 *
          reference.beli2019Lemma99Values R S ε η 2) =
        ε * (s * reference.ternaryDeterminantUnitPart * η) ^ 2 := by
    rw [reference.beli2019Lemma99Values_secondAdjacentProduct R S ε η,
      hs]
    simp only [pow_two]
    ac_rfl
  rw [hfirst, hsecond, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right]

/-- Isotropy of the displayed ternary form is controlled by `(η, ε)`. -/
theorem beli2019Lemma99Values_isotropic_iff
    [HilbertSymbolLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S) :
    DiagonalIsotropic
        (diagonalUnitCoefficients
          (reference.beli2019Lemma99Values R S ε η)) ↔
      hilbertSymbol K η ε = 1 := by
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    reference.beli2019Lemma99Values_adjacentHilbert R S ε η hparity]

/-- Matching the isotropy dichotomy gives equality of ternary Hasse
invariants. -/
theorem beli2019Lemma99Values_hasse_eq
    [HilbertSymbolLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S)
    (hmatch : reference.Lemma814FirstThreeIsotropic ↔
      hilbertSymbol K η ε = 1) :
    diagonalHasseSymbol K
        (reference.beli2019Lemma99Values R S ε η) =
      diagonalHasseSymbol K reference.valueUnit := by
  apply diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
  calc
    DiagonalIsotropic
          (diagonalUnitCoefficients
            (reference.beli2019Lemma99Values R S ε η)) ↔
        hilbertSymbol K η ε = 1 :=
      reference.beli2019Lemma99Values_isotropic_iff R S ε η hparity
    _ ↔ reference.Lemma814FirstThreeIsotropic := hmatch.symm
    _ ↔ DiagonalIsotropic
          (diagonalUnitCoefficients reference.valueUnit) :=
      reference.lemma814FirstThreeIsotropic_iff_diagonalValueUnits

/-- Local diagonal classification realizes the unified coefficient list in
the original ternary quadratic space. -/
theorem beli2019Lemma99Values_diagonalRepresents
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (reference : GoodBONG q L 3) (R S : Int) (ε η : Kˣ)
    (hparity : Int.ModEq 2 R S)
    (hdeterminant : Int.ModEq 2
      (ordUnit K reference.toBONG.valueProduct) R)
    (hmatch : reference.Lemma814FirstThreeIsotropic ↔
      hilbertSymbol K η ε = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (reference.beli2019Lemma99Values R S ε η))
      (diagonalUnitCoefficients reference.valueUnit) :=
  DyadicDiagonalClassificationLaws.represents_of_invariants
    (reference.beli2019Lemma99Values R S ε η) reference.valueUnit
    (reference.beli2019Lemma99Values_determinantSquare
      R S ε η hparity hdeterminant)
    (reference.beli2019Lemma99Values_hasse_eq
      R S ε η hparity hmatch)

end BONG.GoodBONG

end Bong
