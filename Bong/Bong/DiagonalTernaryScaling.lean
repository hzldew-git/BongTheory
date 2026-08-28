/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma86
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.DiagonalOrthogonalBasis

/-!
# Diagonal ternary scaling

This file formalizes the ternary change of coefficients used in the proof of
Beli (2019), Lemma 8.14.  The transformation

`[a₁, a₂, a₃] ↦ [εa₁, εηa₂, ηa₃]`

preserves the determinant square class.  Its remaining ambient-space
condition is exactly the adjacent Hilbert-symbol identity occurring in the
paper.  Local diagonal classification then produces an actual orthogonal
basis with these values.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The coefficient sequence `[εa₁, εηa₂, ηa₃]` from the ternary part of
Lemma 8.14. -/
noncomputable def ternaryScaledValues
    (a : GoodBONG q L 3) (ε η : Kˣ) : Fin 3 → Kˣ :=
  ![ε * a.valueUnit (0 : Fin 3),
    ε * η * a.valueUnit (1 : Fin 3),
    η * a.valueUnit (2 : Fin 3)]

@[simp]
theorem ternaryScaledValues_zero
    (a : GoodBONG q L 3) (ε η : Kˣ) :
    a.ternaryScaledValues ε η (0 : Fin 3) =
      ε * a.valueUnit (0 : Fin 3) := by
  rfl

@[simp]
theorem ternaryScaledValues_one
    (a : GoodBONG q L 3) (ε η : Kˣ) :
    a.ternaryScaledValues ε η (1 : Fin 3) =
      ε * η * a.valueUnit (1 : Fin 3) := by
  rfl

@[simp]
theorem ternaryScaledValues_two
    (a : GoodBONG q L 3) (ε η : Kˣ) :
    a.ternaryScaledValues ε η (2 : Fin 3) =
      η * a.valueUnit (2 : Fin 3) := by
  rfl

/-- The source and scaled ternary forms have the same determinant square
class. -/
theorem ternaryScaledValues_determinantSquare
    (a : GoodBONG q L 3) (ε η : Kˣ) :
    IsSquare
      (diagonalUnitDeterminant (a.ternaryScaledValues ε η) *
        diagonalUnitDeterminant a.valueUnit) := by
  refine ⟨ε * η * diagonalUnitDeterminant a.valueUnit, ?_⟩
  apply Units.ext
  simp only [diagonalUnitDeterminant, Fin.prod_univ_three,
    ternaryScaledValues_zero, ternaryScaledValues_one,
    ternaryScaledValues_two, Units.val_mul]
  ring

/-- The adjacent Hilbert identity in the paper is precisely the Hasse
invariant condition for the scaled ternary form. -/
theorem ternaryScaledValues_hasse_eq
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))) :
    diagonalHasseSymbol K (a.ternaryScaledValues ε η) =
      diagonalHasseSymbol K a.valueUnit := by
  rw [diagonalHasseSymbol_fin_three_eq_adjacent,
    diagonalHasseSymbol_fin_three_eq_adjacent]
  have hfirst :
      -(a.ternaryScaledValues ε η (0 : Fin 3) *
          a.ternaryScaledValues ε η (1 : Fin 3)) =
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) *
          ε ^ 2 := by
    apply Units.ext
    simp only [ternaryScaledValues_zero, ternaryScaledValues_one,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have hsecond :
      -(a.ternaryScaledValues ε η (1 : Fin 3) *
          a.ternaryScaledValues ε η (2 : Fin 3)) =
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) *
          η ^ 2 := by
    apply Units.ext
    simp only [ternaryScaledValues_one, ternaryScaledValues_two,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hfirst, hsecond, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right, hadjacent]

/-- The invariant calculation as a reusable diagonal representation. -/
theorem ternaryScaled_diagonalRepresents
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (a.ternaryScaledValues ε η))
      (diagonalUnitCoefficients a.valueUnit) :=
  DyadicDiagonalClassificationLaws.represents_of_invariants
    (a.ternaryScaledValues ε η) a.valueUnit
    (a.ternaryScaledValues_determinantSquare ε η)
    (a.ternaryScaledValues_hasse_eq ε η hadjacent)

/-- Local diagonal classification turns the ternary invariant calculation
into an orthogonal basis of the original ambient quadratic space. -/
theorem exists_ternaryScaledOrthogonalBasis
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))) :
    ∃ X : BONG.OrthogonalBasisData q 3,
      ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i := by
  have hrep := a.ternaryScaled_diagonalRepresents ε η hadjacent
  exact DiagonalRepresents.exists_orthogonalBasisData a
    (a.ternaryScaledValues ε η) hrep

/-- The first mixed prefix of a basis with the scaled values is `ε` times a
square. -/
theorem ternaryScaled_comparisonPrefixUnit_one
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.comparisonPrefixUnit a 1 =
      ε * (a.valueUnit (0 : Fin 3)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 1 * X.prefixProduct 1 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 3 => j.1 < 1) = {0} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The second mixed prefix is `η` times a square. -/
theorem ternaryScaled_comparisonPrefixUnit_two
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.comparisonPrefixUnit a 2 =
      η * (ε * a.valueUnit (0 : Fin 3) *
        a.valueUnit (1 : Fin 3)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 2 * X.prefixProduct 2 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 3 => j.1 < 2) = {0, 1} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The full mixed comparison product is a square. -/
theorem ternaryScaled_comparisonPrefixUnit_full
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.comparisonPrefixUnit a 3 =
      (ε * η * diagonalUnitDeterminant a.valueUnit) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 3 * X.prefixProduct 3 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
    diagonalUnitDeterminant
  simp [hvalues, Fin.prod_univ_three, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- Valuation-unit multipliers preserve the full order sequence. -/
theorem ternaryScaled_sameOrders
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.SameOrders a := by
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  intro i
  fin_cases i
  · change ordUnit K (X.valueUnit (0 : Fin 3)) =
      a.toBONG.order (0 : Fin 3)
    rw [hvalues, ternaryScaledValues_zero,
      a.toBONG.order_eq_ordUnit, ordUnit_mul, hεOrder]
    simp
    unfold GoodBONG.valueUnit
    rfl
  · change ordUnit K (X.valueUnit (1 : Fin 3)) =
      a.toBONG.order (1 : Fin 3)
    rw [hvalues, ternaryScaledValues_one,
      a.toBONG.order_eq_ordUnit, ordUnit_mul, ordUnit_mul,
      hεOrder, hηOrder]
    simp
    unfold GoodBONG.valueUnit
    rfl
  · change ordUnit K (X.valueUnit (2 : Fin 3)) =
      a.toBONG.order (2 : Fin 3)
    rw [hvalues, ternaryScaledValues_two,
      a.toBONG.order_eq_ordUnit, ordUnit_mul, hηOrder]
    simp
    unfold GoodBONG.valueUnit
    rfl

/-- The first adjacent defect of the scaled basis is the defect of
`-η a₁ a₂`; the remaining factor is the square `ε²`. -/
theorem ternaryScaled_adjacentDefect_zero
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K)
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) := by
  unfold BONG.OrthogonalBasisData.adjacentDefect
    BONG.OrthogonalBasisData.adjacentProduct
  change defectOrder (K := K)
      (-(X.valueUnit (0 : Fin 3) * X.valueUnit (1 : Fin 3))) = _
  rw [hvalues (0 : Fin 3), hvalues (1 : Fin 3)]
  have hproduct :
      -(a.ternaryScaledValues ε η (0 : Fin 3) *
          a.ternaryScaledValues ε η (1 : Fin 3)) =
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) *
          ε ^ 2 := by
    apply Units.ext
    simp only [ternaryScaledValues_zero, ternaryScaledValues_one,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- The second adjacent defect of the scaled basis is the defect of
`-ε a₂ a₃`; the remaining factor is the square `η²`. -/
theorem ternaryScaled_adjacentDefect_one
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    X.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
  unfold BONG.OrthogonalBasisData.adjacentDefect
    BONG.OrthogonalBasisData.adjacentProduct
  change defectOrder (K := K)
      (-(X.valueUnit (1 : Fin 3) * X.valueUnit (2 : Fin 3))) = _
  rw [hvalues (1 : Fin 3), hvalues (2 : Fin 3)]
  have hproduct :
      -(a.ternaryScaledValues ε η (1 : Fin 3) *
          a.ternaryScaledValues ε η (2 : Fin 3)) =
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) *
          η ^ 2 := by
    apply Units.ext
    simp only [ternaryScaledValues_one, ternaryScaledValues_two,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- Bounds on the defects of `ε` and `η` are exactly the two prefix bounds
required by Lemma 8.6(i). -/
theorem ternaryScaled_prefixDefectBounds
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i)
    (hεDefect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η) :
    X.PrefixDefectBounds a := by
  intro i
  fin_cases i
  · change (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 1
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.ternaryScaled_comparisonPrefixUnit_one X ε η hvalues,
      defectOrder_mul_square]
    exact hεDefect
  · change (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 2
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.ternaryScaled_comparisonPrefixUnit_two X ε η hvalues,
      defectOrder_mul_square]
    exact hηDefect

/-- The final comparison hypothesis in Lemma 8.6(i) is automatic for the
scaled ternary coefficient pattern. -/
theorem ternaryScaled_fullComparisonSquare
    (a : GoodBONG q L 3) (X : BONG.OrthogonalBasisData q 3)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.ternaryScaledValues ε η i) :
    IsSquare (X.comparisonPrefixUnit a 3) := by
  rw [a.ternaryScaled_comparisonPrefixUnit_full X ε η hvalues]
  refine ⟨ε * η * diagonalUnitDeterminant a.valueUnit, ?_⟩
  simp only [pow_two]

/-- In the property-A ternary case, the explicit Hilbert and defect data
produce a transformed good BONG on the original lattice.  This is the
lattice-theoretic construction used in the `R₁ < R₃`, rank-three branch of
Lemma 8.14. -/
theorem exists_goodBONG_ternaryScaledValues_of_propertyA
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))))
    (hproperty : a.toBONG.HasPropertyA)
    (hAlphaSum :
      a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
        2 * (ramificationIndex K : ℚ)) :
    ∃ c : GoodBONG q L 3,
      ∀ i, c.valueUnit i = a.ternaryScaledValues ε η i := by
  rcases a.exists_ternaryScaledOrthogonalBasis ε η hadjacent with
    ⟨X, hvalues⟩
  have hordersX : X.SameOrders a :=
    a.ternaryScaled_sameOrders X ε η hεUnit hηUnit hvalues
  have hprefixX : X.PrefixDefectBounds a :=
    a.ternaryScaled_prefixDefectBounds X ε η hvalues hεDefect hηDefect
  have hfullX : IsSquare (X.comparisonPrefixUnit a 3) :=
    a.ternaryScaled_fullComparisonSquare X ε η hvalues
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      a X hordersX hprefixX hfullX with
    ⟨M, c₀, hreal, hgood⟩
  let c : GoodBONG q M 3 := ⟨c₀, hgood⟩
  have horders : a.SameOrders c := by
    intro i
    calc
      a.order i = X.order i := (hordersX i).symm
      _ = c.order i := X.order_eq_of_isRealizedBy hreal i
  have hprefix : a.PrefixDefectBounds c :=
    X.prefixDefectBounds_of_isRealizedBy a hreal hprefixX
  have hfull : IsSquare (comparisonPrefixUnit a c 3) := by
    change IsSquare (a.prefixProduct 3 * c.prefixProduct 3)
    rw [← BONG.OrthogonalBasisData.prefixProduct_eq_of_isRealizedBy
      (b := c) hreal 3]
    exact hfullX
  have halphas : a.SameAlphas c :=
    a.beli2019Lemma86_iii c hproperty horders hprefix hfull
  have hinternal : a.InternalRepresentationConditions c := by
    intro i hi htrigger
    fin_cases i
    · norm_num at hi
    · change 2 * (ramificationIndex K : ℚ) <
        a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) at htrigger
      exact (not_lt_of_ge hAlphaSum htrigger).elim
  have hconditions : ClassificationConditions a c :=
    ⟨horders, halphas, hprefix, hinternal⟩
  have hisometric : Lattice.IsIsometric q q L M :=
    (isometric_iff_classificationConditions
      (QuadraticSpace.isIsometric_refl q) a c).2 hconditions
  rcases hisometric with ⟨f⟩
  let transformed := c.mapLatticeIsometry f.symm
  refine ⟨transformed, ?_⟩
  intro i
  apply Units.ext
  change (c.toBONG.mapLatticeIsometry f.symm).value i =
    (a.ternaryScaledValues ε η i : K)
  rw [BONG.value_mapLatticeIsometry]
  have hvalue := X.value_eq_of_isRealizedBy hreal i
  have hscaledValue := congrArg Units.val (hvalues i)
  change c₀.value i = (a.ternaryScaledValues ε η i : K)
  rw [← hvalue]
  simpa using hscaledValue

/-- First-coordinate projection of the value-preserving property-A ternary
scaling construction. -/
theorem exists_goodBONG_ternaryScaled_of_propertyA
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))))
    (hproperty : a.toBONG.HasPropertyA)
    (hAlphaSum :
      a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
        2 * (ramificationIndex K : ℚ)) :
    ∃ c : GoodBONG q L 3,
      c.valueUnit (0 : Fin 3) = ε * a.valueUnit (0 : Fin 3) := by
  rcases a.exists_goodBONG_ternaryScaledValues_of_propertyA
      ε η hεUnit hηUnit hεDefect hηDefect hadjacent hproperty hAlphaSum with
    ⟨c, hc⟩
  exact ⟨c, (hc 0).trans (a.ternaryScaledValues_zero ε η)⟩

end BONG.GoodBONG

end Bong
