/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92RankFourRealization
import Bong.Bong.Beli2019Corollary811

/-!
# Beli (2019), Lemma 9.2: the rank-five prescribed basis

This file formalizes the complementary coefficient change

`[a₁,a₂,a₃,a₄,a₅] ↦ [a₁,a₂,εa₃,εηa₄,ηa₅]`.

As in rank four, local diagonal classification constructs an orthogonal
basis, Lemma 8.6 realizes it by a good BONG, and Beli's 2009 theorem will
identify the resulting lattice with the source lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- The rank-five coefficient family in the remaining branch of Lemma 9.2. -/
noncomputable def lemma92LaterScaledValues
    (a : GoodBONG q L 5) (ε η : Kˣ) : Fin 5 → Kˣ :=
  Fin.cons (a.valueUnit (0 : Fin 5)) <|
    Fin.cons (a.tail.valueUnit (0 : Fin 4)) <|
      a.tail.tail.ternaryScaledValues ε η

@[simp]
theorem lemma92LaterScaledValues_zero
    (a : GoodBONG q L 5) (ε η : Kˣ) :
    a.lemma92LaterScaledValues ε η (0 : Fin 5) =
      a.valueUnit (0 : Fin 5) := by
  rfl

@[simp]
theorem lemma92LaterScaledValues_one
    (a : GoodBONG q L 5) (ε η : Kˣ) :
    a.lemma92LaterScaledValues ε η (1 : Fin 5) =
      a.valueUnit (1 : Fin 5) := by
  change a.tail.valueUnit (0 : Fin 4) = _
  rw [a.valueUnit_goodTail]
  congr 1

@[simp]
theorem lemma92LaterScaledValues_two
    (a : GoodBONG q L 5) (ε η : Kˣ) :
    a.lemma92LaterScaledValues ε η (2 : Fin 5) =
      ε * a.valueUnit (2 : Fin 5) := by
  change ε * a.tail.tail.valueUnit (0 : Fin 3) = _
  rw [a.tail.valueUnit_goodTail, a.valueUnit_goodTail]
  congr 2

@[simp]
theorem lemma92LaterScaledValues_three
    (a : GoodBONG q L 5) (ε η : Kˣ) :
    a.lemma92LaterScaledValues ε η (3 : Fin 5) =
      ε * η * a.valueUnit (3 : Fin 5) := by
  change ε * η * a.tail.tail.valueUnit (1 : Fin 3) = _
  rw [a.tail.valueUnit_goodTail, a.valueUnit_goodTail]
  congr 2

@[simp]
theorem lemma92LaterScaledValues_four
    (a : GoodBONG q L 5) (ε η : Kˣ) :
    a.lemma92LaterScaledValues ε η (4 : Fin 5) =
      η * a.valueUnit (4 : Fin 5) := by
  change η * a.tail.tail.valueUnit (2 : Fin 3) = _
  rw [a.tail.valueUnit_goodTail, a.valueUnit_goodTail]
  congr 2

/-- Prepending the two unchanged coefficients to the ternary diagonal
isometry gives the required rank-five ambient representation. -/
theorem lemma92LaterScaled_diagonalRepresents
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3)))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (a.lemma92LaterScaledValues ε η))
      (diagonalUnitCoefficients a.valueUnit) := by
  have hternary :=
    a.tail.tail.ternaryScaled_diagonalRepresents ε η hadjacent
  have hfour := diagonalRepresents_cons hternary
    (a.tail.valueUnit (0 : Fin 4) : K)
  have hfive := diagonalRepresents_cons hfour
    (a.valueUnit (0 : Fin 5) : K)
  have htailOriginal :
      Fin.cons (a.tail.valueUnit (0 : Fin 4))
          a.tail.tail.valueUnit = a.tail.valueUnit := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using a.tail.valueUnit_goodTail j
  have horiginal :
      Fin.cons (a.valueUnit (0 : Fin 5)) a.tail.valueUnit =
        a.valueUnit := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using a.valueUnit_goodTail j
  unfold lemma92LaterScaledValues
  rw [diagonalUnitCoefficients_cons, diagonalUnitCoefficients_cons,
    ← horiginal, diagonalUnitCoefficients_cons,
    ← htailOriginal, diagonalUnitCoefficients_cons]
  exact hfive

/-- The prescribed rank-five values occur on an orthogonal basis of the
source ambient quadratic space. -/
theorem exists_lemma92LaterScaledOrthogonalBasis
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3)))) :
    ∃ X : BONG.OrthogonalBasisData q 5,
      ∀ i, X.valueUnit i = a.lemma92LaterScaledValues ε η i := by
  exact DiagonalRepresents.exists_orthogonalBasisData a
    (a.lemma92LaterScaledValues ε η)
    (a.lemma92LaterScaled_diagonalRepresents ε η hadjacent)

/-- Valuation-unit multipliers preserve the five source orders. -/
theorem lemma92LaterScaled_sameOrders
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.SameOrders a := by
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  intro i
  fin_cases i
  · change ordUnit K (X.valueUnit (0 : Fin 5)) =
      ordUnit K (a.valueUnit (0 : Fin 5))
    rw [hvalues, lemma92LaterScaledValues_zero]
  · change ordUnit K (X.valueUnit (1 : Fin 5)) =
      ordUnit K (a.valueUnit (1 : Fin 5))
    rw [hvalues, lemma92LaterScaledValues_one]
  · change ordUnit K (X.valueUnit (2 : Fin 5)) =
      ordUnit K (a.valueUnit (2 : Fin 5))
    rw [hvalues, lemma92LaterScaledValues_two, ordUnit_mul, hεOrder]
    simp
  · change ordUnit K (X.valueUnit (3 : Fin 5)) =
      ordUnit K (a.valueUnit (3 : Fin 5))
    rw [hvalues, lemma92LaterScaledValues_three,
      ordUnit_mul, ordUnit_mul, hεOrder, hηOrder]
    simp
  · change ordUnit K (X.valueUnit (4 : Fin 5)) =
      ordUnit K (a.valueUnit (4 : Fin 5))
    rw [hvalues, lemma92LaterScaledValues_four, ordUnit_mul, hηOrder]
    simp

/-- The first mixed prefix is a square. -/
theorem lemma92LaterScaled_comparisonPrefixUnit_one
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.comparisonPrefixUnit a 1 =
      (a.valueUnit (0 : Fin 5)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 1 * X.prefixProduct 1 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 5 => j.1 < 1) = {0} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The second mixed prefix is also a square because both coefficients are
unchanged. -/
theorem lemma92LaterScaled_comparisonPrefixUnit_two
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.comparisonPrefixUnit a 2 =
      (a.valueUnit (0 : Fin 5) *
        a.valueUnit (1 : Fin 5)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 2 * X.prefixProduct 2 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 5 => j.1 < 2) = {0, 1} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The third mixed prefix has the defect of `ε`. -/
theorem lemma92LaterScaled_comparisonPrefixUnit_three
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.comparisonPrefixUnit a 3 =
      ε * (a.valueUnit (0 : Fin 5) *
        a.valueUnit (1 : Fin 5) * a.valueUnit (2 : Fin 5)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 3 * X.prefixProduct 3 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 5 => j.1 < 3) =
      {0, 1, 2} by decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The fourth mixed prefix has the defect of `η`. -/
theorem lemma92LaterScaled_comparisonPrefixUnit_four
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.comparisonPrefixUnit a 4 =
      η * (ε * a.valueUnit (0 : Fin 5) *
        a.valueUnit (1 : Fin 5) * a.valueUnit (2 : Fin 5) *
          a.valueUnit (3 : Fin 5)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 4 * X.prefixProduct 4 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 5 => j.1 < 4) =
      {0, 1, 2, 3} by decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The full mixed comparison product is a square. -/
theorem lemma92LaterScaled_comparisonPrefixUnit_five
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    X.comparisonPrefixUnit a 5 =
      (ε * η * diagonalUnitDeterminant a.valueUnit) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 5 * X.prefixProduct 5 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
    diagonalUnitDeterminant
  simp [hvalues, Fin.prod_univ_five, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- Only the third and fourth cuts give nontrivial Lemma 8.6 prefix
conditions; they are the defects of `ε` and `η`. -/
theorem lemma92LaterScaled_prefixDefectBounds
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i)
    (hεDefect : (a.alphaValue (2 : Fin 4) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (3 : Fin 4) : WithTop ℚ) ≤
      defectOrder (K := K) η) :
    X.PrefixDefectBounds a := by
  intro i
  fin_cases i
  · change (a.alphaValue (0 : Fin 4) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 1
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92LaterScaled_comparisonPrefixUnit_one X ε η hvalues]
    have hsquare : IsSquare ((a.valueUnit (0 : Fin 5)) ^ 2) := by
      refine ⟨a.valueUnit (0 : Fin 5), ?_⟩
      simp only [pow_two]
    rw [defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · change (a.alphaValue (1 : Fin 4) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 2
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92LaterScaled_comparisonPrefixUnit_two X ε η hvalues]
    have hsquare : IsSquare
        ((a.valueUnit (0 : Fin 5) * a.valueUnit (1 : Fin 5)) ^ 2) := by
      refine ⟨a.valueUnit (0 : Fin 5) * a.valueUnit (1 : Fin 5), ?_⟩
      simp only [pow_two]
    rw [defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · change (a.alphaValue (2 : Fin 4) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 3
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92LaterScaled_comparisonPrefixUnit_three X ε η hvalues,
      defectOrder_mul_square]
    exact hεDefect
  · change (a.alphaValue (3 : Fin 4) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 4
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92LaterScaled_comparisonPrefixUnit_four X ε η hvalues,
      defectOrder_mul_square]
    exact hηDefect

/-- The full comparison square required by Lemma 8.6(i). -/
theorem lemma92LaterScaled_fullComparisonSquare
    (a : GoodBONG q L 5) (X : BONG.OrthogonalBasisData q 5)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92LaterScaledValues ε η i) :
    IsSquare (X.comparisonPrefixUnit a 5) := by
  rw [a.lemma92LaterScaled_comparisonPrefixUnit_five X ε η hvalues]
  refine ⟨ε * η * diagonalUnitDeterminant a.valueUnit, ?_⟩
  simp only [pow_two]

/-- Rank-five output of the ambient construction and Lemma 8.6, before
lattice classification. -/
structure Lemma92LaterRawRealization
    (a : GoodBONG q L 5) (ε η : Kˣ) where
  lattice : Lattice K V
  transformed : GoodBONG q lattice 5
  firstValue_eq : transformed.valueUnit (0 : Fin 5) =
    a.valueUnit (0 : Fin 5)
  secondValue_eq : transformed.valueUnit (1 : Fin 5) =
    a.valueUnit (1 : Fin 5)
  thirdValue_eq : transformed.valueUnit (2 : Fin 5) =
    ε * a.valueUnit (2 : Fin 5)
  fourthValue_eq : transformed.valueUnit (3 : Fin 5) =
    ε * η * a.valueUnit (3 : Fin 5)
  fifthValue_eq : transformed.valueUnit (4 : Fin 5) =
    η * a.valueUnit (4 : Fin 5)
  sameOrders : a.SameOrders transformed
  prefixDefectBounds : a.PrefixDefectBounds transformed
  fullComparisonSquare :
    IsSquare (comparisonPrefixUnit a transformed 5)
  sourceAlpha_le : ∀ i, a.alphaValue i ≤ transformed.alphaValue i

/-- Construction of the rank-five prescribed good BONG on an as-yet
unidentified lattice. -/
theorem exists_lemma92LaterRawRealization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (2 : Fin 4) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (3 : Fin 4) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3)))) :
    Nonempty (Lemma92LaterRawRealization a ε η) := by
  rcases a.exists_lemma92LaterScaledOrthogonalBasis ε η hadjacent with
    ⟨X, hvalues⟩
  have hordersX : X.SameOrders a :=
    a.lemma92LaterScaled_sameOrders X ε η hεUnit hηUnit hvalues
  have hprefixX : X.PrefixDefectBounds a :=
    a.lemma92LaterScaled_prefixDefectBounds X ε η hvalues
      hεDefect hηDefect
  have hfullX : IsSquare (X.comparisonPrefixUnit a 5) :=
    a.lemma92LaterScaled_fullComparisonSquare X ε η hvalues
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      a X hordersX hprefixX hfullX with
    ⟨M, c₀, hreal, hgood⟩
  let c : GoodBONG q M 5 := ⟨c₀, hgood⟩
  have hvalue (i : Fin 5) :
      c.valueUnit i = a.lemma92LaterScaledValues ε η i := by
    calc
      c.valueUnit i = X.valueUnit i :=
        (X.valueUnit_eq_of_isRealizedBy hreal i).symm
      _ = a.lemma92LaterScaledValues ε η i := hvalues i
  have horders : a.SameOrders c := by
    intro i
    calc
      a.order i = X.order i := (hordersX i).symm
      _ = c.order i := X.order_eq_of_isRealizedBy hreal i
  have hprefix : a.PrefixDefectBounds c :=
    X.prefixDefectBounds_of_isRealizedBy a hreal hprefixX
  have hfull : IsSquare (comparisonPrefixUnit a c 5) := by
    change IsSquare (a.prefixProduct 5 * c.prefixProduct 5)
    rw [← X.prefixProduct_eq_of_isRealizedBy (b := c) hreal 5]
    exact hfullX
  have halpha (i : Fin 4) : a.alphaValue i ≤ c.alphaValue i :=
    beli2019Lemma86_ii a c horders hprefix hfull i
  exact ⟨{
    lattice := M
    transformed := c
    firstValue_eq := (hvalue 0).trans
      (a.lemma92LaterScaledValues_zero ε η)
    secondValue_eq := (hvalue 1).trans
      (a.lemma92LaterScaledValues_one ε η)
    thirdValue_eq := (hvalue 2).trans
      (a.lemma92LaterScaledValues_two ε η)
    fourthValue_eq := (hvalue 3).trans
      (a.lemma92LaterScaledValues_three ε η)
    fifthValue_eq := (hvalue 4).trans
      (a.lemma92LaterScaledValues_four ε η)
    sameOrders := horders
    prefixDefectBounds := hprefix
    fullComparisonSquare := hfull
    sourceAlpha_le := halpha
  }⟩

namespace Lemma92LaterRawRealization

/-- The first literal binary alpha is unchanged because the first two
coefficients and their orders are unchanged. -/
theorem adjacentBinaryAlpha_zero_eq
    {a : GoodBONG q L 5} {ε η : Kˣ}
    (D : Lemma92LaterRawRealization a ε η) :
    D.transformed.adjacentBinaryAlpha (0 : Fin 4) =
      a.adjacentBinaryAlpha (0 : Fin 4) := by
  unfold adjacentBinaryAlpha halfGapCandidate leftDefectCandidate
    adjacentDefect adjacentProduct
  rw [← D.sameOrders (0 : Fin 4).succ,
    ← D.sameOrders (0 : Fin 4).castSucc]
  have hzero : (0 : Fin 4).castSucc = (0 : Fin 5) := Fin.ext rfl
  have hone : (0 : Fin 4).succ = (1 : Fin 5) := Fin.ext rfl
  rw [hzero, hone, D.firstValue_eq, D.secondValue_eq]

/-- Corollary 8.10's normalization of the first literal binary alpha gives
equality of the first global alpha after Lemma 8.6. -/
theorem firstAlpha_eq_of_adjacentBinaryAlpha
    {a : GoodBONG q L 5} {ε η : Kˣ}
    (D : Lemma92LaterRawRealization a ε η)
    (hbinary : a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ)) :
    a.alphaValue (0 : Fin 4) =
      D.transformed.alphaValue (0 : Fin 4) := by
  have hhalf := D.transformed.alpha_le_halfGapCandidate (0 : Fin 4)
  have hleft := D.transformed.alpha_le_leftDefectCandidate
    (i := (0 : Fin 4)) (j := (0 : Fin 4)) le_rfl
  have hupperTop : D.transformed.alpha (0 : Fin 4) ≤
      D.transformed.adjacentBinaryAlpha (0 : Fin 4) := by
    unfold adjacentBinaryAlpha
    exact le_min hhalf hleft
  rw [D.adjacentBinaryAlpha_zero_eq, hbinary,
    ← D.transformed.coe_alphaValue] at hupperTop
  have hupper : D.transformed.alphaValue (0 : Fin 4) ≤
      a.alphaValue (0 : Fin 4) := by
    exact_mod_cast hupperTop
  exact le_antisymm (D.sourceAlpha_le 0) hupper

/-- The common source right endpoints then propagate first-alpha equality to
all four rank-five alphas. -/
theorem sameAlphas_of_firstAlpha_eq_of_sourceRightEndpoints
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L 5} {ε η : Kˣ}
    (D : Lemma92LaterRawRealization a ε η)
    (hfirst : a.alphaValue (0 : Fin 4) =
      D.transformed.alphaValue (0 : Fin 4))
    (hsource : ∀ i : Fin 4,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 4)) :
    a.SameAlphas D.transformed := by
  intro i
  apply le_antisymm (D.sourceAlpha_le i)
  have hmono := D.transformed.alphaRightEndpoint_antitone
    (show (0 : Fin 4) ≤ i by omega)
  have hsourceI := hsource i
  unfold alphaRightEndpoint at hmono hsourceI
  have hiOrder := D.sameOrders i.succ
  have hzeroOrder := D.sameOrders (0 : Fin 4).succ
  rw [← hiOrder, ← hzeroOrder, ← hfirst] at hmono
  linarith

/-- The two early internal representation clauses use the unchanged first
two prefixes; the last clause is excluded by the paper's alpha-sum bound. -/
theorem internalRepresentationConditions_of_lastAlphaSum_le
    {a : GoodBONG q L 5} {ε η : Kˣ}
    (D : Lemma92LaterRawRealization a ε η)
    (hAlphaSum :
      a.alphaValue (2 : Fin 4) + a.alphaValue (3 : Fin 4) ≤
        2 * (ramificationIndex K : ℚ)) :
    a.InternalRepresentationConditions D.transformed := by
  intro i hi htrigger
  fin_cases i
  · norm_num at hi
  · have hpref :
        D.transformed.prefixValues 1 (by omega) =
          a.prefixValues 1 (by omega) := by
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      change (D.transformed.valueUnit (0 : Fin 5) : K) =
        (a.valueUnit (0 : Fin 5) : K)
      exact congrArg Units.val D.firstValue_eq
    rw [hpref]
    exact a.prefixValues_represents_succ 1 (by omega)
  · have hpref :
        D.transformed.prefixValues 2 (by omega) =
          a.prefixValues 2 (by omega) := by
      funext j
      fin_cases j
      · change (D.transformed.valueUnit (0 : Fin 5) : K) =
          (a.valueUnit (0 : Fin 5) : K)
        exact congrArg Units.val D.firstValue_eq
      · change (D.transformed.valueUnit (1 : Fin 5) : K) =
          (a.valueUnit (1 : Fin 5) : K)
        exact congrArg Units.val D.secondValue_eq
    rw [hpref]
    exact a.prefixValues_represents_succ 2 (by omega)
  · change 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (2 : Fin 4) + a.alphaValue (3 : Fin 4) at htrigger
    exact (not_lt_of_ge hAlphaSum htrigger).elim

/-- Beli's 2009 classification transports a fully verified raw rank-five
realization back to the source lattice. -/
theorem toLaterScalingData
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L 5} {ε η : Kˣ}
    (D : Lemma92LaterRawRealization a ε η)
    (hsameAlphas : a.SameAlphas D.transformed)
    (hinternal : a.InternalRepresentationConditions D.transformed) :
    Nonempty (Lemma92LaterScalingData a ε η) := by
  have hconditions : ClassificationConditions a D.transformed :=
    ⟨D.sameOrders, hsameAlphas, D.prefixDefectBounds, hinternal⟩
  have hisometric : Lattice.IsIsometric q q L D.lattice :=
    (isometric_iff_classificationConditions
      (QuadraticSpace.isIsometric_refl q) a D.transformed).2 hconditions
  rcases hisometric with ⟨f⟩
  let transformed := D.transformed.mapLatticeIsometry f.symm
  have hvalue (i : Fin 5) :
      transformed.valueUnit i = D.transformed.valueUnit i := by
    apply Units.ext
    change (D.transformed.toBONG.mapLatticeIsometry f.symm).value i =
      D.transformed.toBONG.value i
    rw [BONG.value_mapLatticeIsometry]
  exact ⟨{
    transformed := transformed
    firstValue_eq := (hvalue 0).trans D.firstValue_eq
    secondValue_eq := (hvalue 1).trans D.secondValue_eq
    thirdValue_eq := (hvalue 2).trans D.thirdValue_eq
    fourthValue_eq := (hvalue 3).trans D.fourthValue_eq
    fifthValue_eq := (hvalue 4).trans D.fifthValue_eq
  }⟩

end Lemma92LaterRawRealization

/-- Exact rank-five scaling theorem, parameterized by the explicit local unit
and Hilbert calculations of the printed proof. -/
theorem exists_lemma92LaterScalingData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 5) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (2 : Fin 4) : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (a.alphaValue (3 : Fin 4) : WithTop ℚ))
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.tail.valueUnit (0 : Fin 3) *
            a.tail.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.tail.valueUnit (1 : Fin 3) *
            a.tail.tail.valueUnit (2 : Fin 3))))
    (hbinary : a.adjacentBinaryAlpha (0 : Fin 4) =
      (a.alphaValue (0 : Fin 4) : WithTop ℚ))
    (hsource : ∀ i : Fin 4,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 4))
    (hAlphaSum :
      a.alphaValue (2 : Fin 4) + a.alphaValue (3 : Fin 4) ≤
        2 * (ramificationIndex K : ℚ)) :
    Nonempty (Lemma92LaterScalingData a ε η) := by
  rcases a.exists_lemma92LaterRawRealization ε η hεUnit hηUnit
      (hεDefect ▸ le_rfl) (hηDefect ▸ le_rfl) hadjacent with ⟨D⟩
  have hfirst := D.firstAlpha_eq_of_adjacentBinaryAlpha hbinary
  have halphas :=
    D.sameAlphas_of_firstAlpha_eq_of_sourceRightEndpoints hfirst hsource
  have hinternal :=
    D.internalRepresentationConditions_of_lastAlphaSum_le hAlphaSum
  exact D.toLaterScalingData halphas hinternal

end BONG.GoodBONG

end Bong
