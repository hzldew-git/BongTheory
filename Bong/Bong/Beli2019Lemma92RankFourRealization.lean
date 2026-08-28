/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92SegmentLift
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.Beli2019Reflexivity

/-!
# Beli (2019), Lemma 9.2: the rank-four prescribed basis

This file carries out the geometric and Lemma 8.6 parts of the quaternary
coefficient change

`[a₁,a₂,a₃,a₄] ↦ [a₁, εa₂, εηa₃, ηa₄]`.

The subsequent classification step will identify the lattice produced by
Lemma 8.6 with the original initial quaternary segment.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- The rank-four coefficient family used in the early alternatives of
Lemma 9.2. -/
noncomputable def lemma92EarlyScaledValues
    (a : GoodBONG q L 4) (ε η : Kˣ) : Fin 4 → Kˣ :=
  Fin.cons (a.valueUnit (0 : Fin 4))
    (a.tail.ternaryScaledValues ε η)

@[simp]
theorem lemma92EarlyScaledValues_zero
    (a : GoodBONG q L 4) (ε η : Kˣ) :
    a.lemma92EarlyScaledValues ε η (0 : Fin 4) =
      a.valueUnit (0 : Fin 4) := by
  rfl

@[simp]
theorem lemma92EarlyScaledValues_one
    (a : GoodBONG q L 4) (ε η : Kˣ) :
    a.lemma92EarlyScaledValues ε η (1 : Fin 4) =
      ε * a.valueUnit (1 : Fin 4) := by
  change ε * a.tail.valueUnit (0 : Fin 3) = _
  rw [a.valueUnit_goodTail]
  congr 2

@[simp]
theorem lemma92EarlyScaledValues_two
    (a : GoodBONG q L 4) (ε η : Kˣ) :
    a.lemma92EarlyScaledValues ε η (2 : Fin 4) =
      ε * η * a.valueUnit (2 : Fin 4) := by
  change ε * η * a.tail.valueUnit (1 : Fin 3) = _
  rw [a.valueUnit_goodTail]
  congr 2

@[simp]
theorem lemma92EarlyScaledValues_three
    (a : GoodBONG q L 4) (ε η : Kˣ) :
    a.lemma92EarlyScaledValues ε η (3 : Fin 4) =
      η * a.valueUnit (3 : Fin 4) := by
  change η * a.tail.valueUnit (2 : Fin 3) = _
  rw [a.valueUnit_goodTail]
  congr 2

/-- The ternary Hilbert-symbol identity, with the unchanged first
coefficient prepended, represents the original rank-four quadratic space. -/
theorem lemma92EarlyScaled_diagonalRepresents
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3)))) :
    DiagonalRepresents
      (diagonalUnitCoefficients (a.lemma92EarlyScaledValues ε η))
      (diagonalUnitCoefficients a.valueUnit) := by
  have htail :=
    a.tail.ternaryScaled_diagonalRepresents ε η hadjacent
  have hcons := diagonalRepresents_cons htail
    (a.valueUnit (0 : Fin 4) : K)
  have horiginal :
      Fin.cons (a.valueUnit (0 : Fin 4)) a.tail.valueUnit =
        a.valueUnit := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using a.valueUnit_goodTail j
  unfold lemma92EarlyScaledValues
  rw [diagonalUnitCoefficients_cons, ← horiginal,
    diagonalUnitCoefficients_cons]
  exact hcons

/-- The prescribed rank-four values occur on an orthogonal basis of the
original ambient quadratic space. -/
theorem exists_lemma92EarlyScaledOrthogonalBasis
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (ε η : Kˣ)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3)))) :
    ∃ X : BONG.OrthogonalBasisData q 4,
      ∀ i, X.valueUnit i = a.lemma92EarlyScaledValues ε η i := by
  exact DiagonalRepresents.exists_orthogonalBasisData a
    (a.lemma92EarlyScaledValues ε η)
    (a.lemma92EarlyScaled_diagonalRepresents ε η hadjacent)

/-- Valuation-unit multipliers preserve all four prescribed orders. -/
theorem lemma92EarlyScaled_sameOrders
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    X.SameOrders a := by
  have hεOrder : ordUnit K ε = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hεUnit
  have hηOrder : ordUnit K η = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).1 hηUnit
  intro i
  fin_cases i
  · change ordUnit K (X.valueUnit (0 : Fin 4)) =
      ordUnit K (a.valueUnit (0 : Fin 4))
    rw [hvalues, lemma92EarlyScaledValues_zero]
  · change ordUnit K (X.valueUnit (1 : Fin 4)) =
      ordUnit K (a.valueUnit (1 : Fin 4))
    rw [hvalues, lemma92EarlyScaledValues_one,
      ordUnit_mul, hεOrder]
    simp
  · change ordUnit K (X.valueUnit (2 : Fin 4)) =
      ordUnit K (a.valueUnit (2 : Fin 4))
    rw [hvalues, lemma92EarlyScaledValues_two,
      ordUnit_mul, ordUnit_mul,
      hεOrder, hηOrder]
    simp
  · change ordUnit K (X.valueUnit (3 : Fin 4)) =
      ordUnit K (a.valueUnit (3 : Fin 4))
    rw [hvalues, lemma92EarlyScaledValues_three,
      ordUnit_mul, hηOrder]
    simp

/-- The first mixed prefix is already a square. -/
theorem lemma92EarlyScaled_comparisonPrefixUnit_one
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    X.comparisonPrefixUnit a 1 =
      (a.valueUnit (0 : Fin 4)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 1 * X.prefixProduct 1 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 1) = {0} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The second mixed prefix has defect exactly the defect of `ε`. -/
theorem lemma92EarlyScaled_comparisonPrefixUnit_two
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    X.comparisonPrefixUnit a 2 =
      ε * (a.valueUnit (0 : Fin 4) *
        a.valueUnit (1 : Fin 4)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 2 * X.prefixProduct 2 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 2) = {0, 1} by
    decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The third mixed prefix has defect exactly the defect of `η`. -/
theorem lemma92EarlyScaled_comparisonPrefixUnit_three
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    X.comparisonPrefixUnit a 3 =
      η * (ε * a.valueUnit (0 : Fin 4) *
        a.valueUnit (1 : Fin 4) * a.valueUnit (2 : Fin 4)) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 3 * X.prefixProduct 3 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 3) =
      {0, 1, 2} by decide]
  simp [hvalues, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The full mixed comparison product is a square. -/
theorem lemma92EarlyScaled_comparisonPrefixUnit_four
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    X.comparisonPrefixUnit a 4 =
      (ε * η * diagonalUnitDeterminant a.valueUnit) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
  change a.toBONG.prefixProduct 4 * X.prefixProduct 4 = _
  unfold BONG.prefixProduct BONG.OrthogonalBasisData.prefixProduct
    diagonalUnitDeterminant
  simp [hvalues, Fin.prod_univ_four, pow_two]
  unfold GoodBONG.valueUnit
  ac_rfl

/-- The two prescribed unit-defect bounds are exactly the nontrivial prefix
bounds required by Lemma 8.6(i). -/
theorem lemma92EarlyScaled_prefixDefectBounds
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i)
    (hεDefect : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) η) :
    X.PrefixDefectBounds a := by
  intro i
  fin_cases i
  · change (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 1
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92EarlyScaled_comparisonPrefixUnit_one X ε η hvalues]
    have hsquare : IsSquare ((a.valueUnit (0 : Fin 4)) ^ 2) := by
      refine ⟨a.valueUnit (0 : Fin 4), ?_⟩
      simp only [pow_two]
    rw [defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 2
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92EarlyScaled_comparisonPrefixUnit_two X ε η hvalues,
      defectOrder_mul_square]
    exact hεDefect
  · change (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
      X.comparisonPrefixDefect a 3
    unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
    rw [a.lemma92EarlyScaled_comparisonPrefixUnit_three X ε η hvalues,
      defectOrder_mul_square]
    exact hηDefect

/-- The endpoint condition in Lemma 8.6(i) is automatic for this scaling. -/
theorem lemma92EarlyScaled_fullComparisonSquare
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (ε η : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.lemma92EarlyScaledValues ε η i) :
    IsSquare (X.comparisonPrefixUnit a 4) := by
  rw [a.lemma92EarlyScaled_comparisonPrefixUnit_four X ε η hvalues]
  refine ⟨ε * η * diagonalUnitDeterminant a.valueUnit, ?_⟩
  simp only [pow_two]

/-- The output of the geometric construction and Lemma 8.6 before applying
the 2009 lattice classification theorem. -/
structure Lemma92EarlyRawRealization
    (a : GoodBONG q L 4) (ε η : Kˣ) where
  lattice : Lattice K V
  transformed : GoodBONG q lattice 4
  firstValue_eq : transformed.valueUnit (0 : Fin 4) =
    a.valueUnit (0 : Fin 4)
  secondValue_eq : transformed.valueUnit (1 : Fin 4) =
    ε * a.valueUnit (1 : Fin 4)
  thirdValue_eq : transformed.valueUnit (2 : Fin 4) =
    ε * η * a.valueUnit (2 : Fin 4)
  fourthValue_eq : transformed.valueUnit (3 : Fin 4) =
    η * a.valueUnit (3 : Fin 4)
  sameOrders : a.SameOrders transformed
  prefixDefectBounds : a.PrefixDefectBounds transformed
  fullComparisonSquare :
    IsSquare (comparisonPrefixUnit a transformed 4)
  sourceAlpha_le : ∀ i, a.alphaValue i ≤ transformed.alphaValue i

/-- The Hilbert identity and the two unit-defect bounds produce the exact
rank-four coefficient family on a good BONG.  At this stage its lattice is
not yet identified with the source lattice. -/
theorem exists_lemma92EarlyRawRealization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3)))) :
    Nonempty (Lemma92EarlyRawRealization a ε η) := by
  rcases a.exists_lemma92EarlyScaledOrthogonalBasis ε η hadjacent with
    ⟨X, hvalues⟩
  have hordersX : X.SameOrders a :=
    a.lemma92EarlyScaled_sameOrders X ε η hεUnit hηUnit hvalues
  have hprefixX : X.PrefixDefectBounds a :=
    a.lemma92EarlyScaled_prefixDefectBounds X ε η hvalues
      hεDefect hηDefect
  have hfullX : IsSquare (X.comparisonPrefixUnit a 4) :=
    a.lemma92EarlyScaled_fullComparisonSquare X ε η hvalues
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      a X hordersX hprefixX hfullX with
    ⟨M, c₀, hreal, hgood⟩
  let c : GoodBONG q M 4 := ⟨c₀, hgood⟩
  have hvalue (i : Fin 4) :
      c.valueUnit i = a.lemma92EarlyScaledValues ε η i := by
    calc
      c.valueUnit i = X.valueUnit i :=
        (X.valueUnit_eq_of_isRealizedBy hreal i).symm
      _ = a.lemma92EarlyScaledValues ε η i := hvalues i
  have horders : a.SameOrders c := by
    intro i
    calc
      a.order i = X.order i := (hordersX i).symm
      _ = c.order i := X.order_eq_of_isRealizedBy hreal i
  have hprefix : a.PrefixDefectBounds c :=
    X.prefixDefectBounds_of_isRealizedBy a hreal hprefixX
  have hfull : IsSquare (comparisonPrefixUnit a c 4) := by
    change IsSquare (a.prefixProduct 4 * c.prefixProduct 4)
    rw [← X.prefixProduct_eq_of_isRealizedBy (b := c) hreal 4]
    exact hfullX
  have halpha (i : Fin 3) : a.alphaValue i ≤ c.alphaValue i :=
    beli2019Lemma86_ii a c horders hprefix hfull i
  exact ⟨{
    lattice := M
    transformed := c
    firstValue_eq := (hvalue 0).trans
      (a.lemma92EarlyScaledValues_zero ε η)
    secondValue_eq := (hvalue 1).trans
      (a.lemma92EarlyScaledValues_one ε η)
    thirdValue_eq := (hvalue 2).trans
      (a.lemma92EarlyScaledValues_two ε η)
    fourthValue_eq := (hvalue 3).trans
      (a.lemma92EarlyScaledValues_three ε η)
    sameOrders := horders
    prefixDefectBounds := hprefix
    fullComparisonSquare := hfull
    sourceAlpha_le := halpha
  }⟩

namespace Lemma92EarlyRawRealization

/-- The first adjacent defect of the prescribed family is the defect of
`-εa₁a₂`. -/
theorem adjacentDefect_zero
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η) :
    D.transformed.adjacentDefect (0 : Fin 3) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (0 : Fin 4) *
          a.valueUnit (1 : Fin 4))) := by
  unfold adjacentDefect adjacentProduct
  change defectOrder (K := K)
      (-(D.transformed.valueUnit (0 : Fin 4) *
        D.transformed.valueUnit (1 : Fin 4))) = _
  rw [D.firstValue_eq, D.secondValue_eq]
  congr 1
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

/-- The square factor `η²` disappears from the last adjacent defect. -/
theorem adjacentDefect_two
    [QuadraticDefectLaws K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η) :
    D.transformed.adjacentDefect (2 : Fin 3) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (2 : Fin 4) *
          a.valueUnit (3 : Fin 4))) := by
  unfold adjacentDefect adjacentProduct
  change defectOrder (K := K)
      (-(D.transformed.valueUnit (2 : Fin 4) *
        D.transformed.valueUnit (3 : Fin 4))) = _
  rw [D.thirdValue_eq, D.fourthValue_eq]
  have hproduct :
      -((ε * η * a.valueUnit (2 : Fin 4)) *
          (η * a.valueUnit (3 : Fin 4))) =
        (-(ε * a.valueUnit (2 : Fin 4) *
          a.valueUnit (3 : Fin 4))) * η ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- Equality of the first defining adjacent candidate gives equality of the
first alpha, using the lower bound supplied by Lemma 8.6(ii). -/
theorem firstAlpha_eq_of_candidate_eq
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hcandidate :
      (((D.transformed.orderGap (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ)) :
    a.alphaValue (0 : Fin 3) =
      D.transformed.alphaValue (0 : Fin 3) := by
  have hupperTop :=
    BONG.OrthogonalBasisData.alpha_le_orderGap_add_sourceAdjacent
      D.transformed (0 : Fin 3)
  rw [hcandidate] at hupperTop
  have hupper : D.transformed.alphaValue (0 : Fin 3) ≤
      a.alphaValue (0 : Fin 3) := by
    exact_mod_cast hupperTop
  exact le_antisymm (D.sourceAlpha_le 0) hupper

/-- The analogous final-candidate equality gives equality of the third
alpha. -/
theorem lastAlpha_eq_of_candidate_eq
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hcandidate :
      (((D.transformed.orderGap (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (2 : Fin 3) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    a.alphaValue (2 : Fin 3) =
      D.transformed.alphaValue (2 : Fin 3) := by
  have hupperTop :=
    BONG.OrthogonalBasisData.alpha_le_orderGap_add_sourceAdjacent
      D.transformed (2 : Fin 3)
  rw [hcandidate] at hupperTop
  have hupper : D.transformed.alphaValue (2 : Fin 3) ≤
      a.alphaValue (2 : Fin 3) := by
    exact_mod_cast hupperTop
  exact le_antisymm (D.sourceAlpha_le 2) hupper

/-- In the strict-outer-order branch, equality of the first alpha and the
paper's common right-endpoint relation force equality of all three alphas. -/
theorem sameAlphas_of_firstAlpha_eq_of_sourceRightEndpoints
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hfirst : a.alphaValue (0 : Fin 3) =
      D.transformed.alphaValue (0 : Fin 3))
    (hsource : ∀ i : Fin 3,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3)) :
    a.SameAlphas D.transformed := by
  intro i
  apply le_antisymm (D.sourceAlpha_le i)
  have hmono := D.transformed.alphaRightEndpoint_antitone
    (show (0 : Fin 3) ≤ i by omega)
  have hsourceI := hsource i
  unfold alphaRightEndpoint at hmono hsourceI
  have hiOrder := D.sameOrders i.succ
  have hzeroOrder := D.sameOrders (0 : Fin 3).succ
  rw [← hiOrder, ← hzeroOrder, ← hfirst] at hmono
  linarith

/-- The equal-outer-order branch only needs equality at the last alpha; the
common left endpoints of an alternating quaternary BONG propagate it back to
the other two indices. -/
theorem sameAlphas_of_quaternaryAlternating_last
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (ha : a.HasQuaternaryAlternatingOrders)
    (hlast : a.alphaValue (2 : Fin 3) =
      D.transformed.alphaValue (2 : Fin 3)) :
    a.SameAlphas D.transformed := by
  have hb : D.transformed.HasQuaternaryAlternatingOrders := by
    constructor
    · calc
        D.transformed.order (0 : Fin 4) = a.order (0 : Fin 4) :=
          (D.sameOrders 0).symm
        _ = a.order (2 : Fin 4) := ha.1
        _ = D.transformed.order (2 : Fin 4) := D.sameOrders 2
    · calc
        D.transformed.order (1 : Fin 4) = a.order (1 : Fin 4) :=
          (D.sameOrders 1).symm
        _ = a.order (3 : Fin 4) := ha.2
        _ = D.transformed.order (3 : Fin 4) := D.sameOrders 3
  have haEndpoints := a.alphaLeftEndpoints_eq_of_quaternaryAlternating ha
  have hbEndpoints :=
    D.transformed.alphaLeftEndpoints_eq_of_quaternaryAlternating hb
  intro i
  fin_cases i
  · change a.alphaValue (0 : Fin 3) =
      D.transformed.alphaValue (0 : Fin 3)
    have ha02 := haEndpoints.1.trans haEndpoints.2
    have hb02 := hbEndpoints.1.trans hbEndpoints.2
    unfold alphaLeftEndpoint at ha02 hb02
    rw [D.sameOrders (0 : Fin 3).castSucc,
      D.sameOrders (2 : Fin 3).castSucc, hlast] at ha02
    linarith
  · change a.alphaValue (1 : Fin 3) =
      D.transformed.alphaValue (1 : Fin 3)
    have ha12 := haEndpoints.2
    have hb12 := hbEndpoints.2
    unfold alphaLeftEndpoint at ha12 hb12
    rw [D.sameOrders (1 : Fin 3).castSucc,
      D.sameOrders (2 : Fin 3).castSucc, hlast] at ha12
    linarith
  · exact hlast

/-- For classification condition (iv), the first possible clause follows
from the unchanged first coefficient; the second is excluded by the strict
alpha-sum estimate in the paper. -/
theorem internalRepresentationConditions_of_lastAlphaSum_le
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hAlphaSum :
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) ≤
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
      change (D.transformed.valueUnit (0 : Fin 4) : K) =
        (a.valueUnit (0 : Fin 4) : K)
      exact congrArg Units.val D.firstValue_eq
    rw [hpref]
    exact a.prefixValues_represents_succ 1 (by omega)
  · change 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) at htrigger
    exact (not_lt_of_ge hAlphaSum htrigger).elim

/-- Once the remaining alpha equalities and internal representation clauses
have been proved, Beli's 2009 classification transports the prescribed good
BONG back to the original quaternary lattice. -/
theorem toEarlyScalingData
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hsameAlphas : a.SameAlphas D.transformed)
    (hinternal : a.InternalRepresentationConditions D.transformed) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  have hconditions : ClassificationConditions a D.transformed :=
    ⟨D.sameOrders, hsameAlphas, D.prefixDefectBounds, hinternal⟩
  have hisometric : Lattice.IsIsometric q q L D.lattice :=
    (isometric_iff_classificationConditions
      (QuadraticSpace.isIsometric_refl q) a D.transformed).2 hconditions
  rcases hisometric with ⟨f⟩
  let transformed := D.transformed.mapLatticeIsometry f.symm
  have hvalue (i : Fin 4) :
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
  }⟩

/-- Completion of the strict-outer-order classification branch from its two
explicit numerical ingredients. -/
theorem toEarlyScalingData_of_firstCandidate
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (hcandidate :
      (((D.transformed.orderGap (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsource : ∀ i : Fin 3,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3))
    (hAlphaSum :
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ)) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  have hfirst := D.firstAlpha_eq_of_candidate_eq hcandidate
  have halphas :=
    D.sameAlphas_of_firstAlpha_eq_of_sourceRightEndpoints hfirst hsource
  have hinternal :=
    D.internalRepresentationConditions_of_lastAlphaSum_le hAlphaSum
  exact D.toEarlyScalingData halphas hinternal

/-- Completion of the equal-outer-order classification branch from the final
adjacent candidate used in the paper. -/
theorem toEarlyScalingData_of_lastCandidate
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L 4} {ε η : Kˣ}
    (D : Lemma92EarlyRawRealization a ε η)
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hcandidate :
      (((D.transformed.orderGap (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (2 : Fin 3) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  have hlast := D.lastAlpha_eq_of_candidate_eq hcandidate
  have halphas :=
    D.sameAlphas_of_quaternaryAlternating_last halternating hlast
  have hinternal :=
    a.internalRepresentationConditions_of_quaternaryAlternating
      D.transformed halternating
  exact D.toEarlyScalingData halphas hinternal

end Lemma92EarlyRawRealization

/-- Exact rank-four construction in the `R₁ < R₃` branch, parameterized by
the two units and the explicit Hilbert/defect calculations made in the
paper. -/
theorem exists_lemma92EarlyScalingData_of_firstCandidate
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))))
    (hfirstCandidate :
      (((a.orderGap (0 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K)
            (-(ε * a.valueUnit (0 : Fin 4) *
              a.valueUnit (1 : Fin 4))) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hsource : ∀ i : Fin 3,
      a.alphaRightEndpoint i = a.alphaRightEndpoint (0 : Fin 3))
    (hAlphaSum :
      a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ)) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  rcases a.exists_lemma92EarlyRawRealization ε η hεUnit hηUnit
      (hεDefect ▸ le_rfl) (hηDefect ▸ le_rfl) hadjacent with ⟨D⟩
  have hgap : D.transformed.orderGap (0 : Fin 3) =
      a.orderGap (0 : Fin 3) := by
    unfold orderGap
    rw [← D.sameOrders (0 : Fin 3).succ,
      ← D.sameOrders (0 : Fin 3).castSucc]
  have hcandidate :
      (((D.transformed.orderGap (0 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (0 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    rw [hgap, D.adjacentDefect_zero]
    exact hfirstCandidate
  exact D.toEarlyScalingData_of_firstCandidate
    hcandidate hsource hAlphaSum

/-- Exact rank-four construction in the alternating-order branch
`R₁ = R₃`, `R₂ = R₄`. -/
theorem exists_lemma92EarlyScalingData_of_lastCandidate
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : defectOrder (K := K) ε =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hηDefect : defectOrder (K := K) η =
      (a.alphaValue (2 : Fin 3) : WithTop ℚ))
    (hadjacent :
      hilbertSymbol K
          (-(η * a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(ε * a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.tail.valueUnit (0 : Fin 3) *
            a.tail.valueUnit (1 : Fin 3)))
          (-(a.tail.valueUnit (1 : Fin 3) *
            a.tail.valueUnit (2 : Fin 3))))
    (halternating : a.HasQuaternaryAlternatingOrders)
    (hlastCandidate :
      (((a.orderGap (2 : Fin 3) : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K)
            (-(ε * a.valueUnit (2 : Fin 4) *
              a.valueUnit (3 : Fin 4))) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ)) :
    Nonempty (Lemma92EarlyScalingData a ε η) := by
  rcases a.exists_lemma92EarlyRawRealization ε η hεUnit hηUnit
      (hεDefect ▸ le_rfl) (hηDefect ▸ le_rfl) hadjacent with ⟨D⟩
  have hgap : D.transformed.orderGap (2 : Fin 3) =
      a.orderGap (2 : Fin 3) := by
    unfold orderGap
    rw [← D.sameOrders (2 : Fin 3).succ,
      ← D.sameOrders (2 : Fin 3).castSucc]
  have hcandidate :
      (((D.transformed.orderGap (2 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + D.transformed.adjacentDefect (2 : Fin 3) =
        (a.alphaValue (2 : Fin 3) : WithTop ℚ) := by
    rw [hgap, D.adjacentDefect_two]
    exact hlastCandidate
  exact D.toEarlyScalingData_of_lastCandidate halternating hcandidate

end BONG.GoodBONG

end Bong
