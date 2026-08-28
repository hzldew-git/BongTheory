/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalQuaternaryComplement
import Bong.Bong.DiagonalCodimensionTwoRepresentation
import Bong.Bong.TernaryExactRealization
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quaternary complements from codimension-two representation

This file derives the quaternary universality/complement interface from the
more primitive codimension-two local representation theorem.  First, every
represented binary diagonal form is completed by the orthogonal two-
dimensional complement of its image.  A suitable auxiliary binary line is
then chosen so that the codimension-two theorem applies.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

namespace DiagonalRepresents

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A represented nondegenerate binary diagonal form in a quaternary form
can be completed by an orthogonal binary complement. -/
theorem binary_complete_to_quaternary
    (source : Fin 2 → Kˣ) (target : Fin 4 → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    ∃ c : Fin 2 → Kˣ,
      DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append source c))
        (diagonalUnitCoefficients target) := by
  classical
  let sourceCoefficients : Fin 2 → K := diagonalUnitCoefficients source
  let targetCoefficients : Fin 4 → K := diagonalUnitCoefficients target
  have hsource : ∀ i, sourceCoefficients i ≠ 0 :=
    fun i ↦ Units.ne_zero (source i)
  have htarget : ∀ i, targetCoefficients i ≠ 0 :=
    fun i ↦ Units.ne_zero (target i)
  let qs := QuadraticSpace.finiteDiagonal sourceCoefficients hsource
  let qt := QuadraticSpace.finiteDiagonal targetCoefficients htarget
  have hspace : qt.Represents qs := by
    exact toQuadraticSpaceRepresents hsource htarget hrep
  rcases hspace with ⟨F⟩
  let rangeEquiv : (Fin 2 → K) ≃ₗ[K] LinearMap.range F.toLinearMap :=
    LinearEquiv.ofBijective F.toLinearMap.rangeRestrict
      ⟨by
        intro x y hxy
        apply F.injective
        exact congrArg Subtype.val hxy,
        LinearMap.surjective_rangeRestrict _⟩
  have hRangeNondegenerate :
      (qt.bilin.restrict (LinearMap.range F.toLinearMap)).Nondegenerate := by
    have hform :
        qt.bilin.restrict (LinearMap.range F.toLinearMap) =
          LinearMap.BilinForm.congr rangeEquiv qs.bilin := by
      ext x y
      change qt.bilin (x : Fin 4 → K) (y : Fin 4 → K) =
        qs.bilin (rangeEquiv.symm x) (rangeEquiv.symm y)
      rw [← F.map_bilin]
      congr 2
      · exact (congrArg Subtype.val
          (rangeEquiv.apply_symm_apply x)).symm
      · exact (congrArg Subtype.val
          (rangeEquiv.apply_symm_apply y)).symm
    rw [hform]
    exact qs.nondegenerate.congr rangeEquiv
  let range := LinearMap.range F.toLinearMap
  let complement := qt.bilin.orthogonal range
  have hRangeCompl : IsCompl range complement :=
    qt.bilin.isCompl_orthogonal_of_restrict_nondegenerate
      qt.isSymm.isRefl hRangeNondegenerate
  have hComplementNondegenerate :
      (qt.bilin.restrict complement).Nondegenerate := by
    rw [qt.bilin.restrict_nondegenerate_iff_isCompl_orthogonal
      qt.isSymm.isRefl]
    have horth : qt.bilin.orthogonal complement = range := by
      exact qt.bilin.orthogonal_orthogonal qt.nondegenerate
        qt.isSymm.isRefl range
    rw [horth]
    exact hRangeCompl.symm
  have hComplementFinrank : Module.finrank K complement = 2 := by
    change Module.finrank K
        (qt.bilin.orthogonal (LinearMap.range F.toLinearMap)) = 2
    rw [qt.bilin.finrank_orthogonal qt.nondegenerate,
      LinearMap.finrank_range_of_inj F.injective]
    simp
  have hexistsBasis := LinearMap.BilinForm.exists_orthogonal_basis
    (B := qt.bilin.restrict complement)
    ((LinearMap.BilinForm.isSymm_iff).mp
      (qt.isSymm.restrict complement))
  rw [hComplementFinrank] at hexistsBasis
  rcases hexistsBasis with ⟨complementBasis, hComplementOrthogonal⟩
  have hComplementIOrtho :
      (qt.bilin.restrict complement).iIsOrtho complementBasis :=
    hComplementOrthogonal
  have hComplementValue (i : Fin 2) :
      qt.quadratic (complementBasis i : Fin 4 → K) ≠ 0 := by
    change qt.bilin (complementBasis i : Fin 4 → K)
      (complementBasis i : Fin 4 → K) ≠ 0
    exact hComplementIOrtho.not_isOrtho_basis_self_of_nondegenerate
      hComplementNondegenerate i
  let c : Fin 2 → Kˣ := fun i ↦
    Units.mk0 (qt.quadratic (complementBasis i : Fin 4 → K))
      (hComplementValue i)
  let reindex : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 4 → K) :=
    LinearEquiv.piCongrLeft K (fun _ : Fin 4 ↦ K) finSumFinEquiv
  have hreindex_symm_apply (x : Fin 4 → K) (i : Fin 2 ⊕ Fin 2) :
      reindex.symm x i = x (finSumFinEquiv i) := by
    rfl
  let split : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)) :=
    reindex.symm.trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) K K)
  let assemble : ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] (Fin 4 → K) :=
    (rangeEquiv.prodCongr complementBasis.equivFun.symm).trans
      (range.prodEquivOfIsCompl complement hRangeCompl)
  let fullEquiv : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
    split.trans assemble
  let newBasis : Basis (Fin 4) K (Fin 4 → K) :=
    (Pi.basisFun K (Fin 4)).map fullEquiv
  have hsplit_zero : split (Pi.basisFun K (Fin 4) (0 : Fin 4)) =
      (Pi.basisFun K (Fin 2) (0 : Fin 2), 0) := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
  have hsplit_one : split (Pi.basisFun K (Fin 4) (1 : Fin 4)) =
      (Pi.basisFun K (Fin 2) (1 : Fin 2), 0) := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
  have hsplit_two : split (Pi.basisFun K (Fin 4) (2 : Fin 4)) =
      (0, Pi.basisFun K (Fin 2) (0 : Fin 2)) := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
  have hsplit_three : split (Pi.basisFun K (Fin 4) (3 : Fin 4)) =
      (0, Pi.basisFun K (Fin 2) (1 : Fin 2)) := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
    · funext i
      fin_cases i <;>
        simp [split, hreindex_symm_apply, finSumFinEquiv]
  have hnewBasis_zero : newBasis (0 : Fin 4) =
      F.toLinearMap (Pi.basisFun K (Fin 2) (0 : Fin 2)) := by
    change assemble (split (Pi.basisFun K (Fin 4) (0 : Fin 4))) = _
    rw [hsplit_zero]
    simp [assemble, rangeEquiv, range, complement]
  have hnewBasis_one : newBasis (1 : Fin 4) =
      F.toLinearMap (Pi.basisFun K (Fin 2) (1 : Fin 2)) := by
    change assemble (split (Pi.basisFun K (Fin 4) (1 : Fin 4))) = _
    rw [hsplit_one]
    simp [assemble, rangeEquiv, range, complement]
  have hnewBasis_two : newBasis (2 : Fin 4) =
      (complementBasis (0 : Fin 2) : Fin 4 → K) := by
    change assemble (split (Pi.basisFun K (Fin 4) (2 : Fin 4))) = _
    rw [hsplit_two]
    simp [assemble, rangeEquiv, range, complement]
  have hnewBasis_three : newBasis (3 : Fin 4) =
      (complementBasis (1 : Fin 2) : Fin 4 → K) := by
    change assemble (split (Pi.basisFun K (Fin 4) (3 : Fin 4))) = _
    rw [hsplit_three]
    simp [assemble, rangeEquiv, range, complement]
  have hsourceOrthogonal (i j : Fin 2) (hij : i ≠ j) :
      qt.bilin
          (F.toLinearMap (Pi.basisFun K (Fin 2) i))
          (F.toLinearMap (Pi.basisFun K (Fin 2) j)) = 0 := by
    rw [F.map_bilin, QuadraticSpace.finiteDiagonal_bilin_apply]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp [sourceCoefficients, diagonalUnitCoefficients]
    · simp [sourceCoefficients, diagonalUnitCoefficients]
    · exact (hij rfl).elim
  have hsourceComplement (i j : Fin 2) :
      qt.bilin
          (F.toLinearMap (Pi.basisFun K (Fin 2) i))
          (complementBasis j : Fin 4 → K) = 0 := by
    exact (complementBasis j).property _
      ⟨Pi.basisFun K (Fin 2) i, rfl⟩
  have hcomplementSource (i j : Fin 2) :
      qt.bilin
          (complementBasis i : Fin 4 → K)
          (F.toLinearMap (Pi.basisFun K (Fin 2) j)) = 0 := by
    rw [qt.isSymm.eq]
    exact hsourceComplement j i
  have hcomplementOrthogonal (i j : Fin 2) (hij : i ≠ j) :
      qt.bilin
          (complementBasis i : Fin 4 → K)
          (complementBasis j : Fin 4 → K) = 0 := by
    exact (LinearMap.BilinForm.iIsOrtho_def.mp hComplementIOrtho)
      i j hij
  have horthogonal : qt.bilin.iIsOrtho newBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [hnewBasis_zero, hnewBasis_one] using
        hsourceOrthogonal 0 1 (by decide)
    · simpa [hnewBasis_zero, hnewBasis_two] using
        hsourceComplement 0 0
    · simpa [hnewBasis_zero, hnewBasis_three] using
        hsourceComplement 0 1
    · simpa [hnewBasis_one, hnewBasis_zero] using
        hsourceOrthogonal 1 0 (by decide)
    · exact (hij rfl).elim
    · simpa [hnewBasis_one, hnewBasis_two] using
        hsourceComplement 1 0
    · simpa [hnewBasis_one, hnewBasis_three] using
        hsourceComplement 1 1
    · simpa [hnewBasis_two, hnewBasis_zero] using
        hcomplementSource 0 0
    · simpa [hnewBasis_two, hnewBasis_one] using
        hcomplementSource 0 1
    · exact (hij rfl).elim
    · simpa [hnewBasis_two, hnewBasis_three] using
        hcomplementOrthogonal 0 1 (by decide)
    · simpa [hnewBasis_three, hnewBasis_zero] using
        hcomplementSource 1 0
    · simpa [hnewBasis_three, hnewBasis_one] using
        hcomplementSource 1 1
    · simpa [hnewBasis_three, hnewBasis_two] using
        hcomplementOrthogonal 1 0 (by decide)
    · exact (hij rfl).elim
  let X : BONG.OrthogonalBasisData qt 4 := ⟨newBasis, horthogonal⟩
  have hXvalue_zero : X.valueUnit (0 : Fin 4) = source 0 := by
    apply Units.ext
    change qt.quadratic (newBasis (0 : Fin 4)) = (source 0 : K)
    rw [hnewBasis_zero, F.map_quadratic,
      QuadraticSpace.finiteDiagonal_quadratic_apply]
    exact diagonalQuadratic_basisFun
      (diagonalUnitCoefficients source) 0
  have hXvalue_one : X.valueUnit (1 : Fin 4) = source 1 := by
    apply Units.ext
    change qt.quadratic (newBasis (1 : Fin 4)) = (source 1 : K)
    rw [hnewBasis_one, F.map_quadratic,
      QuadraticSpace.finiteDiagonal_quadratic_apply]
    exact diagonalQuadratic_basisFun
      (diagonalUnitCoefficients source) 1
  have hXvalue_two : X.valueUnit (2 : Fin 4) = c 0 := by
    apply Units.ext
    change qt.quadratic (newBasis (2 : Fin 4)) =
      qt.quadratic (complementBasis (0 : Fin 2) : Fin 4 → K)
    rw [hnewBasis_two]
  have hXvalue_three : X.valueUnit (3 : Fin 4) = c 1 := by
    apply Units.ext
    change qt.quadratic (newBasis (3 : Fin 4)) =
      qt.quadratic (complementBasis (1 : Fin 2) : Fin 4 → K)
    rw [hnewBasis_three]
  have hXvalues (i : Fin 4) :
      X.valueUnit i = Fin.append source c i := by
    refine Fin.addCases (m := 2) (n := 2) ?_ ?_ i
    · intro j
      rw [Fin.append_left]
      fin_cases j
      · simpa using hXvalue_zero
      · simpa using hXvalue_one
    · intro j
      rw [Fin.append_right]
      fin_cases j
      · simpa using hXvalue_two
      · simpa using hXvalue_three
  have hcoefficients :
      diagonalUnitCoefficients (Fin.append source c) = X.value := by
    funext i
    exact (congrArg Units.val (hXvalues i)).symm
  refine ⟨c, ?_⟩
  refine ⟨X.basis.equivFun.symm.toLinearMap,
    X.basis.equivFun.symm.injective, ?_⟩
  intro x
  calc
    diagonalQuadratic (diagonalUnitCoefficients target)
        (X.basis.equivFun.symm x) =
        qt.quadratic (X.basis.equivFun.symm x) := by
          rw [QuadraticSpace.finiteDiagonal_quadratic_apply]
    _ = diagonalQuadratic X.value x :=
      (X.diagonalQuadratic_value_eq x).symm
    _ = diagonalQuadratic
        (diagonalUnitCoefficients (Fin.append source c)) x := by
          rw [hcoefficients]

/-- A square has even additive valuation. -/
private theorem even_ordUnit_of_isSquare (a : Kˣ) (ha : IsSquare a) :
    Even (ordUnit K a) := by
  rcases ha with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

/-- The chosen uniformizer is not a square because its valuation is one. -/
private theorem uniformizerUnit_not_isSquare :
    ¬ IsSquare (uniformizerUnit K) := by
  intro hsquare
  have heven := even_ordUnit_of_isSquare (K := K)
    (uniformizerUnit K) hsquare
  have horder : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [horder] at heven
  rcases heven with ⟨z, hz⟩
  omega

end DiagonalRepresents

/-- The codimension-two local representation theorem implies the
quaternary complement theorem: choose an auxiliary line whose product with
the prescribed determinant class is nonsquare, embed the resulting binary
form, and take its two-dimensional orthogonal complement. -/
noncomputable instance dyadicQuaternaryComplementLawsProved
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [DyadicDiagonalCodimensionTwoLaws K] :
    DyadicQuaternaryComplementLaws K where
  complement b base := by
    classical
    let A : Kˣ := -diagonalUnitDeterminant base * b
    let d : Kˣ :=
      if IsSquare A then uniformizerUnit K else 1
    have hproduct : ¬ IsSquare (A * d) := by
      by_cases hA : IsSquare A
      · have hpi : ¬ IsSquare (uniformizerUnit K) :=
          DiagonalRepresents.uniformizerUnit_not_isSquare (K := K)
        have hnot : ¬ IsSquare (A * uniformizerUnit K) := by
          intro hApi
          have hquotient : IsSquare ((A * uniformizerUnit K) / A) :=
            hApi.div hA
          have heq : (A * uniformizerUnit K) / A = uniformizerUnit K := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm]
          rw [heq] at hquotient
          exact hpi hquotient
        simpa [d, hA] using hnot
      · simpa [d, hA] using hA
    let pair : Fin 2 → Kˣ := ![b, d]
    have hpairDeterminant : diagonalUnitDeterminant pair = b * d := by
      simp [pair, diagonalUnitDeterminant, Fin.prod_univ_two]
    have hdet : ¬ IsSquare
        (-diagonalUnitDeterminant base *
          diagonalUnitDeterminant pair) := by
      rw [hpairDeterminant]
      simpa only [A, mul_assoc] using hproduct
    have hbinary : DiagonalRepresents
        (diagonalUnitCoefficients pair)
        (diagonalUnitCoefficients base) :=
      diagonalRepresents_of_not_negative_determinant_square
        pair base (by omega) hdet
    rcases DiagonalRepresents.binary_complete_to_quaternary
      pair base hbinary with ⟨c, hc⟩
    let tail : Fin 3 → Kˣ := Fin.cons d c
    have htuple : Fin.append pair c = Fin.cons b tail := by
      funext i
      refine Fin.addCases (m := 2) (n := 2) ?_ ?_ i
      · intro j
        rw [Fin.append_left]
        fin_cases j <;> rfl
      · intro j
        rw [Fin.append_right]
        fin_cases j <;> rfl
    refine ⟨tail, ?_⟩
    rw [← htuple]
    exact hc

end Bong
