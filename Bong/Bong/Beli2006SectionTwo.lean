/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryScaledExactRealization
import Bong.Bong.BeliLemma319
import Bong.Bong.BeliLemma43

/-!
# Beli (2006), Section 2

This file records the binary similarity invariant, the numerical criterion for
an orthogonal basis to realize a good BONG, and the equivalence between good
BONGs and maximal norm splittings.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG

/-- The invariant `a(L)` of a binary BONG, modulo squares of valuation units. -/
noncomputable def binarySimilarityInvariant (b : BONG V q L 2) :
    UnitSquareClass K :=
  b.binaryUnitSquareClass

/-- The order `R(L)` of the binary similarity invariant. -/
noncomputable def binarySimilarityOrder (b : BONG V q L 2) : Int :=
  b.binaryOrderGap

/-- The order of `a(L)` is the difference of the two BONG orders. -/
theorem binarySimilarityOrder_eq (b : BONG V q L 2) :
    b.binarySimilarityOrder = b.order 1 - b.order 0 :=
  rfl

/-- Every binary BONG supplies an admissible value of Beli's set `A_F`. -/
theorem binarySimilarityInvariant_admissible (b : BONG V q L 2) :
    IsBinaryParameterAdmissible b.binaryParameter :=
  b.binaryParameter_isBinaryParameterAdmissible

namespace OrthogonalBasisData

/-- The scalar ratio attached to two adjacent orthogonal basis vectors. -/
noncomputable def adjacentParameter (X : OrthogonalBasisData q n)
    (i : Fin n) (hi : i.1 + 1 < n) : Kˣ :=
  X.valueUnit ⟨i.1 + 1, hi⟩ / X.valueUnit i

/-- The two numerical conditions in Beli (2006), Definition 2.2. -/
def SatisfiesGoodBONGCriteria (X : OrthogonalBasisData q n) : Prop :=
  X.HasWeakTwoStepOrder ∧
    ∀ (i : Fin n) (hi : i.1 + 1 < n),
      IsBinaryParameterAdmissible (X.adjacentParameter i hi)

/-- An adjacent binary realization identifies its binary parameter with the
corresponding scalar ratio. -/
theorem adjacentPair_binaryParameter_eq
    {X : OrthogonalBasisData q n} {i : Fin n}
    {hi : i.1 + 1 < n} (w : AdjacentPairWitness X i hi) :
    w.bong.binaryParameter = X.adjacentParameter i hi := by
  apply Units.ext
  rw [coe_binaryParameter]
  simp only [adjacentParameter, Units.val_div_eq_div_val, coe_valueUnit]
  rw [← w.bong.quadratic_ambientVector 1,
    ← w.bong.quadratic_ambientVector 0]
  unfold value
  change q.quadratic (w.bong.ambientVector 1 : V) /
      q.quadratic (w.bong.ambientVector 0 : V) = _
  rw [w.ambientVector_zero, w.ambientVector_one]

/-- Adjacent binary realizability implies the admissibility inequalities. -/
theorem admissible_of_hasAdjacentBONGs
    {X : OrthogonalBasisData q n} (h : X.HasAdjacentBONGs) :
    ∀ (i : Fin n) (hi : i.1 + 1 < n),
      IsBinaryParameterAdmissible (X.adjacentParameter i hi) := by
  intro i hi
  rcases h i hi with ⟨w⟩
  rw [← adjacentPair_binaryParameter_eq w]
  exact w.bong.binaryParameter_isBinaryParameterAdmissible

/-- An admissible adjacent parameter has an exact binary realization on the
two prescribed orthogonal basis vectors. -/
noncomputable def adjacentPairWitness_of_admissible
    (X : OrthogonalBasisData q n)
    (i : Fin n) (hi : i.1 + 1 < n)
    (hadmissible : IsBinaryParameterAdmissible (X.adjacentParameter i hi)) :
    AdjacentPairWitness X i hi := by
  let next : Fin n := ⟨i.1 + 1, hi⟩
  let index : Fin 2 → Fin n := ![i, next]
  have hine : i ≠ next := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [next] at hval
    omega
  have hindex : Function.Injective index := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      apply hine
      simpa [index] using hab
    · exfalso
      apply hine
      simpa [index] using hab.symm
    · rfl
  have hli : LinearIndependent K
      (binaryPairFamily (X.basis i) (X.basis next)) := by
    convert X.basis.linearIndependent.comp index hindex using 1
    funext j
    fin_cases j <;> rfl
  let carrier := binaryPairSpan (K := K) (X.basis i) (X.basis next)
  let pairBasis : Basis (Fin 2) K carrier :=
    binaryPairBasis (K := K) (X.basis i) (X.basis next) hli
  have hpairOrtho :
      (q.bilin.restrict carrier).iIsOrtho pairBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro a b hab
    change q.bilin (pairBasis a : V) (pairBasis b : V) = 0
    rw [coe_binaryPairBasis, coe_binaryPairBasis]
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) i next hine
    · exact (LinearMap.BilinForm.iIsOrtho_def.mp X.orthogonal) next i hine.symm
    · exact (hab rfl).elim
  have hpairSelf : ∀ j, (q.bilin.restrict carrier) (pairBasis j) (pairBasis j) ≠ 0 := by
    intro j
    change q.quadratic (pairBasis j : V) ≠ 0
    rw [coe_binaryPairBasis]
    fin_cases j
    · exact X.value_ne_zero i
    · exact X.value_ne_zero next
  have hnondeg : (q.bilin.restrict carrier).Nondegenerate :=
    (hpairOrtho.nondegenerate_iff_not_isOrtho_basis_self
      (q.bilin.restrict carrier) pairBasis).2 hpairSelf
  let targetQ := q.restrict carrier hnondeg
  let first := X.valueUnit i
  let second := X.valueUnit next
  have hparameter : second / first = X.adjacentParameter i hi := rfl
  have hadmissible' : IsBinaryParameterAdmissible (second / first) := by
    rwa [hparameter]
  let source := BONG.scaledBinaryExactBONG first second hadmissible'
  let e : (Fin 2 → K) ≃ₗ[K] carrier :=
    source.basis.equiv pairBasis (Equiv.refl (Fin 2))
  have hforms : targetQ.bilin.comp e.toLinearMap e.toLinearMap =
      (BONG.scaledBinaryModelSpace first second hadmissible').bilin := by
    apply LinearMap.BilinForm.ext_basis source.basis
    intro a b
    rw [LinearMap.BilinForm.comp_apply]
    change q.bilin (e (source.basis a) : V) (e (source.basis b) : V) = _
    simp only [e, Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply]
    by_cases hab : a = b
    · subst b
      rw [show
        (BONG.scaledBinaryModelSpace first second hadmissible').bilin
            (source.basis a) (source.basis a) = source.value a by
          exact source.quadratic_ambientVector a]
      change q.quadratic (pairBasis a : V) = source.value a
      have hpairValue : ∀ j : Fin 2,
          q.quadratic (pairBasis j : V) = ![X.value i, X.value next] j := by
        intro j
        rw [coe_binaryPairBasis]
        fin_cases j <;> rfl
      have hsourceValue : ∀ j : Fin 2,
          source.value j = ![(first : K), (second : K)] j := by
        intro j
        fin_cases j
        · simp [source]
        · simp [source]
      rw [hpairValue a, hsourceValue a]
      fin_cases a
      · change X.value i = (first : K)
        rfl
      · change X.value next = (second : K)
        rfl
    · have hleft :=
        (LinearMap.BilinForm.iIsOrtho_def.mp hpairOrtho) a b hab
      have hright :=
        (LinearMap.BilinForm.iIsOrtho_def.mp source.ambientVector_iIsOrtho) a b hab
      change q.bilin (pairBasis a : V) (pairBasis b : V) =
        (BONG.scaledBinaryModelSpace first second hadmissible').bilin
          (source.ambientVector a) (source.ambientVector b)
      exact hleft.trans hright.symm
  let f : QuadraticSpace.Isometry
      (BONG.scaledBinaryModelSpace first second hadmissible') targetQ :=
    { toLinearEquiv := e
      map_bilin := by
        intro x y
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := source.map f
  refine {
    carrier := carrier
    nondegenerate := hnondeg
    lattice := Lattice.map e (BONG.scaledBinaryModelLattice (K := K))
    bong := mapped
    ambientVector_zero := ?_
    ambientVector_one := ?_
  }
  · change ((mapped.ambientVector 0 : carrier) : V) = X.basis i
    rw [BONG.ambientVector_map]
    change ((e (source.basis 0) : carrier) : V) = X.basis i
    rw [show e (source.basis 0) = pairBasis 0 by simp [e]]
    rw [coe_binaryPairBasis]
    rfl
  · change ((mapped.ambientVector 1 : carrier) : V) = X.basis next
    rw [BONG.ambientVector_map]
    change ((e (source.basis 1) : carrier) : V) = X.basis next
    rw [show e (source.basis 1) = pairBasis 1 by simp [e]]
    rw [coe_binaryPairBasis]
    rfl

/-- Pointwise admissibility gives all adjacent binary realizations. -/
theorem hasAdjacentBONGs_of_admissible
    (X : OrthogonalBasisData q n)
    (h : ∀ (i : Fin n) (hi : i.1 + 1 < n),
      IsBinaryParameterAdmissible (X.adjacentParameter i hi)) :
    X.HasAdjacentBONGs := by
  intro i hi
  exact ⟨X.adjacentPairWitness_of_admissible i hi (h i hi)⟩

end OrthogonalBasisData

end BONG

/-- The local binary realization input in the if-direction of Beli (2006),
Definition 2.2.  This interface has no default instance. -/
class Beli2006SectionTwoLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  adjacentBONGs_of_admissible
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : BONG.OrthogonalBasisData q n) :
    (∀ (i : Fin n) (hi : i.1 + 1 < n),
      BONG.IsBinaryParameterAdmissible (X.adjacentParameter i hi)) →
      X.HasAdjacentBONGs

/-- The exact scaled binary model supplies the realization law in Beli
(2006), Section 2. -/
noncomputable instance beli2006SectionTwoLaws :
    Beli2006SectionTwoLaws.{u, v} K where
  adjacentBONGs_of_admissible X h := X.hasAdjacentBONGs_of_admissible h

namespace BONG.OrthogonalBasisData

variable [BeliLemma43ConstructionLaws.{u, v} K]
  [Beli2006SectionTwoLaws.{u, v} K]

/-- Beli (2006), Definition 2.2: the exact numerical existence criterion for
a good BONG on a prescribed orthogonal basis. -/
theorem hasGoodRealization_iff_beli2006Criteria
    (X : OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.SatisfiesGoodBONGCriteria := by
  rw [X.hasGoodRealization_iff]
  constructor
  · rintro ⟨hpairs, horder⟩
    exact ⟨horder, admissible_of_hasAdjacentBONGs hpairs⟩
  · rintro ⟨horder, hadmissible⟩
    exact ⟨Beli2006SectionTwoLaws.adjacentBONGs_of_admissible
      X hadmissible, horder⟩

end BONG.OrthogonalBasisData

namespace BONG

variable [BeliSectionFourLaws.{u, v} K]
  [BeliLemma43ConstructionLaws.{u, v} K]

/-- Beli (2006), Definition 2.3 and the paragraph following it: good BONGs
are exactly those obtained from maximal norm splittings, with improper binary
components available in the forward direction. -/
theorem isGood_iff_exists_maximalNormSplitting
    (b : BONG V q L n) :
    b.IsGood ↔
      ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
          (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
        b.IsPutTogether M.toOrthogonalDecomposition c ∧
          AllBinaryComponentsImproper M c := by
  constructor
  · exact b.beliLemma43_iii
  · rintro ⟨_t, M, c, hput, _himproper⟩
    exact beliCorollary42_ii M c b hput

end BONG

end Bong
