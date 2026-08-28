/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41
import Bong.Bong.Segment

/-!
# Beli (2003), Lemma 4.3

This file gives a precise meaning to an orthogonal basis being a BONG "for
some lattice" and to the existence of every adjacent binary BONG.  The
only-if directions of Lemma 4.3(i),(ii) are proved from consecutive-segment
realization and Corollary 4.2.  The constructive converse and the improper
maximal-norm blocking are isolated in `BeliLemma43ConstructionLaws`, with no
default instance.
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

/-- An orthogonal field basis, the input data of Beli's Lemma 4.3. -/
structure OrthogonalBasisData (q : QuadraticSpace K V) (n : Nat) where
  /-- The underlying field basis. -/
  basis : Basis (Fin n) K V
  /-- Distinct basis vectors are orthogonal. -/
  orthogonal : q.bilin.iIsOrtho basis

namespace OrthogonalBasisData

variable (X : OrthogonalBasisData q n)

/-- The quadratic value of an orthogonal basis vector. -/
noncomputable def value (i : Fin n) : K :=
  q.quadratic (X.basis i)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Every diagonal value of an orthogonal basis is nonzero. -/
theorem value_ne_zero (i : Fin n) : X.value i ≠ 0 := by
  change q.bilin (X.basis i) (X.basis i) ≠ 0
  exact X.orthogonal.not_isOrtho_basis_self_of_nondegenerate
    q.nondegenerate i

/-- A diagonal value bundled as a nonzero field element. -/
noncomputable def valueUnit (i : Fin n) : Kˣ :=
  Units.mk0 (X.value i) (X.value_ne_zero i)

/-- The order `R_i` of an orthogonal basis vector. -/
noncomputable def order (i : Fin n) : Int :=
  ordUnit K (X.valueUnit i)

@[simp]
theorem coe_valueUnit (i : Fin n) : (X.valueUnit i : K) = X.value i :=
  rfl

end OrthogonalBasisData

/-- A BONG has exactly the vectors of the supplied orthogonal basis. -/
def OrthogonalBasisData.IsRealizedBy (X : OrthogonalBasisData q n)
    {L : Lattice K V} (b : BONG V q L n) : Prop :=
  ∀ i, b.ambientVector i = X.basis i

namespace OrthogonalBasisData

variable {X : OrthogonalBasisData q n} {b : BONG V q L n}

/-- Realization identifies the quadratic-value sequences. -/
theorem value_eq_of_isRealizedBy (h : X.IsRealizedBy b) (i : Fin n) :
    X.value i = b.value i := by
  rw [← b.quadratic_ambientVector i]
  exact congrArg q.quadratic (h i).symm

/-- Realization identifies the order sequences. -/
theorem order_eq_of_isRealizedBy (h : X.IsRealizedBy b) (i : Fin n) :
    X.order i = b.order i := by
  apply WithTop.coe_injective
  rw [order, coe_ordUnit, BONG.coe_order]
  change ord K (X.value i) = ord K (b.value i)
  rw [X.value_eq_of_isRealizedBy h i]

/-- The basis is a BONG of some lattice having property A. -/
def HasPropertyARealization (X : OrthogonalBasisData q n) : Prop :=
  ∃ (L : Lattice K V) (b : BONG V q L n),
    X.IsRealizedBy b ∧ Lattice.HasJordanPropertyA q L

/-- The basis is a good BONG of some lattice. -/
def HasGoodRealization (X : OrthogonalBasisData q n) : Prop :=
  ∃ (L : Lattice K V) (b : BONG V q L n),
    X.IsRealizedBy b ∧ b.IsGood

/-- The strict two-step inequalities in Lemma 4.3(i). -/
def HasStrictTwoStepOrder (X : OrthogonalBasisData q n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 2 < n),
    X.order i < X.order ⟨i.1 + 2, hi⟩

/-- The weak two-step inequalities in Lemma 4.3(ii). -/
def HasWeakTwoStepOrder (X : OrthogonalBasisData q n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 2 < n),
    X.order i ≤ X.order ⟨i.1 + 2, hi⟩

end OrthogonalBasisData

/-- A concrete binary BONG realizing two adjacent vectors. -/
structure AdjacentPairWitness (X : OrthogonalBasisData q n)
    (i : Fin n) (hi : i.1 + 1 < n) where
  /-- The nondegenerate binary carrier. -/
  carrier : Submodule K V
  /-- Nondegeneracy of the restricted binary form. -/
  nondegenerate : (q.bilin.restrict carrier).Nondegenerate
  /-- The binary lattice. -/
  lattice : Lattice K carrier
  /-- A BONG of that binary lattice. -/
  bong : BONG carrier (q.restrict carrier nondegenerate) lattice 2
  /-- Its first vector is the requested basis vector. -/
  ambientVector_zero : (bong.ambientVector 0 : V) = X.basis i
  /-- Its second vector is the next requested basis vector. -/
  ambientVector_one :
    (bong.ambientVector 1 : V) = X.basis ⟨i.1 + 1, hi⟩

/-- Every adjacent orthogonal pair occurs as a binary BONG. -/
def OrthogonalBasisData.HasAdjacentBONGs
    (X : OrthogonalBasisData q n) : Prop :=
  ∀ (i : Fin n) (hi : i.1 + 1 < n),
    Nonempty (AdjacentPairWitness X i hi)

namespace OrthogonalBasisData

variable {X : OrthogonalBasisData q n} {b : BONG V q L n}

/-- A realized global BONG supplies every adjacent binary BONG. -/
theorem hasAdjacentBONGs_of_isRealizedBy (h : X.IsRealizedBy b) :
    X.HasAdjacentBONGs := by
  intro i hi
  have hbound : i.1 + 2 ≤ n := by omega
  rcases b.exists_segmentWitness i.1 2 hbound with ⟨w⟩
  refine ⟨{
    carrier := w.carrier
    nondegenerate := w.nondegenerate
    lattice := w.lattice
    bong := w.bong
    ambientVector_zero := ?_
    ambientVector_one := ?_
  }⟩
  · calc
      (w.bong.ambientVector 0 : V) =
          b.ambientVector ⟨i.1 + (0 : Fin 2).1, by omega⟩ :=
        w.ambientVector_eq 0
      _ = b.ambientVector i := by congr
      _ = X.basis i := h i
  · calc
      (w.bong.ambientVector 1 : V) =
          b.ambientVector ⟨i.1 + (1 : Fin 2).1, by omega⟩ :=
        w.ambientVector_eq 1
      _ = b.ambientVector ⟨i.1 + 1, hi⟩ := by congr
      _ = X.basis ⟨i.1 + 1, hi⟩ := h _

/-- The only-if direction of Lemma 4.3(ii). -/
theorem conditions_of_hasGoodRealization (hX : X.HasGoodRealization) :
    X.HasAdjacentBONGs ∧ X.HasWeakTwoStepOrder := by
  rcases hX with ⟨L, b, hreal, hgood⟩
  refine ⟨X.hasAdjacentBONGs_of_isRealizedBy hreal, ?_⟩
  intro i hi
  rw [X.order_eq_of_isRealizedBy hreal,
    X.order_eq_of_isRealizedBy hreal]
  exact hgood i hi

end OrthogonalBasisData

/-- All binary blocks in a component family are improper modular. -/
def AllBinaryComponentsImproper
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily) : Prop :=
  ∀ (i : Fin t)
      (h : M.toOrthogonalDecomposition.componentRank i = 2),
    ((c i).castLength h).IsImproperModular

end BONG

/-- The constructive inputs in Beli (2003), Lemma 4.3. -/
class BeliLemma43ConstructionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- The constructive if-direction of Lemma 4.3(i). -/
  propertyA_of_conditions
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : BONG.OrthogonalBasisData q n) :
    X.HasAdjacentBONGs → X.HasStrictTwoStepOrder →
      X.HasPropertyARealization
  /-- The constructive if-direction of Lemma 4.3(ii). -/
  good_of_conditions
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {n : Nat}
    (X : BONG.OrthogonalBasisData q n) :
    X.HasAdjacentBONGs → X.HasWeakTwoStepOrder → X.HasGoodRealization
  /-- Lemma 4.3(iii), including the improper-binary refinement. -/
  good_has_improper_maximalNormSplitting
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (hgood : b.IsGood) :
    ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
        (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
      b.IsPutTogether M.toOrthogonalDecomposition c ∧
        BONG.AllBinaryComponentsImproper M c

namespace BONG.OrthogonalBasisData

variable {X : OrthogonalBasisData q n}
  [BeliLemma43ConstructionLaws.{u, v} K]

/-- The if-direction of Beli (2003), Lemma 4.3(i). -/
theorem hasPropertyARealization_of_conditions
    (hpairs : X.HasAdjacentBONGs) (horder : X.HasStrictTwoStepOrder) :
    X.HasPropertyARealization :=
  BeliLemma43ConstructionLaws.propertyA_of_conditions X hpairs horder

/-- The if-direction of Beli (2003), Lemma 4.3(ii). -/
theorem hasGoodRealization_of_conditions
    (hpairs : X.HasAdjacentBONGs) (horder : X.HasWeakTwoStepOrder) :
    X.HasGoodRealization :=
  BeliLemma43ConstructionLaws.good_of_conditions X hpairs horder

/-- Beli (2003), Lemma 4.3(ii). -/
theorem hasGoodRealization_iff :
    X.HasGoodRealization ↔
      X.HasAdjacentBONGs ∧ X.HasWeakTwoStepOrder := by
  constructor
  · exact X.conditions_of_hasGoodRealization
  · rintro ⟨hpairs, horder⟩
    exact X.hasGoodRealization_of_conditions hpairs horder

end BONG.OrthogonalBasisData

namespace BONG

variable [BeliLemma43ConstructionLaws.{u, v} K]

/-- Beli (2003), Lemma 4.3(iii). -/
theorem beliLemma43_iii (b : BONG V q L n) (hgood : b.IsGood) :
    ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
        (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
      b.IsPutTogether M.toOrthogonalDecomposition c ∧
        AllBinaryComponentsImproper M c :=
  BeliLemma43ConstructionLaws.good_has_improper_maximalNormSplitting b hgood

end BONG

namespace BONG.OrthogonalBasisData

variable {X : BONG.OrthogonalBasisData q n}
  [BONGStructuralLaws.{u, v} K]

/-- The only-if direction of Lemma 4.3(i). -/
theorem conditions_of_hasPropertyARealization
    (hX : X.HasPropertyARealization) :
    X.HasAdjacentBONGs ∧ X.HasStrictTwoStepOrder := by
  rcases hX with ⟨L, b, hreal, hproperty⟩
  refine ⟨X.hasAdjacentBONGs_of_isRealizedBy hreal, ?_⟩
  have hb := b.beliCorollary42_i hproperty
  intro i hi
  rw [X.order_eq_of_isRealizedBy hreal,
    X.order_eq_of_isRealizedBy hreal]
  exact hb i hi

variable [BeliLemma43ConstructionLaws.{u, v} K]

/-- Beli (2003), Lemma 4.3(i). -/
theorem hasPropertyARealization_iff :
    X.HasPropertyARealization ↔
      X.HasAdjacentBONGs ∧ X.HasStrictTwoStepOrder := by
  constructor
  · exact X.conditions_of_hasPropertyARealization
  · rintro ⟨hpairs, horder⟩
    exact X.hasPropertyARealization_of_conditions hpairs horder

end BONG.OrthogonalBasisData

end Bong
