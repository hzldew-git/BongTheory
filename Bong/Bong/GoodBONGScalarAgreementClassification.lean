/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.GoodBONGScalarAgreement
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.DefectArithmetic

/-!
# Integral classification from literal good-BONG coefficients

Literal equality of the complete coefficient sequences makes all four
conditions in Beli's 2009 classification theorem automatic.  This small
bridge is useful after an integral BONG-normalization argument: it turns the
normalized numerical sequence into an actual integral lattice isometry.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG.ScalarAgreement

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

/-- Literal agreement of good-BONG coefficients implies the four numerical
and representation conditions in Beli's integral classification theorem. -/
theorem classificationConditions (h : ScalarAgreement a b) :
    ClassificationConditions a b := by
  refine {
    sameOrders := h.order_eq
    sameAlphas := h.alphaValue_eq
    prefixDefectBounds := ?_
    internalRepresentations := ?_ }
  · intro i
    have hproduct : a.comparisonPrefixProduct b i =
        a.prefixProduct (i.val + 1) ^ 2 := by
      unfold comparisonPrefixProduct
      rw [← h.prefixProduct_eq (i.val + 1)]
      simp only [pow_two]
    have hsquare : IsSquare (a.comparisonPrefixProduct b i) := by
      refine ⟨a.prefixProduct (i.val + 1), ?_⟩
      rw [hproduct, pow_two]
    rw [BONG.GoodBONG.defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  · intro i _hi _htrigger
    have hprefix :
        b.prefixValues i.val (by omega) =
          a.prefixValues i.val (by omega) := by
      exact (h.prefixValues_eq i.val (by omega)).symm
    rw [hprefix]
    unfold BONG.GoodBONG.prefixValues
    exact DiagonalRepresents.prefixOfLE _ (by omega)

/-- Two equally long good BONGs with literally equal coefficients are
integrally isometric as soon as their ambient quadratic spaces are
isometric.  The deep input is the already proved Beli 2009 classification
theorem, not an additional law parameter. -/
theorem isIsometric (h : ScalarAgreement a b)
    (ambient : q.IsIsometric r) :
    Lattice.IsIsometric q r L M := by
  letI : GoodBONGClassificationLaws.{u, v, w} K :=
    goodBONGClassificationLawsProved K
  exact (isometric_iff_classificationConditions ambient a b).2
    h.classificationConditions

end BONG.GoodBONG.ScalarAgreement

end Bong
