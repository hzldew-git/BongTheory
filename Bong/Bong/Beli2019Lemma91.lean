/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91ExceptionC
import Bong.Bong.Beli2019NecessityComplete

/-!
# Beli (2019), Lemma 9.1

This file assembles the five branches of Lemma 9.1.  The canonical unary
source is realized by the first prefix of the full source lattice.  Necessity
for that represented prefix supplies the hypotheses of Lemma 8.13, while the
three exception files exclude all alternatives left by Lemma 8.14.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N S : Nat}

/-- The first prefix lattice embeds integrally into its parent lattice. -/
theorem firstUnaryPrefix_represents (c : GoodBONG r M (S + 2)) :
    Lattice.Represents r
      (r.restrict c.firstUnaryPrefixWitness.carrier
        c.firstUnaryPrefixWitness.nondegenerate)
      M c.firstUnaryPrefixWitness.lattice := by
  let w₁ := c.firstUnaryPrefixWitness
  exact ⟨
    { toLinearMap := w₁.carrier.subtype
      injective := Subtype.val_injective
      map_bilin _ _ := rfl
      map_mem := by
        intro x hx
        exact w₁.contained x hx }⟩

/-- A representation of the full source gives the explicit Lemma 8.13
conditions for its canonical unary first prefix. -/
theorem lemma813Conditions_firstUnarySegment_of_representation
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [GoodBONGDeepIntegralExtensionLaws.{u, v, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (representation : Lattice.Represents q r L M) :
    a.Lemma813Conditions c.firstUnarySegment := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
  let w₁ := c.firstUnaryPrefixWitness
  let b := c.firstUnarySegment
  have hprefix : Lattice.Represents r
      (r.restrict w₁.carrier w₁.nondegenerate)
      M w₁.lattice := by
    simpa only [w₁] using c.firstUnaryPrefix_represents
  have hrepresentation : Lattice.Represents q
      (r.restrict w₁.carrier w₁.nondegenerate)
      L w₁.lattice :=
    representation.trans hprefix
  have horder : a.order (0 : Fin (N + 3)) =
      b.order (0 : Fin 1) := by
    calc
      a.order (0 : Fin (N + 3)) = c.order (0 : Fin (S + 2)) := hfirst
      _ = c.firstUnarySegment.order (0 : Fin 1) :=
        c.firstUnarySegment_order_zero.symm
      _ = b.order (0 : Fin 1) := by rfl
  have conditions : RepresentationConditions a b (Nat.zero_le (N + 2)) :=
    beli2019_necessity (sourceLaws := sourceLaws)
      (targetLaws := targetLaws) a b (Nat.zero_le (N + 2)) hrepresentation
  have explicit : a.Lemma813Conditions b :=
    (a.representationConditions_iff_lemma813 b horder
      hrepresentation.ambient).mp conditions
  exact explicit

/-- The five alternatives displayed in Beli (2019), Lemma 9.1. -/
noncomputable def Lemma91Alternative
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2)) : Prop :=
  a.order (0 : Fin (N + 3)) < a.order ⟨2, by omega⟩ ∨
  a.order (1 : Fin (N + 3)) = c.order (1 : Fin (S + 2)) ∨
  a.orderGap (0 : Fin (N + 2)) =
    2 * (ramificationIndex K : Int) ∨
  (∃ hfour : 3 < N + 3,
    a.order (1 : Fin (N + 3)) = a.order ⟨3, hfour⟩) ∨
  (a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) ∧
    a.alphaValue (0 : Fin (N + 2)) <
      c.alphaValue (0 : Fin (S + 1)))

/-- The `R₂ = S₂` branch of Lemma 9.1.  If `R₂ = R₄`, the immediate
order branch applies.  Otherwise goodness gives `R₂ < R₄`, and the three
exception files exclude Lemma 8.14(a)--(c). -/
theorem beli2019Lemma91_of_equalSecondOrder
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (unaryConditions : a.Lemma813Conditions c.firstUnarySegment) :
    Nonempty
      (a.Beli2019PrescribedFirstValueTransform c.firstUnarySegment) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  have horder : a.order (0 : Fin (N + 3)) =
      c.firstUnarySegment.order (0 : Fin 1) :=
    hfirst.trans c.firstUnarySegment_order_zero.symm
  by_cases hequal : ∃ hfour : 3 < N + 3,
      a.order (1 : Fin (N + 3)) = a.order ⟨3, hfour⟩
  · rcases hequal with ⟨hfour, hequal⟩
    exact a.beli2019Lemma91_of_firstThird_lt_or_secondFourth_eq
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c.firstUnarySegment horder unaryConditions (Or.inr ⟨hfour, hequal⟩)
  · have hsecondFourth : ∀ hfour : 3 < N + 3,
        a.order (1 : Fin (N + 3)) < a.order ⟨3, hfour⟩ := by
      intro hfour
      have hle : a.order (1 : Fin (N + 3)) ≤
          a.order ⟨3, hfour⟩ := by
        convert a.good (⟨1, by omega⟩ : Fin (N + 3)) (by omega) using 1 <;>
          congr
      exact lt_of_le_of_ne hle (fun h => hequal ⟨hfour, h⟩)
    have hnotA := a.not_lemma814ExceptionA_of_equalSecondOrder_allRanks
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond ambient conditions hsecondFourth
    have hnotB := a.not_lemma814ExceptionB_of_equalSecondOrder
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond ambient conditions hsecondFourth
    have hnotC := a.not_lemma814ExceptionC_of_equalSecondOrder
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond ambient conditions
    have hnotExceptional :
        ¬a.Beli2019Lemma814Exceptional c.firstUnarySegment := by
      rintro (A | B | C)
      · exact hnotA A
      · exact hnotB B
      · exact hnotC C
    exact (a.beli2019Lemma814Explicit
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c.firstUnarySegment horder unaryConditions).mpr hnotExceptional

/-- The noncircular arithmetic core of Beli (2019), Lemma 9.1.

In the paper the notation `N ≤ M` means an ambient quadratic-space
representation together with the four conditions of Theorem 2.1; it does
*not* mean `Lattice.Represents`.  The unary `Lemma813Conditions` input is the
consequence `[b₁] ≤ M` obtained there from transitivity of this relation.
Keeping it explicit prevents Lemma 9.1 from assuming the desired lattice
representation theorem. -/
theorem beli2019Lemma91
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c hRank)
    (unaryConditions : a.Lemma813Conditions c.firstUnarySegment)
    (hcase : a.Lemma91Alternative c) :
    Nonempty
      (a.Beli2019PrescribedFirstValueTransform c.firstUnarySegment) := by
  letI : Beli2006AlphaLaws.{u, v} K := targetLaws
  have horder : a.order (0 : Fin (N + 3)) =
      c.firstUnarySegment.order (0 : Fin 1) :=
    hfirst.trans c.firstUnarySegment_order_zero.symm
  unfold Lemma91Alternative at hcase
  rcases hcase with hfirstThird | hsecond | hgap | hsecondFourth | hdefect
  · exact a.beli2019Lemma91_of_firstThird_lt_or_secondFourth_eq
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c.firstUnarySegment horder unaryConditions (Or.inl hfirstThird)
  · exact a.beli2019Lemma91_of_equalSecondOrder
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c hRank hfirst hsecond ambient conditions unaryConditions
  · letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.beli2019Lemma91_of_firstGap_eq_twoE
      c.firstUnarySegment horder unaryConditions hgap
  · rcases hsecondFourth with ⟨hfour, hsecondFourth⟩
    exact a.beli2019Lemma91_of_firstThird_lt_or_secondFourth_eq
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c.firstUnarySegment horder unaryConditions
        (Or.inr ⟨hfour, hsecondFourth⟩)
  · exact a.beli2019Lemma91_of_fullSource_firstThirdDefect
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      c horder unaryConditions hdefect.1 hdefect.2

end BONG.GoodBONG

end Bong
