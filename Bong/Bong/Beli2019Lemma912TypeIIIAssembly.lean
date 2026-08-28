/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIConditions
import Bong.Bong.Beli2019Lemma912TypeIIINormalization

/-!
# Beli (2019), Lemma 9.12: complete type-III reduction assembly

The residual type-III parameters first give the normalized source BONG and
the Lemma 9.11 binary replacement.  Its literal integral image is an
index-`p` sublattice.  The four representation conditions proved in the
preceding files turn that sublattice into the concrete reduction consumed by
the Section 9 descent.
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Once the normalization and literal index-`p` image have been chosen,
the type-III estimates produce the exact reduction of the original problem. -/
noncomputable def beli2019Lemma912_typeIIIIndexPReduction
    [PerfectResidueFieldLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hparams : Beli2019Lemma912TypeIIIParameters a c)
    (S : Beli2019Lemma912TypeIIINormalizationData a)
    (D : Beli2019Lemma911Data
      (S.transformed.castLength
        (show N + 5 = 3 + (N + 2) by omega)).typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData
      (S.transformed.castLength
        (show N + 5 = 3 + (N + 2) by omega)) D)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (htransformed :
      RepresentationConditions S.transformed c (Nat.le_refl (N + 4))) :
    let problem := Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient hsource
    Beli2019RepresentationProblem.IndexPReduction problem := by
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let source := S.transformed.castLength hambient
  let target := I.bong.castLength hlength
  have hsourceBack : source.castLength hlength = S.transformed := by
    exact castLength_castLength S.transformed hambient hlength
  have hsourceNorm :
      RepresentationConditions (source.castLength hlength) c le_rfl := by
    rw [hsourceBack]
    exact htransformed
  have hsecondOriginal : c.order (1 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) + 1 :=
    beli2019Lemma912_sourceSecond_eq_add_one_of_typeIII
      (alphaV := sourceAlpha) (alphaW := comparisonAlpha)
        (parityW := comparisonParity) a c profile hfirst hparams
  have hfirstTransformed : S.transformed.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)) :=
    (S.sameOrders (0 : Fin (N + 5))).symm.trans hfirst
  have hsecondTransformed : c.order (1 : Fin (N + 5)) =
      S.transformed.order (1 : Fin (N + 5)) + 1 := by
    calc
      c.order (1 : Fin (N + 5)) =
          a.order (1 : Fin (N + 5)) + 1 := hsecondOriginal
      _ = S.transformed.order (1 : Fin (N + 5)) + 1 :=
        congrArg (fun z : Int => z + 1)
          (S.sameOrders (1 : Fin (N + 5)))
  have houterTransformed :
      S.transformed.order (0 : Fin (N + 5)) =
        S.transformed.order (2 : Fin (N + 5)) := by
    calc
      S.transformed.order (0 : Fin (N + 5)) =
          a.order (0 : Fin (N + 5)) :=
        (S.sameOrders (0 : Fin (N + 5))).symm
      _ = a.order (2 : Fin (N + 5)) := profile.firstThird_eq
      _ = S.transformed.order (2 : Fin (N + 5)) :=
        S.sameOrders (2 : Fin (N + 5))
  have hsecondAlphaTransformed : S.transformed.alphaValue
      (1 : Fin (N + 4)) = 1 := by
    calc
      S.transformed.alphaValue (1 : Fin (N + 4)) =
          a.alphaValue (1 : Fin (N + 4)) :=
        (S.sameAlphas (1 : Fin (N + 4))).symm
      _ = 1 := hparams.2.2
  have hfirstAlphaTransformed : S.transformed.alphaValue
      (0 : Fin (N + 4)) = c.alphaValue (0 : Fin (N + 4)) := by
    calc
      S.transformed.alphaValue (0 : Fin (N + 4)) =
          a.alphaValue (0 : Fin (N + 4)) :=
        (S.sameAlphas (0 : Fin (N + 4))).symm
      _ = c.alphaValue (0 : Fin (N + 4)) := hparams.2.1
  have hfirstGapEq : S.transformed.orderGap (0 : Fin (N + 4)) =
      a.orderGap (0 : Fin (N + 4)) := by
    unfold orderGap
    change S.transformed.order (1 : Fin (N + 5)) -
        S.transformed.order (0 : Fin (N + 5)) =
      a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5))
    rw [← S.sameOrders (1 : Fin (N + 5)),
      ← S.sameOrders (0 : Fin (N + 5))]
  have hfirstGapEvenTransformed :
      Even (S.transformed.orderGap (0 : Fin (N + 4))) := by
    rw [hfirstGapEq]
    exact profile.firstGap_even
  have hfirstGapLeTransformed :
      S.transformed.orderGap (0 : Fin (N + 4)) ≤
        2 * (ramificationIndex K : Int) - 2 := by
    rw [hfirstGapEq]
    exact profile.firstGap_le_twoE_sub_two
  have hsecondLowerOriginal : a.order (0 : Fin (N + 5)) ≤
      a.order (1 : Fin (N + 5)) :=
    beli2019Lemma912_secondOrder_ge_firstOrder_of_typeIII
      (alpha := sourceAlpha) (parity := sourceParity) a c profile hparams
  have hsecondLowerTransformed :
      S.transformed.order (0 : Fin (N + 5)) ≤
        S.transformed.order (1 : Fin (N + 5)) := by
    calc
      S.transformed.order (0 : Fin (N + 5)) =
          a.order (0 : Fin (N + 5)) :=
        (S.sameOrders (0 : Fin (N + 5))).symm
      _ ≤ a.order (1 : Fin (N + 5)) := hsecondLowerOriginal
      _ = S.transformed.order (1 : Fin (N + 5)) :=
        S.sameOrders (1 : Fin (N + 5))
  have hfirstNorm : (source.castLength hlength).order
        (0 : Fin ((N + 2) + 3)) =
      c.order (0 : Fin ((N + 2) + 3)) := by
    rw [hsourceBack]
    exact hfirstTransformed
  have hsecondNorm : c.order (1 : Fin ((N + 2) + 3)) =
      (source.castLength hlength).order (1 : Fin ((N + 2) + 3)) + 1 := by
    rw [hsourceBack]
    exact hsecondTransformed
  have houterNorm : (source.castLength hlength).order
        (0 : Fin ((N + 2) + 3)) =
      (source.castLength hlength).order (2 : Fin ((N + 2) + 3)) := by
    rw [hsourceBack]
    exact houterTransformed
  have hsecondAlphaNorm : (source.castLength hlength).alphaValue
      (1 : Fin ((N + 2) + 2)) = 1 := by
    rw [hsourceBack]
    exact hsecondAlphaTransformed
  have hfirstAlphaNorm : (source.castLength hlength).alphaValue
      (0 : Fin ((N + 2) + 2)) =
        c.alphaValue (0 : Fin ((N + 2) + 2)) := by
    rw [hsourceBack]
    exact hfirstAlphaTransformed
  have hfirstGapEvenNorm : Even
      ((source.castLength hlength).orderGap
        (0 : Fin ((N + 2) + 2))) := by
    rw [hsourceBack]
    exact hfirstGapEvenTransformed
  have hfirstGapLeNorm : (source.castLength hlength).orderGap
        (0 : Fin ((N + 2) + 2)) ≤
      2 * (ramificationIndex K : Int) - 2 := by
    rw [hsourceBack]
    exact hfirstGapLeTransformed
  have hsecondLowerNorm : (source.castLength hlength).order
        (0 : Fin ((N + 2) + 3)) ≤
      (source.castLength hlength).order (1 : Fin ((N + 2) + 3)) := by
    rw [hsourceBack]
    exact hsecondLowerTransformed
  have htarget : RepresentationConditions target c le_rfl := by
    exact beli2019Lemma912_typeIII_representationConditions
      (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
      (comparisonAlpha := comparisonAlpha)
      (comparisonParity := comparisonParity)
      source c D I hlength hsourceNorm hfirstNorm hsecondNorm houterNorm
        hsecondAlphaNorm hfirstAlphaNorm hfirstGapEvenNorm
          hfirstGapLeNorm hsecondLowerNorm
  let problem := Beli2019RepresentationProblem.ofData
    a c (Nat.le_refl (N + 4)) ambient hsource
  change Beli2019RepresentationProblem.IndexPReduction problem
  exact {
    index_eq := rfl
    lattice := I.lattice
    inclusion := I.inclusion
    targetBONG := target
    conditions := htarget }

set_option maxHeartbeats 8000000 in
-- Normalization, realization, and all four condition packages elaborate together.
/-- The type-III parameter branch of Lemma 9.12 constructs a literal
index-`p` reduction satisfying all four representation conditions. -/
theorem exists_beli2019Lemma912_typeIIIIndexPReduction
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [comparisonAlpha : Beli2006AlphaLaws.{u, w} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [comparisonParity : Beli2009AlphaParityLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hparams : Beli2019Lemma912TypeIIIParameters a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4))) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := sourceAlpha
  letI : Beli2009AlphaParityLaws.{u, v} K := sourceParity
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases exists_beli2019Lemma912TypeIIINormalizationData
    (K := K) (V := V) (W := W) a c profile hparams.2.2 with ⟨S⟩
  have htransformed :
      RepresentationConditions S.transformed c (Nat.le_refl (N + 4)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      S.transformed c c (Nat.le_refl (N + 4))).mp hsource
  rcases exists_beli2019Lemma912TypeIIIRealization_of_normalization
    (alphaV := sourceAlpha) (alphaW := comparisonAlpha)
    (parityV := sourceParity) (parityW := comparisonParity)
      a c profile hfirst hparams S with ⟨D, ⟨C⟩⟩
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let source := S.transformed.castLength hambient
  rcases exists_beli2019Lemma912TypeIIIIndexPData
    (structural := structural) source D C with ⟨I⟩
  exact ⟨beli2019Lemma912_typeIIIIndexPReduction
    (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
    (comparisonAlpha := comparisonAlpha)
    (comparisonParity := comparisonParity)
    (structural := structural) (representationLaws := representationLaws)
      a c profile hparams S D I hfirst ambient hsource htransformed⟩

end BONG.GoodBONG

end Bong
