/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912LowProfile
import Bong.Bong.Beli2019Lemma912TypeIIIAllRankAssembly

/-!
# Beli (2019), Lemma 9.12: low-rank parameter branches

This module records the type-III parameter package and derives its two order
facts directly from the all-rank residual profile.  It then invokes the
all-rank type-III assembly, closing that branch in ranks three and four.
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
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

/-- The residual type-III parameter package at rank `T + 3`. -/
def Beli2019Lemma912TypeIIIParametersAllRanks
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3)) : Prop :=
  a.truncatedPrefixDefect c (-1) 3 1 =
      (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ∧
    a.alphaValue (0 : Fin (T + 2)) =
      c.alphaValue (0 : Fin (T + 2)) ∧
    a.alphaValue (1 : Fin (T + 2)) = 1

/-- Equality of first alphas in the type-III branch forces the source second
order to be exactly one above the target second order. -/
theorem beli2019Lemma912_sourceSecond_eq_add_one_of_typeIII_allRanks
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (profile : Beli2019Lemma912InitialProfileAllRanks a c)
    (hfirst : a.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hparams : Beli2019Lemma912TypeIIIParametersAllRanks a c) :
    c.order (1 : Fin (T + 3)) = a.order (1 : Fin (T + 3)) + 1 := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin (T + 1)) profile.firstThird_eq
  have hformula := hremark.previousAlpha_eq
  change a.alphaValue (0 : Fin (T + 2)) =
    ((a.order (1 : Fin (T + 3)) - a.order (2 : Fin (T + 3)) : Int) : ℚ) +
      a.alphaValue (1 : Fin (T + 2)) at hformula
  rw [← profile.firstThird_eq, hparams.2.2] at hformula
  have hsourceAlpha : c.alphaValue (0 : Fin (T + 2)) =
      a.alphaValue (0 : Fin (T + 2)) := hparams.2.1.symm
  have hcAlphaLe : c.alphaValue (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : ℚ) := by
    rw [hsourceAlpha, hformula]
    have hgap := profile.firstGap_le_twoE_sub_two
    unfold orderGap at hgap
    change a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) ≤
      2 * (ramificationIndex K : Int) - 2 at hgap
    push_cast
    exact_mod_cast (show
      a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) + 1 ≤
        2 * (ramificationIndex K : Int) by omega)
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  letI : Beli2009AlphaParityLaws.{u, w} K := parityW
  have hcGapLe : c.orderGap (0 : Fin (T + 2)) ≤
      2 * (ramificationIndex K : Int) :=
    (c.alphaValue_le_twoE_iff_orderGap_le_twoE
      (0 : Fin (T + 2))).mp hcAlphaLe
  have hcGapAlpha := (c.alpha_p3 (0 : Fin (T + 2)) hcGapLe).1
  have hgapUpper : c.orderGap (0 : Fin (T + 2)) ≤
      a.orderGap (0 : Fin (T + 2)) + 1 := by
    rw [hsourceAlpha, hformula] at hcGapAlpha
    unfold orderGap at hcGapAlpha ⊢
    exact_mod_cast hcGapAlpha
  unfold orderGap at hgapUpper
  change c.order (1 : Fin (T + 3)) - c.order (0 : Fin (T + 3)) ≤
    (a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3))) + 1 at hgapUpper
  rw [← hfirst] at hgapUpper
  have hlower := profile.second_lt_sourceSecond
  omega

/-- The target second order is not below the first in the type-III branch. -/
theorem beli2019Lemma912_secondOrder_ge_firstOrder_of_typeIII_allRanks
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [parity : Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (profile : Beli2019Lemma912InitialProfileAllRanks a c)
    (hparams : Beli2019Lemma912TypeIIIParametersAllRanks a c) :
    a.order (0 : Fin (T + 3)) ≤ a.order (1 : Fin (T + 3)) := by
  have hgapLe := a.orderGap_le_one_of_alphaValue_le_one
    (1 : Fin (T + 2)) (by rw [hparams.2.2])
  unfold orderGap at hgapLe
  change a.order (2 : Fin (T + 3)) - a.order (1 : Fin (T + 3)) ≤ 1 at hgapLe
  rw [← profile.firstThird_eq] at hgapLe
  rcases profile.firstGap_even with ⟨z, hz⟩
  unfold orderGap at hz
  change a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3)) = z + z at hz
  omega

set_option maxHeartbeats 10000000 in
-- The rank-three normalization and all four condition proofs elaborate together.
/-- The type-III residual branch gives a literal index-`p` reduction in every
rank at least three. -/
theorem exists_beli2019Lemma912_typeIIIIndexPReduction_of_profile_allRanks
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
    (a : GoodBONG q L (T + 3)) (c : GoodBONG r M (T + 3))
    (profile : Beli2019Lemma912InitialProfileAllRanks a c)
    (hparams : Beli2019Lemma912TypeIIIParametersAllRanks a c)
    (hfirst : a.order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (T + 2))) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (T + 2)) ambient hsource)) := by
  have hsecond :=
    beli2019Lemma912_sourceSecond_eq_add_one_of_typeIII_allRanks
      (alphaV := sourceAlpha) (alphaW := comparisonAlpha)
      (parityW := comparisonParity) a c profile hfirst hparams
  have hsecondLower :=
    beli2019Lemma912_secondOrder_ge_firstOrder_of_typeIII_allRanks
      (alpha := sourceAlpha) (parity := sourceParity) a c profile hparams
  exact exists_beli2019Lemma912_typeIIIIndexPReduction_allRanks
    (sourceAlpha := sourceAlpha) (comparisonAlpha := comparisonAlpha)
    (sourceParity := sourceParity) (comparisonParity := comparisonParity)
    (classificationV := classificationV) (classificationW := classificationW)
    (structural := structural) (representationLaws := representationLaws)
    a c profile.firstThird_eq profile.firstGap_even
      profile.firstGap_le_twoE_sub_two hparams.2.2 hparams.2.1 hfirst hsecond
      hsecondLower profile.second_lt_fourth
      (fun hT => profile.sourceSecond_eq_add_one_imp_first_lt_fifth hT hsecond)
      ambient hsource

end BONG.GoodBONG

end Bong
