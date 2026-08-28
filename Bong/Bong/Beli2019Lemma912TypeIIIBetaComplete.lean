/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIBetaOddGap

/-!
# Beli (2019), Lemma 9.12: all high type-III alpha bounds

The third target gap is either at least `2e`, or it is smaller and has even
or odd parity.  The three preceding files prove exactly these exhaustive
branches, so condition 2.1(ii) at every boundary `i ≥ 3` follows.
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

variable [BeliCorollary44Laws.{u, v} K]

/-- The complete `B_i ≤ beta_i` estimate at every type-III boundary
`i ≥ 3`. -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_three_le
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (comparisonAlpha : Beli2006AlphaLaws.{u, w} K)
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (hsource : (a.castLength hlength).RepresentationDefectCondition c)
    (horder : (I.bong.castLength hlength).RepresentationOrderCondition c le_rfl)
    (hfirst : (a.castLength hlength).order (0 : Fin (T + 3)) =
      c.order (0 : Fin (T + 3)))
    (hsecond : c.order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1)
    (hfirstThird : (a.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)))
    (hfirstGapEven : Even
      ((a.castLength hlength).orderGap (0 : Fin (T + 2))))
    (hsourceSecondLower :
      (a.castLength hlength).order (0 : Fin (T + 3)) ≤
        (a.castLength hlength).order (1 : Fin (T + 3)))
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 ≤ i.val) :
    (I.bong.castLength hlength).representationAlphaValue c i ≤
      (I.bong.castLength hlength).alphaValue
        ⟨i.val - 1, by have hlt := i.lt_large; omega⟩ := by
  let first : Fin (T + 2) := ⟨2, by
    have hlt := i.lt_large
    omega⟩
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      (I.bong.castLength hlength).orderGap first
  · exact
      beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_ge
        (sourceAlpha := sourceAlpha) comparisonAlpha a c D I hlength
          hsource horder i hi (by simpa only [first] using hlarge)
  · have hsmall : (I.bong.castLength hlength).orderGap first <
        2 * (ramificationIndex K : Int) := lt_of_not_ge hlarge
    rcases Int.even_or_odd
        ((I.bong.castLength hlength).orderGap first) with heven | hodd
    · exact
        beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_lt_even
          (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
            a c D I hlength hsource i hi
              (by simpa only [first] using hsmall)
              (by simpa only [first] using heven)
    · exact
        beli2019Lemma912_typeIII_representationAlphaValue_le_targetAlpha_of_thirdGap_lt_odd
          (sourceAlpha := sourceAlpha) (sourceParity := sourceParity)
            comparisonAlpha a c D I hlength hsource hfirst hsecond
              hfirstThird hfirstGapEven hsourceSecondLower i hi
                (by simpa only [first] using hsmall)
                (by simpa only [first] using hodd)

end BONG.GoodBONG

end Bong
