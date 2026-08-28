/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIDefect
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 9.12: comparison alpha after the type-III step

From the fourth boundary onward the type-III image and the source have the
same orders.  The mixed-prefix formula proved from Remark 6.16 says that
each defect candidate for the image is obtained by taking a minimum with
the image alpha.  Hence the half-gap is unchanged and both defect
candidates can only decrease.  This proves the inequality `B_i <= C_i`
used in the type-III part of Lemma 9.12.
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

/-- Every mixed prefix defect of the type-III image is bounded by the
corresponding source defect at a boundary `i >= 3`. -/
theorem beli2019Lemma912_typeIII_mixedPrefixDefect_le_source
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val)
    (epsilon : Kˣ) (j : Nat) :
    (I.bong.castLength hlength).truncatedPrefixDefect c epsilon i.val j <=
      (a.castLength hlength).truncatedPrefixDefect c epsilon i.val j := by
  rw [beli2019Lemma912_typeIII_mixedPrefixDefect
    a c D I hlength i hi epsilon j]
  exact min_le_left _ _

/-- The mixed-prefix comparison including the complete-prefix endpoint.
For an internal prefix this is Remark 6.16; for the full prefix it is
invariance of the complete value product under change of good BONG. -/
theorem beli2019Lemma912_typeIII_mixedPrefixDefect_le_source_at
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (p : Nat) (hpThree : 3 <= p) (hpRank : p <= T + 3)
    (epsilon : Kˣ) (j : Nat) :
    (I.bong.castLength hlength).truncatedPrefixDefect c epsilon p j <=
      (a.castLength hlength).truncatedPrefixDefect c epsilon p j := by
  by_cases hpFull : p = T + 3
  · subst p
    exact le_of_eq
      ((a.castLength hlength).truncatedPrefixDefect_fullLeft_invariant
        (I.bong.castLength hlength) c epsilon j)
  · let i : RepresentationIndex (T + 3) (T + 3) := {
      val := p
      pos := by omega
      lt_large := by omega
      le_small := hpRank }
    exact beli2019Lemma912_typeIII_mixedPrefixDefect_le_source
      a c D I hlength i hpThree epsilon j

set_option maxHeartbeats 4000000 in
-- Normalizing all three nested candidates exceeds the default heartbeat limit.
/-- Candidate normalization unfolds several nested finite-prefix definitions.
The comparison invariant after the type-III replacement is bounded by
the corresponding invariant before replacement at every boundary `i >= 3`.
This is the inequality `B_i <= C_i` in the proof of Lemma 9.12. -/
theorem beli2019Lemma912_typeIII_representationAlpha_le_source
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val) :
    (I.bong.castLength hlength).representationAlpha c i <=
      (a.castLength hlength).representationAlpha c i := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  have hcurrent :
      target.order (⟨i.val, i.lt_large⟩ : Fin (T + 3)) =
        source.order (⟨i.val, i.lt_large⟩ : Fin (T + 3)) := by
    exact beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
      a D I hlength ⟨i.val, i.lt_large⟩ hi
  have hhalf : target.representationHalfGap c i =
      source.representationHalfGap c i := by
    unfold representationHalfGap
    rw [hcurrent]
  have hprimary : target.representationPrimaryDefect c i <=
      source.representationPrimaryDefect c i := by
    unfold representationPrimaryDefect
    rw [hcurrent]
    have hprefix :
        target.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) <=
          source.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) :=
      beli2019Lemma912_typeIII_mixedPrefixDefect_le_source_at
        a c D I hlength (i.val + 1) (by omega)
          (Nat.succ_le_of_lt i.lt_large) (-1) (i.val - 1)
    exact add_le_add_right hprefix _
  rw [target.representationAlpha_eq_min_halfGap_prime c i,
    source.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min (le_of_eq hhalf)
  by_cases hinterior : 1 < i.val ∧ i.val + 1 < T + 3
  · have hnext :
        target.order (⟨i.val + 1, hinterior.2⟩ : Fin (T + 3)) =
          source.order (⟨i.val + 1, hinterior.2⟩ : Fin (T + 3)) := by
      have hnextThree :
          3 <= (⟨i.val + 1, hinterior.2⟩ : Fin (T + 3)).val := by
        change 3 <= i.val + 1
        omega
      exact
        beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
          a D I hlength ⟨i.val + 1, hinterior.2⟩ hnextThree
    have hsecondary : target.representationSecondaryDefect c i hinterior <=
        source.representationSecondaryDefect c i hinterior := by
      unfold representationSecondaryDefect
      rw [hcurrent, hnext]
      have hprefix :
          target.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) <=
            source.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
        beli2019Lemma912_typeIII_mixedPrefixDefect_le_source_at
          a c D I hlength (i.val + 2) (by omega) (by omega)
            1 (i.val - 2)
      exact add_le_add_right hprefix _
    rw [target.representationAlphaPrime_eq_min_primary_secondary
        c i hinterior,
      source.representationAlphaPrime_eq_min_primary_secondary
        c i hinterior]
    exact min_le_min hprimary hsecondary
  · rw [target.representationAlphaPrime_eq_primary_of_not_interior
        c i hinterior,
      source.representationAlphaPrime_eq_primary_of_not_interior
        c i hinterior]
    exact hprimary

/-- Rational-valued form of
`beli2019Lemma912_typeIII_representationAlpha_le_source`. -/
theorem beli2019Lemma912_typeIII_representationAlphaValue_le_source
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3)
    (i : RepresentationIndex (T + 3) (T + 3)) (hi : 3 <= i.val) :
    (I.bong.castLength hlength).representationAlphaValue c i <=
      (a.castLength hlength).representationAlphaValue c i := by
  have h := beli2019Lemma912_typeIII_representationAlpha_le_source
    a c D I hlength i hi
  have hcoe :
      ((I.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) <=
        ((a.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) := by
    simpa only [coe_representationAlphaValue] using h
  exact WithTop.coe_le_coe.mp hcoe

end BONG.GoodBONG

end Bong
