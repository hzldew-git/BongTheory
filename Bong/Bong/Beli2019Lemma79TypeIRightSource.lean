/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIRightBetaProfile
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary
import Bong.Bong.Beli2019Lemma79MixedAssembly

/-!
# Beli (2019), Lemma 7.9(ii): the complete type-I right tail

The half-gap, primary, and secondary comparisons assemble the source branch
of Remark 6.16. The right-profile beta estimate supplies its other branch,
proving condition 2.1(ii) on every odd boundary of the right tail.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The comparison representation invariant is no larger than the source
one at every odd coordinate on the canonical type-I right tail. -/
theorem lemma79_typeI_right_alpha_le_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hhalf := lemma79_typeI_right_halfGap_le_sourceHalfGap
    a b c D C hfirst i hright hlast hodd
  have hprimary := lemma79_typeI_right_primary_le_sourcePrimary
    a b c D C hfirst hrightLast hdefect i hright hlast hodd
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeI_right_secondary_le_sourceSecondary
        a b c D C hfirst hrightLast hdefect i hi hright hlast hodd)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

/-- Lemma 7.9(ii), case 4, at every odd coordinate of the canonical type-I
right tail. -/
theorem beli2019Lemma79_ii_typeI_rightOdd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hAlpha := beli2019Lemma69_ii_typeI_targetRightValue
    a b D C hfirst hrightLast hdefectAB i hright hlast hodd
  apply lemma79_ii_of_rightMixedPrefix_branches
    a b c hdefectAB hdefectAC i hAlpha
  · intro _
    exact lemma79_typeI_right_alpha_le_sourceAlpha
      a b c D C hfirst hrightLast hdefectAB i hright hlast hodd
  · intro _
    exact lemma79_typeI_beta_bound_from_rightProfile
      a b c D C hfirst horderBC hnorm i hright hlast hodd

end BONG.GoodBONG

end Bong
