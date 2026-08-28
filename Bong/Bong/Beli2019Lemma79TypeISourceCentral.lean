/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeISourceInterior
import Bong.Bong.Beli2019Lemma79TypeISourceSecondaryBoundary

/-!
# Beli (2019), Lemma 7.9(ii): the complete central type-I source branch

The right-boundary form of the secondary comparison removes the final
strict-interior hypothesis.  All three candidates defining the comparison
alpha are therefore no larger than the corresponding source candidates at
every central odd boundary.
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
one at every odd coordinate in the canonical central type-I interval. -/
theorem lemma79_typeI_alpha_le_sourceAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hcurrentRight : i.val < C.rightSwitch := by
    rcases hodd with ⟨d, hd⟩
    rcases C.right_even with ⟨e, he⟩
    omega
  have hhalf := lemma79_typeI_halfGap_le_sourceHalfGap
    a b c D C hfirst i hodd hleft hright
  have hprimary := lemma79_typeI_primary_le_sourcePrimary
    a b c D C hfirst hrightLast horder hdefect i hodd hleft hright
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeI_secondary_le_sourceSecondary_of_lt_right
        a b c D C hfirst hrightLast horder hdefect i hi hodd hleft
          hcurrentRight)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

/-- Lemma 7.9(ii), case 4, at every odd coordinate of the canonical
central type-I interval. -/
theorem beli2019Lemma79_ii_typeI_centralOdd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply lemma79_ii_typeI_of_source_branch
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      horderBC hnorm i hodd hleft hright
  intro _
  exact lemma79_typeI_alpha_le_sourceAlpha
    a b c D C hfirst hrightLast horderAB hdefectAB i hodd hleft hright

end BONG.GoodBONG

end Bong
