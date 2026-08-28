/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralSeedsComplete
import Bong.Bong.Beli2019Lemma79TypeIBetaProfile

/-!
# Beli (2019), Lemma 7.9(ii): the complete type-I target branch

Lemma 6.9(ii) supplies the exact mixed alpha needed by Remark 6.16, while
the canonical type-I profile supplies the target-alpha estimate.  Thus only
the source-defect comparison branch of case 4 remains as an input.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 4, after discharging the complete target-alpha
branch.  The remaining implication is precisely the paper's comparison
`C_i ≥ B_i` when Remark 6.16 selects the source mixed defect. -/
theorem lemma79_ii_typeI_of_source_branch
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
    (hright : i.val - 1 < C.rightSwitch)
    (hsource : a.truncatedPrefixDefect c 1 i.val i.val ≤
        (b.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : WithTop ℚ) →
      (b.representationAlphaValue c i : WithTop ℚ) ≤
        (a.representationAlphaValue c i : WithTop ℚ)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hAlpha := beli2019Lemma69_ii_typeI_targetValue_from_conditions
    a b D C hfirst hrightLast horderAB hdefectAB i hodd hleft hright
  apply lemma79_ii_of_rightMixedPrefix_branches
    a b c hdefectAB hdefectAC i hAlpha hsource
  intro _
  exact lemma79_typeI_beta_bound_from_profile
    a b c D C hfirst horderBC hnorm i hodd hleft hright

end BONG.GoodBONG

end Bong
