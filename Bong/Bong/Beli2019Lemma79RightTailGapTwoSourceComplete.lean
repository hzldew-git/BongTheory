/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoSourcePropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete source propagation

This packages the initial source-prefix identity and its positive-length
propagation into one theorem indexed by the number of appended pairs.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every admissible even source prefix beginning at `u + 1` has the
central gap-two defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (pairs : Nat)
    (hend : D.profile.last + 2 * pairs ≤ tailLast.val) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2 + 2 * pairs) / 2)) 0
        (D.profile.last + 2 + 2 * pairs) =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  cases pairs with
  | zero =>
      simpa only [Nat.mul_zero, add_zero] using
        beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect_complete
          a b D hfirst hgapTwo hlast horder hdefect H
            hfirstTail hstrictTail
  | succ pairs =>
      have hend' : D.profile.last + 2 + 2 * pairs ≤ tailLast.val := by
        omega
      simpa only [Nat.succ_eq_add_one] using
        beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_succ
          a b D hfirst hgapTwo hlast horder hdefect H
            hfirstTail hstrictTail pairs hend'

end BONG.GoodBONG

end Bong
