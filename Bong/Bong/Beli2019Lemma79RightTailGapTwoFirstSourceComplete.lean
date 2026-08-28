/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoFirstSource

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete first source prefix

This adds the paper's `u = 1` branch.  There the target prefix before the
gap-two endpoint is empty, so its self-defect is infinite and sharp
domination applies immediately.  Together with the positive-endpoint theorem
this removes the auxiliary assumption `0 < u`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The first alternating source-prefix identity at every gap-two endpoint,
including the empty target-prefix case. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect_complete
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
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast) :
    a.truncatedPrefixDefect a
        ((-1) ^ ((D.profile.last + 2) / 2)) 0
        (D.profile.last + 2) =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  by_cases hlastZero : D.profile.last = 0
  · have hmixed :=
      beli2019Lemma79_typeI_caseEight_gapTwo_centralDefect_eq
        a b D hfirst hdefect hgapTwo hlast H hfirstTail
    have htargetTop :
        b.truncatedPrefixDefect a 1 0 0 = ⊤ := by
      rw [b.truncatedPrefixDefect_zero_right_eq_self a 1 0]
      unfold truncatedPrefixDefect
      rw [b.prefixAlphaCap_zero]
      simp only [inf_top_eq]
      rw [show (1 : Kˣ) * b.prefixProduct 0 * b.prefixProduct 0 = 1 by
        simp [GoodBONG.prefixProduct]]
      rw [defectOrder_eq_top_of_isSquare]
      exact IsSquare.one
    have hseparation :
        a.truncatedPrefixDefect b (-1) 2 0 <
          b.truncatedPrefixDefect a 1 0 0 := by
      rw [htargetTop]
      rw [show a.truncatedPrefixDefect b (-1) 2 0 =
          ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
              b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) :
                Rat) + b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) :
              WithTop Rat) by
        simpa only [hlastZero, Nat.zero_add] using hmixed]
      exact WithTop.coe_lt_top _
    have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
      b a (-1) 1 2 0 0 hseparation
    calc
      a.truncatedPrefixDefect a
          ((-1) ^ ((D.profile.last + 2) / 2)) 0
          (D.profile.last + 2) =
        a.truncatedPrefixDefect a (-1) 0 2 := by
          norm_num [hlastZero]
      _ = a.truncatedPrefixDefect a (-1) 2 0 :=
        a.truncatedPrefixDefect_comm a (-1) 0 2
      _ = a.truncatedPrefixDefect b (-1) 2 0 := by
        simpa only [mul_one] using hsharp
      _ = _ := by
        simpa only [hlastZero, Nat.zero_add] using hmixed
  · exact
      beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect
        a b D hfirst hgapTwo hlast (Nat.pos_of_ne_zero hlastZero)
          horder hdefect H hfirstTail hstrictTail

end BONG.GoodBONG

end Bong
