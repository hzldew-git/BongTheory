/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.Beli2019Lemma79RightTailGapTwoCentralDefect
import Bong.Bong.Beli2019Lemma79RightTailGapTwoPrefixStrict

/-!
# Beli (2019), Lemma 7.9(ii), case 8: first source prefix

The central mixed defect is strictly smaller than the alternating target
prefix.  Sharp capped-defect multiplication therefore identifies the first
alternating source prefix after the gap-two boundary with the central
coefficient.  This is the domination step in lines 5891--5892.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At a positive gap-two endpoint, the first alternating source prefix
after the endpoint has the paper's central coefficient as its defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hlastPos : 0 < D.profile.last)
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
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let eta : Kˣ := (-1) ^ (D.profile.last / 2)
  have hmixed := beli2019Lemma79_typeI_caseEight_gapTwo_centralDefect_eq
    a b D hfirst hdefect hgapTwo hlast H hfirstTail
  have htarget :=
    beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefix_gt_central
      a b D hfirst hgapTwo hlast hlastPos horder hdefect H
        hfirstTail hstrictTail
  have htargetTransfer :
      b.truncatedPrefixDefect a eta D.profile.last 0 =
        b.truncatedPrefixDefect b eta D.profile.last 0 :=
    b.truncatedPrefixDefect_zero_right_eq_self a eta D.profile.last
  have htargetComm :
      b.truncatedPrefixDefect b eta D.profile.last 0 =
        b.truncatedPrefixDefect b eta 0 D.profile.last :=
    b.truncatedPrefixDefect_comm b eta D.profile.last 0
  have hseparation :
      a.truncatedPrefixDefect b (-1)
          (D.profile.last + 2) D.profile.last <
        b.truncatedPrefixDefect a eta D.profile.last 0 := by
    rw [htargetTransfer, htargetComm, hmixed]
    simpa only [eta] using htarget
  have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b a (-1) eta (D.profile.last + 2) D.profile.last 0 hseparation
  have hsign : (-1 : Kˣ) * eta =
      (-1) ^ ((D.profile.last + 2) / 2) := by
    rcases I.last_even with ⟨d, hd⟩
    have hhalf : D.profile.last / 2 = d := by omega
    have hhalfNext : (D.profile.last + 2) / 2 = d + 1 := by omega
    dsimp only [eta]
    rw [hhalf, hhalfNext, pow_succ]
    ac_rfl
  calc
    a.truncatedPrefixDefect a ((-1) ^ ((D.profile.last + 2) / 2)) 0
        (D.profile.last + 2) =
      a.truncatedPrefixDefect a ((-1) ^ ((D.profile.last + 2) / 2))
        (D.profile.last + 2) 0 :=
      a.truncatedPrefixDefect_comm a
        ((-1) ^ ((D.profile.last + 2) / 2)) 0 (D.profile.last + 2)
    _ = a.truncatedPrefixDefect a ((-1) * eta)
        (D.profile.last + 2) 0 := by rw [hsign]
    _ = a.truncatedPrefixDefect b (-1)
        (D.profile.last + 2) D.profile.last := hsharp
    _ = _ := hmixed

end BONG.GoodBONG

end Bong
