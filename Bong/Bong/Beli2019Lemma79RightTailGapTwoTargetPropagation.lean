/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoSourcePropagation
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 7.9(ii), case 8: target-prefix propagation

Right-endpoint monotonicity bounds every later target alpha from below by
the central coefficient.  Remark 6.16 expresses the target self-prefix as
the minimum of that alpha and the source self-prefix, whose exact value was
computed in the preceding file.  This proves lines 5898--5900.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every even target prefix from `u + 1` through the strict tail has the
same defect as the corresponding source prefix and the central mixed
defect.  `pairs = 0` is the first prefix after the gap-two endpoint. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect
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
    (hend : D.profile.last + 1 + 2 * pairs ≤ tailLast.val)
    (hbound : D.profile.last + 2 + 2 * pairs < n + 2) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((D.profile.last + 2 + 2 * pairs) / 2)) 0
        (D.profile.last + 2 + 2 * pairs) =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  let length : Nat := D.profile.last + 2 + 2 * pairs
  let current : Fin (n + 1) := ⟨length - 1, by
    simp only [length]
    omega⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨length, by simp only [length]; omega,
      by simpa only [length] using hbound,
      by simp only [length]; omega⟩
  let central : WithTop Rat :=
    ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first : Rat) : WithTop Rat)
  have hsource :
      a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length =
        central := by
    cases pairs with
    | zero =>
        simpa only [length, central, first, Nat.mul_zero, add_zero] using
          beli2019Lemma79_typeI_caseEight_gapTwo_firstSourcePrefixDefect_complete
            a b D hfirst hgapTwo hlast horder hdefect H
              hfirstTail hstrictTail
    | succ pairs =>
        have hend' : D.profile.last + 2 + 2 * pairs ≤ tailLast.val := by
          omega
        simpa only [length, central, first, Nat.succ_eq_add_one] using
          beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect_succ
            a b D hfirst hgapTwo hlast horder hdefect H
              hfirstTail hstrictTail pairs hend'
  have hfirstCurrent : first ≤ current := by
    change first.val ≤ current.val
    simp only [first, current, length]
    omega
  have hcurrentTail : current ≤ tailLast := by
    change current.val ≤ tailLast.val
    simp only [current, length]
    omega
  have hvalue := H.value_eq current hfirstCurrent hcurrentTail
  have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    D.profile.last length (by simp only [length]; omega)
      (by simpa only [length] using hbound) (by
        refine ⟨pairs + 1, ?_⟩
        simp only [length]
        omega)
  have horderMonotone : b.order first.castSucc ≤ b.order current.succ := by
    rw [b.orderSequence_entryOrZero_eq_order
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)),
      b.orderSequence_entryOrZero_eq_order
        (⟨length, by simpa only [length] using hbound⟩ : Fin (n + 2))]
      at horderEntry
    have hfirstIndex :
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)) = first.castSucc := by
      apply Fin.ext
      rfl
    have hcurrentIndex :
        (⟨length, by simpa only [length] using hbound⟩ : Fin (n + 2)) =
          current.succ := by
      apply Fin.ext
      simp only [current, Fin.val_succ]
      simp only [length]
      omega
    simpa only [hfirstIndex, hcurrentIndex] using horderEntry
  have hbetaQ :
      ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first ≤ b.alphaValue current := by
    have horderQ : (b.order first.castSucc : Rat) ≤
        (b.order current.succ : Rat) := by
      exact_mod_cast horderMonotone
    push_cast at hvalue ⊢
    linarith
  have hbeta : central ≤ (b.alphaValue current : WithTop Rat) := by
    exact WithTop.coe_le_coe.mpr (by simpa only [central] using hbetaQ)
  have hsuffix : ∀ k, idx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · simp only [idx, length] at hk
      omega
    · exact hkn
  have hAlphaRaw := a.beli2019Lemma63_sameRank_right_value
    b hdefect idx hsuffix
  have hAlpha : a.representationAlphaValue b idx =
      b.alphaValue current := by
    simpa only [idx, current, length] using hAlphaRaw
  have hformula := beli2019Remark616_rightPrefix
    a b hdefect idx hAlpha ((-1) ^ (length / 2))
  calc
    b.truncatedPrefixDefect b
        ((-1) ^ ((D.profile.last + 2 + 2 * pairs) / 2)) 0
        (D.profile.last + 2 + 2 * pairs) =
      min (a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length)
        (b.alphaValue current : WithTop Rat) := by
          simpa only [idx, length, current] using hformula
    _ = a.truncatedPrefixDefect a ((-1) ^ (length / 2)) 0 length := by
      rw [min_eq_left]
      rw [hsource]
      exact hbeta
    _ = _ := by simpa only [hsource, central, first]

end BONG.GoodBONG

end Bong
