/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoSourceComplete
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 7.9(ii), case 8: target endpoint

When the final paper index is odd, the required even target prefix ends one
boundary beyond the strict beta interval.  The beta identity at the final
interval point, followed by monotonicity of `S_j + beta_j`, still puts the
new alpha cap above the central coefficient.  Remark 6.16 then gives the
same target-prefix defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The even target prefix ending two places after a same-parity strict-tail
endpoint has the central gap-two defect. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_endpoint
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
    (hnext : tailLast.val + 1 < n + 1)
    (hparity : Even (tailLast.val - D.profile.last)) :
    b.truncatedPrefixDefect b
        ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2) =
      ((((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
          b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ : Rat) : WithTop Rat) := by
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  let current : Fin (n + 1) := ⟨tailLast.val + 1, hnext⟩
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨tailLast.val + 2, by omega, by omega, by omega⟩
  let central : WithTop Rat :=
    ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
      b.alphaValue first : Rat) : WithTop Rat)
  rcases hparity with ⟨pairs, hpairs⟩
  have htailEq : tailLast.val = D.profile.last + 2 * pairs := by
    have hle : D.profile.last ≤ tailLast.val := by
      change first.val ≤ tailLast.val at hfirstTail
      simpa only [first] using hfirstTail
    omega
  have hsourceRaw :=
    beli2019Lemma79_typeI_caseEight_gapTwo_sourcePrefixDefect
      a b D hfirst hgapTwo hlast horder hdefect H hfirstTail
        hstrictTail pairs (by omega)
  have hsource :
      a.truncatedPrefixDefect a ((-1) ^ ((tailLast.val + 2) / 2)) 0
          (tailLast.val + 2) = central := by
    have hlength : tailLast.val + 2 =
        D.profile.last + 2 + 2 * pairs := by omega
    rw [hlength]
    simpa only [central, first] using hsourceRaw
  have hlastValue := H.value_eq tailLast hfirstTail le_rfl
  have htailCurrent : tailLast ≤ current := by
    change tailLast.val ≤ current.val
    simp only [current]
    omega
  have hleftEndpoint := b.alphaLeftEndpoint_monotone htailCurrent
  have hsameIndex : current.castSucc = tailLast.succ := by
    apply Fin.ext
    rfl
  unfold alphaLeftEndpoint at hleftEndpoint
  rw [hsameIndex] at hleftEndpoint
  have horderEntry := b.orderSequence.entryOrZero_le_of_evenGap
    D.profile.last tailLast.val (by
      change first.val ≤ tailLast.val at hfirstTail
      simpa only [first] using hfirstTail) (by omega) (by
        exact ⟨pairs, hpairs⟩)
  have horderMonotone : b.order first.castSucc ≤
      b.order tailLast.castSucc := by
    rw [b.orderSequence_entryOrZero_eq_order
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)),
      b.orderSequence_entryOrZero_eq_order
        (⟨tailLast.val, by omega⟩ : Fin (n + 2))] at horderEntry
    have hfirstIndex :
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)) = first.castSucc := by
      apply Fin.ext
      rfl
    have hlastIndex :
        (⟨tailLast.val, by omega⟩ : Fin (n + 2)) =
          tailLast.castSucc := by
      apply Fin.ext
      rfl
    simpa only [hfirstIndex, hlastIndex] using horderEntry
  have hbetaQ :
      ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first ≤ b.alphaValue current := by
    have horderQ : (b.order first.castSucc : Rat) ≤
        (b.order tailLast.castSucc : Rat) := by
      exact_mod_cast horderMonotone
    push_cast at hlastValue hleftEndpoint ⊢
    linarith
  have hbeta : central ≤ (b.alphaValue current : WithTop Rat) := by
    exact WithTop.coe_le_coe.mpr (by simpa only [central] using hbetaQ)
  have hsuffix : ∀ k, idx.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · simp only [idx] at hk
      have hfirstLe : D.profile.last ≤ tailLast.val := by
        change first.val ≤ tailLast.val at hfirstTail
        simpa only [first] using hfirstTail
      omega
    · exact hkn
  have hAlphaRaw := a.beli2019Lemma63_sameRank_right_value
    b hdefect idx hsuffix
  have hcurrentIndex :
      (⟨idx.val - 1, by
        have hi := idx.lt_large
        have hp := idx.pos
        omega⟩ : Fin (n + 1)) = current := by
    apply Fin.ext
    simp only [idx, current]
    omega
  have hAlpha : a.representationAlphaValue b idx =
      b.alphaValue current := by
    simpa only [hcurrentIndex] using hAlphaRaw
  have hformula := beli2019Remark616_rightPrefix
    a b hdefect idx hAlpha ((-1) ^ ((tailLast.val + 2) / 2))
  rw [hcurrentIndex] at hformula
  calc
    b.truncatedPrefixDefect b ((-1) ^ ((tailLast.val + 2) / 2)) 0
        (tailLast.val + 2) =
      min (a.truncatedPrefixDefect a
          ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2))
        (b.alphaValue current : WithTop Rat) := by
          simpa only [idx] using hformula
    _ = a.truncatedPrefixDefect a
        ((-1) ^ ((tailLast.val + 2) / 2)) 0 (tailLast.val + 2) := by
      rw [min_eq_left]
      rw [hsource]
      exact hbeta
    _ = _ := by simpa only [hsource, central, first]

end BONG.GoodBONG

end Bong
