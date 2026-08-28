/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EvenCandidates
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Proposition 6.2: descent from the primary candidate

The primary branch compares its cross defect with the adjacent source
defect.  Failure of the direct even comparison makes that comparison strict.
Sharp multiplication for capped defects then identifies the cross defect
with the preceding diagonal comparison defect, so condition 2.1(ii) bounds
`A_(i-1)` by it.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- A cross defect strictly below the adjacent source defect is the preceding
diagonal comparison defect. -/
theorem primaryCrossDefect_eq_previousComparison_of_lt_adjacent
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) (i : Nat)
    (hlt : a.truncatedPrefixDefect b (-1) (i + 1) (i - 1) <
      a.truncatedPrefixDefect a (-1) (i - 1) (i + 1)) :
    a.truncatedPrefixDefect b (-1) (i + 1) (i - 1) =
      a.truncatedPrefixDefect b 1 (i - 1) (i - 1) := by
  have hlt' : b.truncatedPrefixDefect a (-1) (i - 1) (i + 1) <
      a.truncatedPrefixDefect a (-1) (i + 1) (i - 1) := by
    calc
      b.truncatedPrefixDefect a (-1) (i - 1) (i + 1) =
          a.truncatedPrefixDefect b (-1) (i + 1) (i - 1) :=
        b.truncatedPrefixDefect_comm a (-1) (i - 1) (i + 1)
      _ < a.truncatedPrefixDefect a (-1) (i - 1) (i + 1) := hlt
      _ = a.truncatedPrefixDefect a (-1) (i + 1) (i - 1) :=
        a.truncatedPrefixDefect_comm a (-1) (i - 1) (i + 1)
  have hmul := b.truncatedPrefixDefect_mul_eq_left_of_lt_right a a
    (-1) (-1) (i - 1) (i + 1) (i - 1) hlt'
  have hmul' : b.truncatedPrefixDefect a 1 (i - 1) (i - 1) =
      b.truncatedPrefixDefect a (-1) (i - 1) (i + 1) := by
    simpa using hmul
  calc
    a.truncatedPrefixDefect b (-1) (i + 1) (i - 1) =
        b.truncatedPrefixDefect a (-1) (i - 1) (i + 1) :=
      a.truncatedPrefixDefect_comm b (-1) (i + 1) (i - 1)
    _ = b.truncatedPrefixDefect a 1 (i - 1) (i - 1) := hmul'.symm
    _ = a.truncatedPrefixDefect b 1 (i - 1) (i - 1) :=
      b.truncatedPrefixDefect_comm a 1 (i - 1) (i - 1)

set_option maxHeartbeats 800000 in
-- Nested `WithTop` normalization and capped-defect arithmetic need extra elaboration time.
/-- In the primary branch, failure of the direct even comparison descends to
the preceding representation invariant. -/
theorem representationAlpha_previous_le_primaryCross
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val)
    (hprimary : a.representationAlpha b i =
      a.representationPrimaryDefect b i)
    (hdirect : ¬a.representationWeightEvenDirect b i) :
    a.representationAlpha b (previousRepresentationIndex i hi) ≤
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) := by
  let p : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let D := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
  let X := a.truncatedPrefixDefect a (-1) p.val (p.val + 2)
  let shift : ℚ := ((a.order p.succ - b.order p.castSucc : Int) : ℚ)
  let gap : ℚ := ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hpCast : p.castSucc = ⟨i.val - 1,
      (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
    apply Fin.ext
    rfl
  have hbeta := a.representationAlpha_le_rightAlpha b hdefect i
  rw [hprimary] at hbeta
  unfold representationPrimaryDefect at hbeta
  rw [← hpSucc, ← hpCast] at hbeta
  change (shift : WithTop ℚ) + D ≤
    (b.alphaValue p : WithTop ℚ) at hbeta
  have halphaRaw := a.alpha_le_orderGap_add_cappedAdjacent p
  have halpha : (a.alphaValue p : WithTop ℚ) ≤
      (gap : WithTop ℚ) + X := by
    simpa only [gap, X] using halphaRaw
  have hshiftEq : (a.order p.castSucc : ℚ) + gap =
      (b.order p.castSucc : ℚ) + shift := by
    dsimp only [gap, shift]
    push_cast
    ring
  have hDX : D < X := by
    by_contra hnot
    have hXD : X ≤ D := le_of_not_gt hnot
    have hdirectTop :
        ((a.order p.castSucc : ℚ) : WithTop ℚ) +
            (a.alphaValue p : WithTop ℚ) ≤
          ((b.order p.castSucc : ℚ) : WithTop ℚ) +
            (b.alphaValue p : WithTop ℚ) := by
      calc
        ((a.order p.castSucc : ℚ) : WithTop ℚ) +
              (a.alphaValue p : WithTop ℚ) ≤
            ((a.order p.castSucc : ℚ) : WithTop ℚ) +
              ((gap : WithTop ℚ) + X) := by gcongr
        _ ≤ ((a.order p.castSucc : ℚ) : WithTop ℚ) +
              ((gap : WithTop ℚ) + D) :=
          by gcongr
        _ = (((a.order p.castSucc : ℚ) + gap : ℚ) : WithTop ℚ) + D := by
          norm_num [add_assoc]
        _ = (((b.order p.castSucc : ℚ) + shift : ℚ) : WithTop ℚ) + D := by
          rw [hshiftEq]
        _ = ((b.order p.castSucc : ℚ) : WithTop ℚ) +
              ((shift : WithTop ℚ) + D) := by
          norm_num [add_assoc]
        _ ≤ ((b.order p.castSucc : ℚ) : WithTop ℚ) +
              (b.alphaValue p : WithTop ℚ) := by
          simpa only [add_comm] using
            add_le_add_left hbeta
              (((b.order p.castSucc : ℚ) : WithTop ℚ))
    have hdirectQ : (a.order p.castSucc : ℚ) + a.alphaValue p ≤
        (b.order p.castSucc : ℚ) + b.alphaValue p := by
      exact_mod_cast hdirectTop
    apply hdirect
    simpa only [representationWeightEvenDirect, p, Fin.castSucc_mk]
      using hdirectQ
  have hDX' : a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) <
      a.truncatedPrefixDefect a (-1) (i.val - 1) (i.val + 1) := by
    simpa only [D, X, p, show i.val - 1 + 2 = i.val + 1 by omega]
      using hDX
  have hcrossEq := a.primaryCrossDefect_eq_previousComparison_of_lt_adjacent
    b i.val hDX'
  have hprevious := hdefect (previousRepresentationIndex i hi)
  rw [a.coe_representationAlphaValue b (previousRepresentationIndex i hi)]
    at hprevious
  rw [hcrossEq]
  simpa only [previousRepresentationIndex] using hprevious

end BONG.GoodBONG

end Bong
