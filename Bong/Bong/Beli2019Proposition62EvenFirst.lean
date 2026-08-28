/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EvenNoninitial

/-!
# Beli (2019), Proposition 6.2: the first even coordinate

At the first boundary, condition 2.1(i) has no pair alternative.  The half-gap
candidate gives the direct comparison as before.  For the primary candidate,
the empty target prefix turns its cross defect into the source adjacent
defect, and Remark 1.1 gives the same direct comparison.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 800000 in
-- Endpoint normal forms and the empty-prefix defect require substantial normalization.
/-- Proposition 6.2(a) at the first boundary. -/
theorem representationWeightEvenDirect_of_first
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hfirst : i.val = 1) :
    a.representationWeightEvenDirect b i := by
  have hcurrent : a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ ≤
      b.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
    let first : Fin (n + 1) := ⟨0, by
      have := i.lt_large
      omega⟩
    rcases horder first with hle | ⟨hpos, _, _⟩
    · simpa only [first, hfirst] using hle
    · simp only [first] at hpos
      omega
  have hprime : a.representationAlphaPrime b i =
      a.representationPrimaryDefect b i :=
    a.representationAlphaPrime_eq_primary_of_not_interior b i (by omega)
  have hnormal : a.representationAlpha b i =
      min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i) := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i, hprime]
  rcases min_choice (a.representationHalfGap b i)
      (a.representationPrimaryDefect b i) with hhalf | hprimary
  · exact a.representationWeightEvenDirect_of_halfGap b hdefect i
      hcurrent (hnormal.trans hhalf)
  · have hprimary' : a.representationAlpha b i =
        a.representationPrimaryDefect b i := hnormal.trans hprimary
    let p : Fin n := ⟨i.val - 1, by
      have := i.pos
      have := i.lt_large
      omega⟩
    have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
      omega
    have hpCast : p.castSucc = ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
      apply Fin.ext
      rfl
    let D := a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
    let X := a.truncatedPrefixDefect a (-1) p.val (p.val + 2)
    let shift : ℚ := ((a.order p.succ - b.order p.castSucc : Int) : ℚ)
    let gap : ℚ := ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
    have hbeta := a.representationAlpha_le_rightAlpha b hdefect i
    rw [hprimary'] at hbeta
    unfold representationPrimaryDefect at hbeta
    rw [← hpSucc, ← hpCast] at hbeta
    change (shift : WithTop ℚ) + D ≤
      (b.alphaValue p : WithTop ℚ) at hbeta
    have halphaRaw := a.alpha_le_orderGap_add_cappedAdjacent p
    have halpha : (a.alphaValue p : WithTop ℚ) ≤
        (gap : WithTop ℚ) + X := by
      simpa only [gap, X] using halphaRaw
    have hDX : D = X := by
      calc
        D = a.truncatedPrefixDefect b (-1) (i.val + 1) 0 := by
          simp only [D, hfirst]
        _ = a.truncatedPrefixDefect a (-1) (i.val + 1) 0 :=
          a.truncatedPrefixDefect_zero_right_eq_self b (-1) (i.val + 1)
        _ = a.truncatedPrefixDefect a (-1) 0 (i.val + 1) :=
          a.truncatedPrefixDefect_comm a (-1) (i.val + 1) 0
        _ = X := by
          simp only [X, p, hfirst]
    have hgapEq : (a.order p.castSucc : ℚ) + gap =
        (a.order p.succ : ℚ) := by
      dsimp only [gap]
      push_cast
      ring
    have hgapEqTop :
        ((a.order p.castSucc : ℚ) : WithTop ℚ) + (gap : WithTop ℚ) =
          ((a.order p.succ : ℚ) : WithTop ℚ) := by
      exact_mod_cast hgapEq
    have hshiftEq : (b.order p.castSucc : ℚ) + shift =
        (a.order p.succ : ℚ) := by
      dsimp only [shift]
      push_cast
      ring
    have hshiftEqTop :
        ((b.order p.castSucc : ℚ) : WithTop ℚ) + (shift : WithTop ℚ) =
          ((a.order p.succ : ℚ) : WithTop ℚ) := by
      exact_mod_cast hshiftEq
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
        _ = (((a.order p.castSucc : ℚ) : WithTop ℚ) +
              (gap : WithTop ℚ)) + X := (add_assoc _ _ _).symm
        _ = ((a.order p.succ : ℚ) : WithTop ℚ) + X := by rw [hgapEqTop]
        _ = ((a.order p.succ : ℚ) : WithTop ℚ) + D := by rw [hDX]
        _ = (((b.order p.castSucc : ℚ) : WithTop ℚ) +
              (shift : WithTop ℚ)) + D := by rw [hshiftEqTop]
        _ = ((b.order p.castSucc : ℚ) : WithTop ℚ) +
              ((shift : WithTop ℚ) + D) := add_assoc _ _ _
        _ ≤ ((b.order p.castSucc : ℚ) : WithTop ℚ) +
              (b.alphaValue p : WithTop ℚ) := by gcongr
    have hdirectQ : (a.order p.castSucc : ℚ) + a.alphaValue p ≤
        (b.order p.castSucc : ℚ) + b.alphaValue p := by
      exact_mod_cast hdirectTop
    simpa only [representationWeightEvenDirect, p, Fin.castSucc_mk]
      using hdirectQ

end BONG.GoodBONG

end Bong
