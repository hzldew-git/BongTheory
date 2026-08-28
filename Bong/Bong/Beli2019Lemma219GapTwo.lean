/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary217

/-!
# Beli (2019), Lemma 2.19: the gap-two case

For `l - j = 2`, the strict order gap makes the threshold in Corollary
2.17 negative.  The relevant capped mixed defect is nonnegative, so
condition (iii) applies immediately.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Beli (2019), Lemma 2.19 when `l - j = 2`. -/
theorem beli2019Lemma219_gapTwo
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hconditions : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hstrict :
      b.order ⟨i.val - 2, by
        have := i.le_small_succ
        omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val i.lt_large.le) := by
  have hcross : b.order ⟨i.val - 2, by
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, i.lt_large⟩ := by
    omega
  have hthreshold :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ)) : WithTop ℚ) < 0 := by
    norm_cast
    push_cast
    have hstrictQ :
        (b.order ⟨i.val - 2, by
          have := i.le_small_succ
          omega⟩ : ℚ) + 2 * (ramificationIndex K : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hstrict
    linarith
  have hnonnegative : (0 : WithTop ℚ) ≤ a.centralCurrentDefect b i := by
    exact a.truncatedPrefixDefect_nonneg
      (alphaV := sourceLaws) (alphaW := targetLaws) b (-1)
        (i.val + 1) (i.val - 1)
  have htrigger := a.beli2019Corollary217_of_currentDefect
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    b le_rfl hconditions.orderCondition hconditions.defectCondition i
      hcross (hthreshold.trans_le hnonnegative)
  exact hconditions.centralRepresentations i htrigger

end BONG.GoodBONG

end Bong
