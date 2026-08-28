/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma29ComparisonReduction
import Bong.Bong.Beli2019SequenceDual
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Corollary 2.10

At an internal boundary where the source-to-target cross gap is larger than
`2e`, condition (ii) says that the comparison prefix product has defect beyond
the dyadic endpoint.  It is therefore a square.

The proof first uses Lemma 1.8(ii) on the two order sequences, then the
double-crossing case of Lemma 2.9 to identify `A_i` with its half-gap
candidate.  This is the exact input required in the `l - j = 1` case of
Lemma 2.19.
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

/-- In the double-crossing normal form of Lemma 2.9, a positive comparison
shift and condition (ii) force the half-gap value strictly below `A'_i`.
This is the non-equality used in the `l - j = 1` case of Lemma 2.19. -/
theorem representationAlpha_ne_prime_of_comparison
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hleft : b.order ⟨i.val - 2, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩)
    (hright : b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ≤
      a.order ⟨i.val + 1, hi.2⟩)
    (hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val)
    (halpha : a.representationAlpha b i =
      a.representationHalfGap b i)
    (hhalf_lt_primary : a.representationHalfGap b i <
      a.representationPrimaryDefect b i) :
    a.representationAlpha b i ≠ a.representationAlphaPrime b i := by
  have hprime :=
    a.representationAlphaPrime_eq_min_primary_comparison
      (alphaV := alphaV) (alphaW := alphaW) b i hi hleft hright
  have hhalf_le_comparison : a.representationHalfGap b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [← halpha]
    exact hcomparison
  have hshiftQ : (0 : ℚ) <
      ((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) := by
    exact_mod_cast hshift
  have hhalf_lt_secondary : a.representationHalfGap b i <
      a.representationSecondaryComparisonDefect b i hi := by
    let D := a.truncatedPrefixDefect b 1 i.val i.val
    by_cases htop : D = ⊤
    · unfold representationSecondaryComparisonDefect
      rw [show a.truncatedPrefixDefect b 1 i.val i.val = ⊤ by
        simpa only [D] using htop]
      simp only [add_top]
      simp [representationHalfGap]
    · have hDlt : D <
          (((a.order ⟨i.val, i.lt_large⟩ +
              a.order ⟨i.val + 1, hi.2⟩ -
              b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
              b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + D := by
        rw [← WithTop.coe_untop D htop, ← WithTop.coe_add]
        exact WithTop.coe_lt_coe.mpr (by linarith)
      apply hhalf_le_comparison.trans_lt
      simpa only [D, representationSecondaryComparisonDefect] using hDlt
  have hhalf_lt_prime : a.representationHalfGap b i <
      a.representationAlphaPrime b i := by
    rw [hprime]
    exact lt_min hhalf_lt_primary hhalf_lt_secondary
  intro heq
  rw [halpha] at heq
  exact (ne_of_lt hhalf_lt_prime) heq

/-- The square-class conclusion and the strict `A_i < A'_i` certificate behind
Beli (2019), Corollary 2.10, at an internal same-rank boundary. -/
theorem beli2019Corollary210_certificate
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiOne : 1 < i.val) (hiNext : i.val + 1 < n + 1)
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    IsSquare (a.prefixProduct i.val * b.prefixProduct i.val) ∧
      a.representationAlpha b i ≠ a.representationAlphaPrime b i := by
  have hiPos := i.pos
  have hiLarge := i.lt_large
  have hiSmall := i.le_small
  let O := (a.representationOrderCondition_iff b le_rfl).mp horder
  have hcrossGap :
      2 * (ramificationIndex K : Int) ≤
        a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hpair := BeliOrderSequence.le_pair_of_large_crossGap O
    a.orderSequence_isKappaBounded_two_mul_e
    b.orderSequence_isKappaBounded_two_mul_e
    (i.val - 1) (by omega) (by omega) (by
      simpa only [orderSequence_at, show i.val - 1 + 1 = i.val by omega]
        using hcrossGap)
  have hsourcePrevious_le_targetPrevious :
      a.order ⟨i.val - 1, by omega⟩ ≤
        b.order ⟨i.val - 1, by omega⟩ := by
    simpa only [orderSequence_at] using hpair.1
  have hsourceCurrent_le_targetCurrent :
      a.order ⟨i.val, i.lt_large⟩ ≤
        b.order ⟨i.val, by omega⟩ := by
    have h := hpair.2 (by omega)
    simpa only [orderSequence_at,
      show i.val - 1 + 1 = i.val by omega] using h

  let targetGap : Fin n := ⟨i.val - 2, by omega⟩
  have htargetGapDef : b.orderGap targetGap =
      b.order ⟨i.val - 1, by omega⟩ -
        b.order ⟨i.val - 2, by omega⟩ := by
    unfold orderGap
    have hsucc : targetGap.succ = ⟨i.val - 1, by omega⟩ := by
      apply Fin.ext
      simp only [targetGap, Fin.val_succ]
      omega
    have hcast : targetGap.castSucc = ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  have htargetGapLower := b.orderGap_ge_neg_two_mul_e targetGap
  rw [htargetGapDef] at htargetGapLower
  have hleft : b.order ⟨i.val - 2, by omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩ := by
    omega

  let sourceGap : Fin n := ⟨i.val, by omega⟩
  have hsourceGapDef : a.orderGap sourceGap =
      a.order ⟨i.val + 1, hiNext⟩ -
        a.order ⟨i.val, i.lt_large⟩ := by
    unfold orderGap
    have hsucc : sourceGap.succ = ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      rfl
    have hcast : sourceGap.castSucc = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
  have hsourceGapLower := a.orderGap_ge_neg_two_mul_e sourceGap
  rw [hsourceGapDef] at hsourceGapLower
  have hright : b.order ⟨i.val - 1, by omega⟩ ≤
      a.order ⟨i.val + 1, hiNext⟩ := by
    omega
  have hshift : 0 <
      a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val - 1, by omega⟩ := by
    omega

  have hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    simpa only [← a.coe_representationAlphaValue b i] using hdefect i
  have hnormal :=
    a.representationAlpha_eq_min_halfGap_primary_of_comparison
      (alphaV := sourceLaws) (alphaW := targetLaws) b i
      ⟨hiOne, hiNext⟩ hleft hright hshift hcomparison
  have hmixedNonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := sourceLaws) (alphaW := targetLaws)
    b (-1) (i.val + 1) (i.val - 1)
  have hhalf_lt_gap : a.representationHalfGap b i <
      ((((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) := by
    unfold representationHalfGap
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hstrictQ :
        (b.order ⟨i.val - 1, by omega⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hstrict
    linarith
  have hhalf_lt_primary : a.representationHalfGap b i <
      a.representationPrimaryDefect b i := by
    unfold representationPrimaryDefect
    exact hhalf_lt_gap.trans_le (le_add_of_nonneg_right hmixedNonnegative)
  have halpha : a.representationAlpha b i =
      a.representationHalfGap b i := by
    rw [hnormal, min_eq_left hhalf_lt_primary.le]
  have hcapped : a.representationHalfGap b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [← halpha]
    exact hcomparison
  have htwoE_lt_half :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.representationHalfGap b i := by
    unfold representationHalfGap
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hstrictQ :
        (b.order ⟨i.val - 1, by omega⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hstrict
    linarith
  constructor
  · apply isSquare_of_two_mul_e_lt_defectOrder
    have hraw := htwoE_lt_half.trans_le <|
      hcapped.trans (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
    simpa only [one_mul] using hraw
  · exact a.representationAlpha_ne_prime_of_comparison
      (alphaV := sourceLaws) (alphaW := targetLaws) b i
      ⟨hiOne, hiNext⟩ hleft hright hshift hcomparison halpha
      hhalf_lt_primary

/-- The square-class and strict-alpha certificate at an endpoint where
Definition 5 has no secondary candidate. -/
theorem beli2019Corollary210_of_not_interior_certificate
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hnotInterior : ¬(1 < i.val ∧ i.val + 1 < n + 1))
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    IsSquare (a.prefixProduct i.val * b.prefixProduct i.val) ∧
      a.representationAlpha b i ≠ a.representationAlphaPrime b i := by
  have hcomparison : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    simpa only [← a.coe_representationAlphaValue b i] using hdefect i
  have hprime :=
    a.representationAlphaPrime_eq_primary_of_not_interior
      b i hnotInterior
  have hnormal : a.representationAlpha b i =
      min (a.representationHalfGap b i)
        (a.representationPrimaryDefect b i) := by
    rw [a.representationAlpha_eq_min_halfGap_prime b i, hprime]
  have hmixedNonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := sourceLaws) (alphaW := targetLaws)
    b (-1) (i.val + 1) (i.val - 1)
  have hhalf_lt_gap : a.representationHalfGap b i <
      ((((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    unfold representationHalfGap
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hstrictQ :
        (b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hstrict
    linarith
  have hhalf_lt_primary : a.representationHalfGap b i <
      a.representationPrimaryDefect b i := by
    unfold representationPrimaryDefect
    exact hhalf_lt_gap.trans_le (le_add_of_nonneg_right hmixedNonnegative)
  have halpha : a.representationAlpha b i =
      a.representationHalfGap b i := by
    rw [hnormal, min_eq_left hhalf_lt_primary.le]
  have hcapped : a.representationHalfGap b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    rw [← halpha]
    exact hcomparison
  have htwoE_lt_half :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.representationHalfGap b i := by
    unfold representationHalfGap
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hstrictQ :
        (b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hstrict
    linarith
  constructor
  · apply isSquare_of_two_mul_e_lt_defectOrder
    have hraw := htwoE_lt_half.trans_le <|
      hcapped.trans (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
    simpa only [one_mul] using hraw
  · have hhalf_lt_prime : a.representationHalfGap b i <
        a.representationAlphaPrime b i := by
      rw [hprime]
      exact hhalf_lt_primary
    intro heq
    rw [halpha] at heq
    exact (ne_of_lt hhalf_lt_prime) heq

/-- Beli (2019), Corollary 2.10, at an internal same-rank boundary. -/
theorem beli2019Corollary210
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiOne : 1 < i.val) (hiNext : i.val + 1 < n + 1)
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    IsSquare (a.prefixProduct i.val * b.prefixProduct i.val) :=
  (a.beli2019Corollary210_certificate
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    b horder hdefect i hiOne hiNext hstrict).1

/-- Corollary 2.10 at an endpoint where Definition 5 has no secondary
candidate. -/
theorem beli2019Corollary210_of_not_interior
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hnotInterior : ¬(1 < i.val ∧ i.val + 1 < n + 1))
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    IsSquare (a.prefixProduct i.val * b.prefixProduct i.val) :=
  (a.beli2019Corollary210_of_not_interior_certificate
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    b hdefect i hnotInterior hstrict).1

/-- Corollary 2.10 with both the internal and endpoint conventions. -/
theorem beli2019Corollary210_complete
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiOne : 1 < i.val)
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    IsSquare (a.prefixProduct i.val * b.prefixProduct i.val) := by
  by_cases hiNext : i.val + 1 < n + 1
  · exact a.beli2019Corollary210
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b horder hdefect i hiOne hiNext hstrict
  · exact a.beli2019Corollary210_of_not_interior
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hdefect i (by omega) hstrict

/-- The strict-alpha half of Corollary 2.10, with both the internal and
endpoint conventions.  It is the hypothesis fed to Lemma 2.14 in the
`l - j = 1` proof of Lemma 2.19. -/
theorem beli2019Corollary210_alpha_ne_prime_complete
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiOne : 1 < i.val)
    (hstrict :
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val, i.lt_large⟩) :
    a.representationAlpha b i ≠ a.representationAlphaPrime b i := by
  by_cases hiNext : i.val + 1 < n + 1
  · exact (a.beli2019Corollary210_certificate
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b horder hdefect i hiOne hiNext hstrict).2
  · exact (a.beli2019Corollary210_of_not_interior_certificate
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hdefect i (by omega) hstrict).2

end BONG.GoodBONG

end Bong
