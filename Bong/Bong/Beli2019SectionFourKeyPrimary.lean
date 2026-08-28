/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyHalfGap
import Bong.Bong.Beli2019PrefixChange

/-!
# Beli (2019), Lemma 4.2: primary-defect candidates

This file treats the primary-defect candidate in the left direct branch of
Lemma 4.2(i).  The first boundary is separated because the target prefix is
empty there, exactly as in the endpoint convention of the paper.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- At the first boundary, the primary defects for the middle and target
BONGs have the same empty right prefix.  Condition 2.1(i) supplies the only
remaining order comparison. -/
theorem representationAlpha_le_leftDirect_sourcePrimary_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hj : j.val = 1) :
    a.representationAlpha c j ≤ a.representationPrimaryDefect b j := by
  have htargetOrder : b.order ⟨j.val - 1, by
        have := j.lt_large
        omega⟩ ≤ c.order ⟨j.val - 1, by
          have := j.lt_large
          omega⟩ := by
    rcases hbc ⟨j.val - 1, by have := j.lt_large; omega⟩ with hcurrent |
        ⟨hiPos, _, _⟩
    · exact hcurrent
    · change 0 < j.val - 1 at hiPos
      omega
  have htargetOrderZero :
      b.order ⟨0, by have := j.lt_large; omega⟩ ≤
        c.order ⟨0, by have := j.lt_large; omega⟩ := by
    simpa only [hj, Nat.reduceSubDiff] using htargetOrder
  calc
    a.representationAlpha c j ≤ a.representationPrimaryDefect c j :=
      a.representationAlpha_le_primary c j
    _ ≤ a.representationPrimaryDefect b j := by
      unfold representationPrimaryDefect
      have hdefectC :=
        a.truncatedPrefixDefect_zero_right_eq_self c (-1) (j.val + 1)
      have hdefectB :=
        a.truncatedPrefixDefect_zero_right_eq_self b (-1) (j.val + 1)
      simp only [hj, Nat.reduceSubDiff] at hdefectC hdefectB ⊢
      rw [hdefectC, hdefectB]
      gcongr
      norm_cast
      exact sub_le_sub_left htargetOrderZero
        (a.order ⟨1, by have := j.lt_large; omega⟩)

/-- Lemma 4.2(i)'s complete `C_(i-1) ≤ A_(i-1)` conclusion at `i = 2`.
There is no secondary candidate at this endpoint. -/
theorem representationAlpha_le_leftDirect_sourceAlpha_of_eq_one
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hj : j.val = 1) :
    a.representationAlpha c j ≤ a.representationAlpha b j := by
  rw [a.representationAlpha_eq_min_halfGap_prime b j,
    a.representationAlphaPrime_eq_primary_of_not_interior b j (by omega)]
  exact le_min
    (a.representationAlpha_le_leftDirect_sourceHalfGap_of_eq_one
      b c hbc j hj)
    (a.representationAlpha_le_leftDirect_sourcePrimary_of_eq_one
      b c hbc j hj)

/-- At the first boundary, `C₁` is also bounded by the half-gap candidate
of `B₁`.  If the boundary is terminal, condition 2.1(i) gives `R₂ ≤ S₂`
directly; otherwise the endpoint order lemma derives it from essentiality. -/
theorem representationAlpha_le_leftDirect_middleHalfGap_of_eq_one
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1)) (hj : j.val = 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j ≤ b.representationHalfGap c j := by
  have hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩ := by
    by_cases hlast : j.val + 1 = n + 1
    · rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, hiNext, _⟩
      · exact hcurrent
      · change j.val + 1 < n + 1 at hiNext
        omega
    · have hiNext : j.val + 1 < n + 1 := by
        have := j.lt_large
        omega
      exact keyLemmaLeftDirect_sourceCurrent_le_middleCurrent_of_eq_one
        a
        b c hab hbc j hj hiNext hessential
  calc
    a.representationAlpha c j ≤ a.representationHalfGap c j :=
      a.representationAlpha_le_halfGap c j
    _ ≤ b.representationHalfGap c j := by
      unfold representationHalfGap
      norm_cast
      simp only [Rat.divInt_eq_div]
      push_cast
      have hcast :
          (a.order ⟨j.val, j.lt_large⟩ : ℚ) ≤
            (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
        exact_mod_cast hsourceCurrent
      linarith

/-- The rank-two endpoint of Lemma 4.2(i)'s second direct conclusion.
Here the two source prefixes are complete BONGs in the same quadratic
space, so their products differ by a square and the primary defects agree
up to the already established order inequality. -/
theorem representationAlpha_le_leftDirect_middleAlpha_of_eq_one_of_last
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    {M N : Lattice K V}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : j.val = 1) (hlast : j.val + 1 = n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j ≤ b.representationAlpha c j := by
  have hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩ := by
    rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, hiNext, _⟩
    · exact hcurrent
    · change j.val + 1 < n + 1 at hiNext
      omega
  have hprimary : a.representationAlpha c j ≤
      b.representationPrimaryDefect c j := by
    calc
      a.representationAlpha c j ≤ a.representationPrimaryDefect c j :=
        a.representationAlpha_le_primary c j
      _ ≤ b.representationPrimaryDefect c j := by
        unfold representationPrimaryDefect
        rcases BONG.exists_valueProduct_eq_mul_square a.toBONG b.toBONG with
          ⟨p, hp⟩
        have hraw : (-1 : Kˣ) * b.toBONG.valueProduct * c.prefixProduct 0 =
            ((-1 : Kˣ) * a.toBONG.valueProduct * c.prefixProduct 0) * p ^ 2 := by
          rw [hp]
          ac_rfl
        have hdefect : b.truncatedPrefixDefect c (-1) (n + 1) 0 =
            a.truncatedPrefixDefect c (-1) (n + 1) 0 := by
          unfold truncatedPrefixDefect
          rw [a.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
            b.prefixProduct_eq_valueProduct_of_rank_le (n + 1) le_rfl,
            hraw, defectOrder_mul_square, a.prefixAlphaCap_last,
            b.prefixAlphaCap_last]
        have hdefectJ :
            b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
              a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) := by
          have hleft : j.val + 1 = n + 1 := hlast
          have hright : j.val - 1 = 0 := by omega
          rw [hleft, hright]
          exact hdefect
        rw [← hdefectJ]
        gcongr
        norm_cast
        exact sub_le_sub_right hsourceCurrent
          (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩)
  rw [b.representationAlpha_eq_min_halfGap_prime c j,
    b.representationAlphaPrime_eq_primary_of_not_interior c j (by omega)]
  exact le_min
    (a.representationAlpha_le_leftDirect_middleHalfGap_of_eq_one
      b c hab hbc j hj hessential)
    hprimary

end BONG.GoodBONG

end Bong
