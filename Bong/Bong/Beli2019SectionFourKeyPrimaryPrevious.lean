/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPrimaryExtraction

/-!
# Beli (2019), Lemma 4.2: the preceding middle invariant

In the primary-candidate branch of Lemma 4.2(i), the case
`T_(i-2) ≤ S_i` uses Lemma 2.7(ii) at the preceding boundary.  The first
theorem below records the `i = 2` endpoint, where the secondary candidate
does not exist.  The second records the three-candidate interior formula.
-/

namespace Bong

open Dyadic

universe u w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {r : QuadraticSpace K W} {s : QuadraticSpace K U}
  {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- At `i = 2`, `B_(i-2)` has only the half-gap and primary candidates. -/
theorem previousMiddleAlpha_eq_min_halfGap_primary_of_eq_two
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : j.val = 2) :
    b.representationAlpha c (previousRepresentationIndex j (by omega)) =
      min
        (b.representationHalfGap c
          (previousRepresentationIndex j (by omega)))
        (b.representationPrimaryDefect c
          (previousRepresentationIndex j (by omega))) := by
  let k := previousRepresentationIndex j (by omega)
  have hnot : ¬(1 < k.val ∧ k.val + 1 < n + 1) := by
    dsimp only [k, previousRepresentationIndex]
    omega
  rw [b.representationAlpha_eq_min_halfGap_prime c k,
    b.representationAlphaPrime_eq_primary_of_not_interior c k hnot]

/-- If `i > 2` and `T_(i-2) ≤ S_i`, Lemma 2.7(ii) gives the exact
three-candidate formula for `B_(i-2)`. -/
theorem previousMiddleAlpha_eq_min_halfGap_primary_current_of_cross
    [Beli2006AlphaLaws.{u, z} K]
    (b : GoodBONG r M (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hj : 2 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    let k := previousRepresentationIndex j (by omega)
    let hk : 1 < k.val ∧ k.val + 1 < n + 1 := by
      have := j.lt_large
      dsimp only [k, previousRepresentationIndex]
      omega
    b.representationAlpha c k =
      min (b.representationHalfGap c k)
        (min (b.representationPrimaryDefect c k)
          (b.representationSecondaryCurrentDefect c k hk)) := by
  dsimp only
  let k := previousRepresentationIndex j (by omega)
  have hk : 1 < k.val ∧ k.val + 1 < n + 1 := by
    have := j.lt_large
    dsimp only [k, previousRepresentationIndex]
    omega
  have hcross' : c.order ⟨k.val - 1, by
      have := k.le_small
      omega⟩ ≤ b.order ⟨k.val + 1, hk.2⟩ := by
    simpa only [k, previousRepresentationIndex,
      Nat.sub_sub, Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using hcross
  rw [b.representationAlpha_eq_min_halfGap_prime c k,
    b.representationAlphaPrime_eq_min_primary_current c k hk hcross']

/-- After shifting by `R_i-S_(i-1)`, the half-gap candidate of
`B_(i-2)` is no smaller than `C_(i-1)`.  This is the first deletion in
the displayed minimum on lines 2191--2194. -/
theorem targetAlpha_le_shift_previousMiddleHalfGap_of_cross
    [Beli2006AlphaLaws.{u, z} K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hprevious : b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        b.representationHalfGap c
          (previousRepresentationIndex j hiTwo) := by
  let targetPair : Fin n := ⟨j.val - 2, by
    have := j.lt_large
    omega⟩
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  calc
    a.representationAlpha c j ≤
        a.representationAlphaPrime c j :=
      a.representationAlpha_le_prime c j
    _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          (c.halfGapValue targetPair : WithTop ℚ) :=
      a.representationAlphaPrime_le_primaryRightHalfGap c j hiTwo
    _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.representationHalfGap c
            (previousRepresentationIndex j hiTwo) := by
      unfold representationHalfGap
      norm_cast
      unfold halfGapValue orderGap
      rw [htargetCast, htargetSucc]
      simp only [previousRepresentationIndex, Nat.sub_sub]
      simp only [Rat.divInt_eq_div]
      push_cast
      have hpreviousQ :
          (b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) ≤
            (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) := by
        exact_mod_cast hprevious
      linarith

end BONG.GoodBONG

end Bong
