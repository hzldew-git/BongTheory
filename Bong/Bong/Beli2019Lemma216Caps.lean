/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma27

/-!
# Beli (2019), Lemma 2.16: half-gap caps

The converse implication in Lemma 2.16 uses
`d[-a_(1,i)b_(1,i-2)] ≤ β_(i-2)` and
`d[-a_(1,i+1)b_(1,i-1)] ≤ α_(i+1)`, followed by the defining half-gap
bounds for those alpha invariants.  This file records the endpoint-aware
Lean forms and the affine `WithTop` calculation used afterwards.
-/

namespace Bong

open Dyadic

universe u v w

/-- If `P` is bounded by the finite cap `p`, an affine lower bound for the
sum threshold forces `P < c + Q`.  Infinite `Q` is handled explicitly. -/
theorem withTop_lt_shift_add_of_affine_sum
    (P Q : WithTop ℚ) (c d p : ℚ)
    (hP : P ≤ (p : WithTop ℚ))
    (hbound : -c + 2 * p ≤ d)
    (hsum : (d : WithTop ℚ) < P + Q) :
    P < (c : WithTop ℚ) + Q := by
  have hPtop : P ≠ ⊤ := by
    intro htop
    rw [htop] at hP
    simp at hP
  by_cases hQtop : Q = ⊤
  · subst Q
    simp only [add_top]
    exact WithTop.lt_top_iff_ne_top.mpr hPtop
  · rw [← WithTop.coe_untop P hPtop] at hP hsum ⊢
    rw [← WithTop.coe_untop Q hQtop] at hsum ⊢
    norm_cast at hP hsum ⊢
    linarith

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The first v2 defect is bounded by the target half-gap used in the proof
of Lemma 2.16. -/
theorem centralPreviousDefect_le_halfGap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : 2 < i.val) :
    a.centralPreviousDefect b i ≤
      (b.halfGapValue ⟨i.val - 3, by
        have := i.le_small_succ
        omega⟩ : WithTop ℚ) := by
  let p : Fin n := ⟨i.val - 3, by
    have := i.le_small_succ
    omega⟩
  have hcap := a.centralPreviousDefect_le_rightCap b i
  have hinternal : i.val - 2 < n + 1 := by
    have := i.le_small_succ
    omega
  rw [b.prefixAlphaCap_of_internal (by omega) hinternal] at hcap
  have hindex : (⟨i.val - 2 - 1, by omega⟩ : Fin n) = p := by
    apply Fin.ext
    dsimp only [p]
    omega
  rw [hindex] at hcap
  exact hcap.trans (by
    exact_mod_cast b.alphaValue_le_halfGapValue p)

/-- The second v2 defect is bounded by the source half-gap used in the proof
of Lemma 2.16. -/
theorem centralCurrentDefect_le_halfGap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val + 1 < m + 1) :
    a.centralCurrentDefect b i ≤
      (a.halfGapValue ⟨i.val, by omega⟩ : WithTop ℚ) := by
  let p : Fin m := ⟨i.val, by omega⟩
  have hcap := a.centralCurrentDefect_le_leftCap b i
  rw [a.prefixAlphaCap_of_internal (by omega) hi] at hcap
  have hindex : (⟨i.val + 1 - 1, by omega⟩ : Fin m) = p := by
    apply Fin.ext
    dsimp only [p]
    omega
  rw [hindex] at hcap
  exact hcap.trans (by
    exact_mod_cast a.alphaValue_le_halfGapValue p)

end BONG.GoodBONG

end Bong
