/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma36

/-!
# He (2024), Lemma 3.7

The first theorem records the paper's chained terminal-defect inequalities.
The second records the additional strict source-gap consequence.  The odd
paper rank `n >= 3` is parameterized as `n = 2 * t + 3`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- The first assertion of He, Lemma 3.7, with an arbitrary source tail. -/
theorem he2022ClassicLemma37BoundsLongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let mixed :=
      a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2)
    let shift : WithTop ℚ :=
      ((((b.order ⟨2 * t + 2, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ))
    let comparison :=
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3)
    mixed <= shift + comparison ∧ shift + comparison <= shift + 1 := by
  dsimp only
  let mixed :=
    a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2)
  let comparison :=
    a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3)
  let shift : WithTop ℚ :=
    ((((b.order ⟨2 * t + 2, by omega⟩ -
      a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ))
  have hLemma36 := a.he2022ClassicLemma36LongSource t b hm
    hAClassic hBClassic hRBefore hRAt hAlpha hSourceEquality
  have hComparisonUpper : comparison <= (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b 1
      (2 * t + 3) (2 * t + 3)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hcapAlpha :
        a.alphaValue ⟨2 * t + 3 - 1, by omega⟩ = 1 := by
      convert hAlpha using 1
      congr 2
    rw [hcapAlpha] at hcap
    simpa [comparison] using hcap
  have hComparisonNe : comparison ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hComparisonUpper
  have hMixedNe : mixed ≠ ⊤ := by
    let lastGap : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      (2 * t + 4) (2 * t + 2)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hcapNe : (b.alphaValue lastGap : WithTop ℚ) ≠ ⊤ :=
      WithTop.coe_ne_top
    apply ne_top_of_le_ne_top hcapNe
    have hindex :
        (⟨2 * t + 2 - 1, by omega⟩ : Fin (2 * t + 2)) = lastGap := by
      apply Fin.ext
      simp only [lastGap]
      omega
    rw [hindex] at hcap
    simpa only [mixed] using hcap
  constructor
  · change mixed <= shift + comparison
    change
      (((a.order ⟨2 * t + 3, by omega⟩ -
        b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          mixed <= comparison at hLemma36
    rw [← WithTop.coe_untop mixed hMixedNe,
      ← WithTop.coe_untop comparison hComparisonNe] at hLemma36 ⊢
    dsimp only [shift]
    norm_cast at hLemma36 ⊢
    push_cast at hLemma36 ⊢
    linarith
  · change shift + comparison <= shift + 1
    exact add_le_add_right hComparisonUpper shift

/-- Exact-rank specialization of the first assertion of Lemma 3.7. -/
theorem he2022ClassicLemma37Bounds (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let mixed :=
      a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2)
    let shift : WithTop ℚ :=
      ((((b.order ⟨2 * t + 2, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ))
    let comparison :=
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3)
    mixed <= shift + comparison ∧ shift + comparison <= shift + 1 := by
  exact a.he2022ClassicLemma37BoundsLongSource (m := 2 * t + 1)
    t b (by omega) hAClassic hBClassic hRBefore hRAt hAlpha
      hSourceEquality

/-- The second assertion of He, Lemma 3.7. -/
theorem he2022ClassicLemma37GapLongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 5 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (hNextMixedZero :
      a.truncatedPrefixDefect b (-1) (2 * t + 5) (2 * t + 3) = 0)
    (hLarge :
      ((((2 * (ramificationIndex K : Int) +
          b.order ⟨2 * t + 2, by omega⟩ -
          a.order ⟨2 * t + 4, by omega⟩ : Int) : ℚ) : WithTop ℚ)) <
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) +
          a.truncatedPrefixDefect b (-1) (2 * t + 5) (2 * t + 3)) :
    2 * (ramificationIndex K : Int) - 1 <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ := by
  have hBounds := a.he2022ClassicLemma37BoundsLongSource
    (m := m + 1) t b (by omega) hAClassic hBClassic hRBefore hRAt
      hAlpha hSourceEquality
  have hUpper :
      a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
        (((b.order ⟨2 * t + 2, by omega⟩ -
          a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          1 := hBounds.1.trans hBounds.2
  rw [hNextMixedZero, add_zero] at hLarge
  have hFiniteStrict :
      ((((2 * (ramificationIndex K : Int) +
          b.order ⟨2 * t + 2, by omega⟩ -
          a.order ⟨2 * t + 4, by omega⟩ : Int) : ℚ) : WithTop ℚ)) <
        (((b.order ⟨2 * t + 2, by omega⟩ -
          a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          1 := hLarge.trans_le hUpper
  norm_cast at hFiniteStrict
  push_cast at hFiniteStrict
  exact_mod_cast (show
    2 * (ramificationIndex K : Int) - 1 <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ by
          linarith)

/-- Exact-rank specialization of the strict source-gap assertion. -/
theorem he2022ClassicLemma37Gap (t : Nat)
    (a : GoodBONG q L (2 * t + 5))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (hNextMixedZero :
      a.truncatedPrefixDefect b (-1) (2 * t + 5) (2 * t + 3) = 0)
    (hLarge :
      ((((2 * (ramificationIndex K : Int) +
          b.order ⟨2 * t + 2, by omega⟩ -
          a.order ⟨2 * t + 4, by omega⟩ : Int) : ℚ) : WithTop ℚ)) <
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) +
          a.truncatedPrefixDefect b (-1) (2 * t + 5) (2 * t + 3)) :
    2 * (ramificationIndex K : Int) - 1 <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ := by
  exact a.he2022ClassicLemma37GapLongSource (m := 2 * t + 1)
    t b (by omega) hAClassic hBClassic hRBefore hRAt hAlpha
      hSourceEquality hNextMixedZero hLarge

end BONG.GoodBONG

end Bong
