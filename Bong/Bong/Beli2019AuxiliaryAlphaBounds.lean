/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlpha

/-!
# Beli (2019), bounds for `A'_i`

The remarks following Definition 5 bound `A'_i` by each alpha cap occurring
in its primary and secondary candidates.  We retain the endpoint-safe cap
form: at an endpoint the corresponding cap is `⊤`, exactly implementing the
paper's convention that nonexistent terms are ignored.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The primary candidate bounds `A'_i` after replacing its defect by the
left prefix alpha cap. -/
theorem representationAlphaPrime_le_primaryLeftCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.prefixAlphaCap (i.val + 1) := by
  calc
    a.representationAlphaPrime b i ≤
        a.representationPrimaryDefect b i :=
      a.representationAlphaPrime_le_primaryDefect b i
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.prefixAlphaCap (i.val + 1) := by
      unfold representationPrimaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_leftCap b (-1) (i.val + 1) (i.val - 1)) _

/-- The primary candidate bounds `A'_i` after replacing its defect by the
right prefix alpha cap. -/
theorem representationAlphaPrime_le_primaryRightCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.prefixAlphaCap (i.val - 1) := by
  calc
    a.representationAlphaPrime b i ≤
        a.representationPrimaryDefect b i :=
      a.representationAlphaPrime_le_primaryDefect b i
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.prefixAlphaCap (i.val - 1) := by
      unfold representationPrimaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_rightCap b (-1) (i.val + 1) (i.val - 1)) _

/-- The secondary candidate bounds `A'_i` through its left prefix alpha cap. -/
theorem representationAlphaPrime_le_secondaryLeftCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.prefixAlphaCap (i.val + 2) := by
  calc
    a.representationAlphaPrime b i ≤
        a.representationSecondaryDefect b i hi :=
      a.representationAlphaPrime_le_secondaryDefect b i hi
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + a.prefixAlphaCap (i.val + 2) := by
      unfold representationSecondaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_leftCap b 1 (i.val + 2) (i.val - 2)) _

/-- The secondary candidate bounds `A'_i` through its right prefix alpha cap. -/
theorem representationAlphaPrime_le_secondaryRightCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlphaPrime b i ≤
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.prefixAlphaCap (i.val - 2) := by
  calc
    a.representationAlphaPrime b i ≤
        a.representationSecondaryDefect b i hi :=
      a.representationAlphaPrime_le_secondaryDefect b i hi
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.prefixAlphaCap (i.val - 2) := by
      unfold representationSecondaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_rightCap b 1 (i.val + 2) (i.val - 2)) _

/-- The first defect in condition (iii') is bounded by its target-side alpha
cap, including the left endpoint convention. -/
theorem centralPreviousDefect_le_rightCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralPreviousDefect b i ≤ b.prefixAlphaCap (i.val - 2) := by
  exact a.truncatedPrefixDefect_le_rightCap b (-1) i.val (i.val - 2)

/-- The second defect in condition (iii') is bounded by its source-side alpha
cap, including the right endpoint convention. -/
theorem centralCurrentDefect_le_leftCap
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) :
    a.centralCurrentDefect b i ≤ a.prefixAlphaCap (i.val + 1) := by
  exact a.truncatedPrefixDefect_le_leftCap b (-1) (i.val + 1) (i.val - 1)

end BONG.GoodBONG

end Bong
