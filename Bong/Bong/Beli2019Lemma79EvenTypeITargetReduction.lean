/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTargetIntegralSplit
import Bong.Bong.Beli2019Lemma79EvenTypeILowWitnessOrder

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central target reduction

Domination, the exact low-witness order, and the integrality split close all
but the two exceptional arithmetic branches named explicitly in the paper:
the preceding alpha is nonintegral, or the capped prefix equals exactly one
less than the primary coefficient.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The two residual target-prefix branches after domination and integral
rounding. -/
def Lemma79TypeICentralTargetException
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ witness : Fin (n + 1),
    Even witness.val ∧
    witness.val + 1 < i.val ∧
    c.order witness.castSucc = b.order ⟨i.val, i.lt_large⟩ - 1 ∧
    c.truncatedPrefixDefect c (-1) witness.val (witness.val + 2) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val ∧
    (((((c.order witness.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) :
        WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val ∧
    IsWithTopRationalInteger
      (c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val) ∧
    (¬ IsRationalInteger
          (c.alphaValue (evenTargetPreviousAlphaIndex i)) ∨
        c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
          ((show ℚ from
              ((b.order ⟨i.val, i.lt_large⟩ -
                c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
              c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
            WithTop ℚ))

set_option maxHeartbeats 4000000 in
-- Dependent target indices are normalized in the low-witness coefficient.
/-- The central target self-prefix is proved unless one of the paper's two
final exceptional arithmetic branches occurs. -/
theorem beli2019Lemma79_typeI_central_even_target_reduction
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val ∨
      Lemma79TypeICentralTargetException b c i := by
  rcases lemma79_even_targetCapped_or_exists_lowWitness
      b c i hiTwo hiEven with hdone |
        ⟨j, hjEven, hjBefore, hjDefect, hjLow, hdom⟩
  · exact Or.inl hdone
  · have hjOrder := lemma79_typeI_central_lowWitness_order_eq
      a b c D C hfirst hnorm i hiEven hiLeft hiRight j hjEven hjLow
    let self : WithTop ℚ :=
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val
    by_cases hintegral : IsWithTopRationalInteger self
    · by_cases halphaIntegral : IsRationalInteger
          (c.alphaValue (evenTargetPreviousAlphaIndex i))
      · have hcoefficient :
            ((c.order j.castSucc -
                c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
                c.alphaValue (evenTargetPreviousAlphaIndex i) =
              ((b.order ⟨i.val, i.lt_large⟩ -
                c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
                c.alphaValue (evenTargetPreviousAlphaIndex i) - 1 := by
          rw [hjOrder]
          push_cast
          ring
        have hdomPrimary :
            ((show ℚ from
                ((b.order ⟨i.val, i.lt_large⟩ -
                  c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
                c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
              WithTop ℚ) ≤ self := by
          dsimp only [self]
          rw [← hcoefficient]
          exact hdom
        by_cases heq : self =
            ((show ℚ from
                ((b.order ⟨i.val, i.lt_large⟩ -
                  c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
                c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
              WithTop ℚ)
        · apply Or.inr
          exact ⟨j, hjEven, hjBefore, hjOrder,
            hjDefect,
            hdom,
            by simpa only [self] using hintegral,
            Or.inr (by simpa only [self] using heq)⟩
        · apply Or.inl
          apply lemma79_even_targetCapped_of_integral_strict_primary
            b c i hiTwo (by simpa only [self] using hintegral)
              halphaIntegral
          exact lt_of_le_of_ne hdomPrimary (Ne.symm heq)
      · apply Or.inr
        exact ⟨j, hjEven, hjBefore, hjOrder,
          hjDefect,
          hdom,
          by simpa only [self] using hintegral,
          Or.inl halphaIntegral⟩
    · exact Or.inl (lemma79_even_targetCapped_of_not_integral
        b c i hcross (by simpa only [self] using hintegral))

end BONG.GoodBONG

end Bong
