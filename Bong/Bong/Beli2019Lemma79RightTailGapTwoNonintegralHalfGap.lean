/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenIntegral

/-!
# Beli (2019), Lemma 7.9(ii), case 8: nonintegral half-gap estimate

A nonintegral comparison alpha lies strictly above `2e`; hence its adjacent
order gap is strictly larger than `2e`.  Substituting this into the
representation half-gap candidate gives the strict estimate used in the
exceptional even branch of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- If `gamma_(i-1)` is nonintegral, then the representation invariant is
strictly smaller than `S_(i+1) - T_(i-1)`. -/
theorem representationAlphaValue_lt_order_sub_previous_of_not_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (hiTwo : 2 <= i.val)
    (hnot : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    b.representationAlphaValue c i <
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousAlphaIndex i).castSucc : Int) : Rat) := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpSucc : p.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [p, evenTargetPreviousAlphaIndex, evenTargetPreviousIndex,
      Fin.succ_mk]
    omega
  have halphaLarge :
      2 * (ramificationIndex K : Rat) < c.alphaValue p := by
    rcases c.beli2009Corollary28_iii p with hsmall | hlarge
    · exact False.elim (hnot (by simpa only [p] using hsmall.2.2))
    · exact hlarge.1
  have hgapLarge : 2 * (ramificationIndex K : Int) < c.orderGap p :=
    ((c.beli2009Corollary28_ii p).2.2).mp halphaLarge
  have halphaHalf := c.beli2009Lemma27_ii p hgapLarge.le
  have hprimaryTop :=
    lemma79_even_representationAlphaValue_le_primaryCoefficient
      b c i hiTwo
  have hprimary : b.representationAlphaValue c i <=
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) := by
    exact_mod_cast hprimaryTop
  calc
    b.representationAlphaValue c i <=
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) := hprimary
    _ < ((b.order ⟨i.val, i.lt_large⟩ -
          c.order p.castSucc : Int) : Rat) := by
      rw [<- hpSucc]
      change
        ((b.order ⟨i.val, i.lt_large⟩ - c.order p.succ : Int) : Rat) +
            c.alphaValue p <
          ((b.order ⟨i.val, i.lt_large⟩ -
            c.order p.castSucc : Int) : Rat)
      rw [halphaHalf]
      unfold halfGapValue
      unfold orderGap at hgapLarge ⊢
      have hgapLargeQ :
          2 * (ramificationIndex K : Rat) <
            (c.order p.succ : Rat) - (c.order p.castSucc : Rat) := by
        exact_mod_cast hgapLarge
      push_cast at hgapLargeQ ⊢
      linarith

end BONG.GoodBONG

end Bong
