/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypes
import Bong.Bong.Beli2019Lemma79EvenTargetIntegralSplit
import Bong.Bong.Beli2019Lemma79EvenTargetParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: numerical gap-one bounds

After the identity `beta_i = S_(i+1) - S` is known, the paper bounds
`B_i` in three recurring ways: the signed primary product has odd order,
the comparison alpha cap is small enough, or the representation half-gap
is small enough.  These lemmas isolate those three numerical conclusions
from the later parity and Jordan-profile arguments.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- If the signed primary product has odd order and the comparison order
is at least the base order, the primary candidate is at most the explicit
gap-one beta. -/
theorem representationAlphaValue_le_order_sub_of_primaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))))
    (hcomparison : base ≤ c.order (evenTargetPreviousIndex i)) :
    b.representationAlphaValue c i ≤
      ((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) := by
  have hzero := b.truncatedPrefixDefect_eq_zero_of_odd_order_general
    c (-1) (i.val + 1) (i.val - 1) hodd
  have hprevious :
      (⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  apply WithTop.coe_le_coe.mp
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ = (((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) :
          WithTop Rat) := by
      unfold representationPrimaryDefect
      rw [hzero, add_zero, hprevious]
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) :
          WithTop Rat) := by
      norm_cast
      exact_mod_cast sub_le_sub_left hcomparison _

/-- A small comparison alpha cap gives the same explicit beta bound via
the primary right-cap candidate. -/
theorem representationAlphaValue_le_order_sub_of_comparisonAlpha
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hiTwo : 2 ≤ i.val)
    (hcomparison : c.alphaValue (evenTargetPreviousAlphaIndex i) ≤
      ((c.order (evenTargetPreviousIndex i) - base : Int) : Rat)) :
    b.representationAlphaValue c i ≤
      ((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) := by
  apply WithTop.coe_le_coe.mp
  calc
    (b.representationAlphaValue c i : WithTop Rat) ≤
        ((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) :
            WithTop Rat) +
          (c.alphaValue (evenTargetPreviousAlphaIndex i) :
            WithTop Rat)) :=
      lemma79_even_representationAlphaValue_le_primaryCoefficient
        b c i hiTwo
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) :
          WithTop Rat) := by
      norm_cast
      push_cast
      push_cast at hcomparison
      linarith

/-- A lower bound on the sum of the source and comparison orders makes the
representation half-gap no larger than the explicit gap-one beta. -/
theorem representationAlphaValue_le_order_sub_of_crossOrderSum
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hsum : 2 * base + 2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val, i.lt_large⟩ +
        c.order (evenTargetPreviousIndex i)) :
    b.representationAlphaValue c i ≤
      ((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) := by
  apply WithTop.coe_le_coe.mp
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ - base : Int) : Rat) :
          WithTop Rat) := by
      unfold representationHalfGap
      norm_cast
      have hsumQ :
          (2 * base + 2 * (ramificationIndex K : Int) : Int) ≤
            b.order ⟨i.val, i.lt_large⟩ +
              c.order (evenTargetPreviousIndex i) := hsum
      have hsumRat :
          ((2 * base + 2 * (ramificationIndex K : Int) : Int) : Rat) ≤
            ((b.order ⟨i.val, i.lt_large⟩ +
              c.order (evenTargetPreviousIndex i) : Int) : Rat) := by
        exact_mod_cast hsumQ
      have hprevious :
          (⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
        apply Fin.ext
        rfl
      rw [← hprevious] at hsumRat
      simp only [Rat.divInt_eq_div]
      push_cast at hsumRat ⊢
      linarith

end BONG.GoodBONG

end Bong
