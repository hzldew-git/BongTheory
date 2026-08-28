/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityProfile
import Bong.Bong.Beli2019Lemma79EvenTargetDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the odd-jump bound

An earlier adjacent pair of odd order has zero quadratic defect.  Monotonicity
of the right alpha endpoints then bounds the alpha immediately before the
current coordinate.  If the pair starts strictly above the profile reference
order, the primary right cap is nonpositive and proves condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- An earlier odd adjacent pair starting above `reference` bounds the alpha
at the final boundary by `current - reference - 1`. -/
theorem caseSix_previousAlpha_le_current_sub_reference_sub_one_of_odd_pair
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (reference : Int) (j : Fin (n + 1))
    (hjlt : j.val + 1 < i.val)
    (hsumOdd : Odd (c.order j.castSucc + c.order j.succ))
    (hreference : reference < c.order j.castSucc) :
    c.alphaValue (evenTargetPreviousAlphaIndex i) ≤
      ((c.order (evenTargetPreviousIndex i) - reference - 1 : Int) : ℚ) := by
  have hzero : c.adjacentDefect j = 0 :=
    c.adjacentDefect_eq_zero_of_order_sum_odd j hsumOdd
  have hlocalTop := c.order_sub_add_alpha_le_adjacentDefect j
  rw [hzero] at hlocalTop
  have hlocal :
      ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j ≤ 0 := by
    exact_mod_cast hlocalTop
  let last : Fin (n + 1) := ⟨i.val - 2, by
    have hiLarge := i.lt_large
    omega⟩
  have hjLast : j ≤ last := by
    change j.val ≤ last.val
    simp only [last]
    omega
  have hendpoint := c.alphaRightEndpoint_antitone hjLast
  have hlastSucc : last.succ = evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [last, evenTargetPreviousIndex, Fin.val_succ]
    omega
  have hlastAlpha : c.alphaValue last =
      c.alphaValue (evenTargetPreviousAlphaIndex i) := by
    apply congrArg c.alphaValue
    apply Fin.ext
    simp only [last, evenTargetPreviousAlphaIndex]
  unfold alphaRightEndpoint at hendpoint
  rw [hlastSucc, hlastAlpha] at hendpoint
  push_cast at hlocal hendpoint ⊢
  have hreferenceOne : (reference : ℚ) + 1 ≤
      (c.order j.castSucc : ℚ) := by
    exact_mod_cast (show reference + 1 ≤ c.order j.castSucc by omega)
  linarith

/-- The primary right cap closes condition 2.1(ii) from the odd-pair alpha
bound and the profile identity `target current = reference + 1`. -/
theorem lemma79_caseSix_secondParity_of_odd_pair_above_reference
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (reference : Int) (j : Fin (n + 1))
    (hcurrent : b.order ⟨i.val, i.lt_large⟩ = reference + 1)
    (hjlt : j.val + 1 < i.val)
    (hsumOdd : Odd (c.order j.castSucc + c.order j.succ))
    (hreference : reference < c.order j.castSucc) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by omega
  have hgamma :=
    caseSix_previousAlpha_le_current_sub_reference_sub_one_of_odd_pair
      c i reference j hjlt hsumOdd hreference
  have hprimary := lemma79_representationAlphaValue_le_primaryRightCap
    b c i
  rw [evenTarget_prefixAlphaCap c i hiTwo] at hprimary
  have hcoefficient :
      ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) ≤ 0 := by
    rw [hcurrent]
    push_cast at hgamma ⊢
    linarith
  have hcoefficientTop :
      (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
          (c.alphaValue (evenTargetPreviousAlphaIndex i) : WithTop ℚ) ≤
        0 := by
    exact_mod_cast hcoefficient
  exact hprimary.trans (hcoefficientTop.trans
    (b.truncatedPrefixDefect_nonneg c 1 i.val i.val))

/-- The odd-pair closure specialized to the constant `T` of the type-II
right profile. -/
theorem beli2019Lemma79_typeII_caseSix_secondParity_of_oddPairAboveReference
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    {N : Lattice K V} (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val)
    (hsumOdd : Odd (c.order j.castSucc + c.order j.succ))
    (hreference :
      b.orderSequence.entryOrZero D.outer.transition.lastZero <
        c.order j.castSucc) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hcurrentEntry : b.orderSequence.entryOrZero i.val = T + 1 := by
    rw [hcurrentBoundary, D.right_target]
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentEntry
  exact lemma79_caseSix_secondParity_of_odd_pair_above_reference
    b c i T j hcurrent hjlt hsumOdd (by simpa only [T] using hreference)

end BONG.GoodBONG

end Bong
