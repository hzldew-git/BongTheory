/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIEndpointEquality

/-!
# Beli (2019), Lemma 7.9(ii), case 6: strict right endpoints

Strict decrease of the right alpha endpoint turns domination into a strict
transported-coefficient inequality.  At the boundary order `T_j = R + 1`,
the type-III boundary identities then put the primary right cap strictly
below one.  If the final alpha is integral, this rounds down to zero.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Strict right-endpoint decrease makes the transported domination
coefficient strictly smaller than the central bound. -/
theorem caseSix_transportedCoefficient_lt_of_rightEndpoint_lt
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (j : Fin (n + 1)) (central : Int)
    (hadjacent : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((central : ℚ) : WithTop ℚ))
    (hendpoint : c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) <
      c.alphaRightEndpoint j) :
    ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) < (central : ℚ) := by
  have hlocalTop :=
    (c.order_sub_add_alpha_le_cappedAdjacent j).trans hadjacent
  have hlocal :
      ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j ≤ (central : ℚ) := by
    exact WithTop.coe_le_coe.mp hlocalTop
  have hlastSucc : (evenTargetPreviousAlphaIndex i).succ =
      evenTargetPreviousIndex i := by
    apply Fin.ext
    simp only [evenTargetPreviousAlphaIndex, evenTargetPreviousIndex,
      Fin.val_succ]
    omega
  unfold alphaRightEndpoint at hendpoint
  rw [hlastSucc] at hendpoint
  push_cast at hlocal hendpoint ⊢
  linarith

/-- At `T_j = R + 1`, strict transported domination puts the primary
right cap strictly below one. -/
theorem beli2019Lemma79_typeIII_caseSix_primaryRightCap_lt_one
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val - 1)
    (hadjacent : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ))
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hendpoint : c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) <
      c.alphaRightEndpoint j) :
    ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) < 1 := by
  let central : Int :=
    b.orderSequence.entryOrZero D.outer.transition.lastZero -
      a.orderSequence.entryOrZero (D.outer.transition.lastZero + 1)
  have htransported :=
    caseSix_transportedCoefficient_lt_of_rightEndpoint_lt
      c i (by omega) j central (by simpa only [central] using hadjacent)
        hendpoint
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hleftBoundary := D.outer.transition.leftBoundary
  have hrightBoundary := D.outer.transition.rightBoundary
  rw [hrightBoundary, hrightIndex] at hcurrentBoundary
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      b.orderSequence.entryOrZero i.val :=
    (b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩).symm
  have harithmetic : b.order ⟨i.val, i.lt_large⟩ -
      c.order j.castSucc + central = 1 := by
    rw [hcurrentOrder, hjOrder]
    simp only [central]
    omega
  let delta : ℚ :=
    ((b.order ⟨i.val, i.lt_large⟩ - c.order j.castSucc : Int) : ℚ)
  have hstrict : delta +
      (((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i)) <
      delta + (central : ℚ) := by
    simpa only [add_comm] using add_lt_add_left htransported delta
  calc
    ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) =
      delta +
        (((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i)) := by
        simp only [delta]
        push_cast
        ring
    _ < delta + (central : ℚ) := hstrict
    _ = 1 := by
      simp only [delta]
      exact_mod_cast harithmetic

/-- The integral-alpha half of the strict type-III boundary branch. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_lt_of_integral
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val - 1)
    (hadjacent : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ))
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hendpoint : c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) <
      c.alphaRightEndpoint j)
    (hintegral : IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiTwo : 2 ≤ i.val := by
    omega
  have hcapLt :=
    beli2019Lemma79_typeIII_caseSix_primaryRightCap_lt_one
      a b c D i hright hthroughLast heven j hjlt hadjacent hjOrder hendpoint
  have hcapIntegral : IsRationalInteger
      (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i)) :=
    hintegral.intCast_add
      (b.order ⟨i.val, i.lt_large⟩ - c.order (evenTargetPreviousIndex i))
  rcases hcapIntegral with ⟨z, hz⟩
  have hzLt : z < 1 := by
    have hzLtQ : (z : ℚ) < 1 := by simpa only [hz] using hcapLt
    exact_mod_cast hzLtQ
  have hzNonpos : z ≤ 0 := by omega
  have hcapNonpos :
      ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) ≤ 0 := by
    rw [hz]
    exact_mod_cast hzNonpos
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
          c.prefixAlphaCap (i.val - 1) :=
      lemma79_representationAlphaValue_le_primaryRightCap b c i
    _ = (((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) :=
      evenTarget_primaryRightCap_eq b c i hiTwo
    _ ≤ 0 := by exact_mod_cast hcapNonpos
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

/-- The nonintegral-alpha half of the strict type-III boundary branch. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_lt_of_nonintegral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (j : Fin (n + 1)) (hjlt : j.val + 1 < i.val - 1)
    (hadjacent : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ))
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hendpoint : c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) <
      c.alphaRightEndpoint j)
    (hnonintegral : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let last : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hgapLarge : 2 * (ramificationIndex K : Int) < c.orderGap last := by
    by_contra hnot
    apply hnonintegral
    apply c.beli2009Corollary28_i last
    rintro ⟨_, hlarge⟩
    exact hnot hlarge
  have halpha : c.alphaValue last = c.halfGapValue last :=
    c.beli2009Lemma27_ii last (by omega)
  have hcapLt :=
    beli2019Lemma79_typeIII_caseSix_primaryRightCap_lt_one
      a b c D i hright hthroughLast heven j hjlt hadjacent hjOrder hendpoint
  have hcapLt' :
      ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          (c.orderGap last : ℚ) / 2 +
          (ramificationIndex K : ℚ) < 1 := by
    rw [show c.alphaValue (evenTargetPreviousAlphaIndex i) =
      c.halfGapValue last by simpa only [last] using halpha] at hcapLt
    unfold halfGapValue at hcapLt
    simpa only [Rat.divInt_eq_div, add_assoc] using hcapLt
  have htwiceQ :
      ((2 * (b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i)) + c.orderGap last +
          2 * (ramificationIndex K : Int) : Int) : ℚ) < 2 := by
    push_cast at hcapLt' ⊢
    linarith
  have htwice :
      2 * (b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i)) + c.orderGap last +
          2 * (ramificationIndex K : Int) < 2 := by
    exact_mod_cast htwiceQ
  have hshift : b.order ⟨i.val, i.lt_large⟩ -
      c.order (evenTargetPreviousIndex i) ≤
        -(2 * (ramificationIndex K : Int)) := by
    omega
  have hpreviousIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
        evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have hhalfNonpos : b.representationHalfGap c i ≤ 0 := by
    unfold representationHalfGap
    rw [hpreviousIndex]
    norm_cast
    simp only [Rat.divInt_eq_div]
    have hshiftQ :
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) ≤
            (-(2 * (ramificationIndex K : Int)) : Int) := by
      exact_mod_cast hshift
    push_cast at hshiftQ ⊢
    linarith
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ ≤ 0 := hhalfNonpos
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
