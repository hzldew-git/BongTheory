/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralCertificates
import Bong.Bong.Beli2006SectionThree

/-!
# Beli (2019), Lemma 7.9(iii): activating the central triggers

Several of the ten cases in the proof first obtain
`beta_(i-1) + beta_i > 2e`.  Property P6 says that equality of the two
orders surrounding these alphas would force the reverse weak inequality.
Goodness already gives the weak two-step order inequality, hence the order
is strict.  When the middle orders agree, the same alpha sum is precisely
the second clause of condition 2.1(iii)'s trigger.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- A strict adjacent-alpha sum forces strict two-step growth of the order
sequence.  This is the contrapositive of P6, combined with goodness. -/
theorem order_twoStep_lt_of_alphaSum_gt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ <
      b.order ⟨i.val, i.lt_large⟩ := by
  have hiOne : 1 < i.val := i.one_lt
  have hiLarge : i.val < n + 2 := i.lt_large
  let leftOrder : Fin (n + 2) := ⟨i.val - 2, by
      have := hiOne
      have := hiLarge
      omega⟩
  have hleftTwo : leftOrder.val + 2 < n + 2 := by
    dsimp only [leftOrder]
    have := i.one_lt
    have := i.lt_large
    omega
  have hmonoRaw := b.good leftOrder hleftTwo
  have hleftOrderIndex : leftOrder =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hrightOrderIndex :
      (⟨leftOrder.val + 2, hleftTwo⟩ : Fin (n + 2)) =
        (⟨i.val, hiLarge⟩ : Fin (n + 2)) := by
    apply Fin.ext
    dsimp only [leftOrder]
    omega
  have hmono : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ ≤ b.order ⟨i.val, i.lt_large⟩ := by
    calc
      b.order ⟨i.val - 2, by omega⟩ = b.order leftOrder :=
        congrArg b.order hleftOrderIndex.symm
      _ ≤ b.order ⟨leftOrder.val + 2, hleftTwo⟩ := hmonoRaw
      _ = b.order ⟨i.val, hiLarge⟩ := congrArg b.order hrightOrderIndex
  apply lt_of_le_of_ne hmono
  intro heq
  let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  have hpreviousCast : previousAlpha.castSucc =
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnext : previousAlpha.val + 1 < n + 1 := by
    dsimp only [previousAlpha]
    have := hiLarge
    omega
  have hcurrentSucc :
      (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)).succ =
        (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change (i.val - 2 + 1) + 1 = i.val
    omega
  have hendpoint : b.order previousAlpha.castSucc =
      b.order (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)).succ := by
    rw [hpreviousCast, hcurrentSucc]
    exact heq
  have hp6 := b.alpha_p6 previousAlpha hnext hendpoint
  have hpreviousAlphaIndex : previousAlpha =
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hcurrentAlphaIndex :
      (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)) =
        (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    dsimp only [previousAlpha]
    have := hiOne
    omega
  have hp6' : b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ ≤ 2 * (ramificationIndex K : ℚ) := by
    have hpreviousValue :
        b.alphaValue (⟨i.val - 2, by omega⟩ : Fin (n + 1)) =
          b.alphaValue previousAlpha :=
      congrArg b.alphaValue hpreviousAlphaIndex.symm
    have hcurrentValue :
        b.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
          b.alphaValue ⟨previousAlpha.val + 1, hnext⟩ :=
      congrArg b.alphaValue hcurrentAlphaIndex.symm
    calc
      b.alphaValue ⟨i.val - 2, by omega⟩ +
          b.alphaValue ⟨i.val - 1, by omega⟩ =
        b.alphaValue previousAlpha +
          b.alphaValue ⟨previousAlpha.val + 1, hnext⟩ := by
            rw [hpreviousValue, hcurrentValue]
      _ ≤ 2 * (ramificationIndex K : ℚ) := hp6
  exact (not_lt_of_ge hp6' hsum)

/-- At equal rank, equality of the middle orders turns a strict sum of the
two representation alphas into the second clause of the original central
trigger. -/
theorem centralAlphaTrigger_of_sameMiddleOrder_of_alphaSum
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hcross : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ < a.order ⟨i.val, i.lt_large⟩)
    (hmiddle : a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.representationAlphaValue b i.previous +
        a.representationAlphaValue b (i.current i.lt_large.le)) :
    a.centralAlphaTrigger b i := by
  refine ⟨hcross, ?_⟩
  unfold centralAdjustedAlpha
  rw [dif_pos i.lt_large.le]
  norm_cast
  push_cast
  rw [hmiddle]
  linarith

/-- At the first common boundary, the middle target order may exceed the
source order by `delta`.  The same shift is allowed as a loss in the
preceding representation alpha; the two corrections cancel in Definition
4's adjusted alpha. -/
theorem centralAlphaTrigger_of_shiftedMiddleOrder_of_alphaSum
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (delta : ℚ)
    (hpreviousLower :
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - delta ≤
        a.representationAlphaValue b i.previous)
    (hcurrent : a.representationAlphaValue b (i.current i.lt_large.le) =
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩)
    (hmiddle : (b.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : ℚ) =
      (a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : ℚ) + delta)
    (hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    a.centralAlphaTrigger b i := by
  refine ⟨?_, ?_⟩
  · rw [hcurrentOrder]
    exact b.order_twoStep_lt_of_alphaSum_gt_twoE i hsum
  · unfold centralAdjustedAlpha
    rw [dif_pos i.lt_large.le]
    norm_cast
    push_cast
    rw [hcurrent, hmiddle]
    linarith

/-- A convenient profile-facing form of the preceding two lemmas.  If the
two relevant `(a,b)` invariants are the adjacent target alphas and the three
orders agree, their strict sum activates condition (iii) for `(a,b)`. -/
theorem centralAlphaTrigger_of_targetAlphaPair
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprevious : a.representationAlphaValue b i.previous =
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩)
    (hcurrent : a.representationAlphaValue b (i.current i.lt_large.le) =
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩)
    (hmiddle : a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩)
    (hcurrentOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    a.centralAlphaTrigger b i := by
  apply a.centralAlphaTrigger_of_sameMiddleOrder_of_alphaSum b i
  · rw [hcurrentOrder]
    exact b.order_twoStep_lt_of_alphaSum_gt_twoE i hsum
  · exact hmiddle
  · rw [hprevious, hcurrent]
    exact hsum

end BONG.GoodBONG

end Bong
