/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneBounds

/-!
# Beli (2019), Lemma 7.9(ii), case 8: assembling gap-one beta bounds

The numerical bounds of the preceding file have the explicit right-hand
side `S_(i+1) - S`.  This file identifies it with the final beta supplied
by the strict tail formula and packages the three concrete proof routes.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The alpha index immediately to the left of a same-rank representation
boundary. -/
def caseEightLastAlphaIndex
    (i : RepresentationIndex (n + 2) (n + 2)) : Fin (n + 1) :=
  ⟨i.val - 1, by
    have hi := i.lt_large
    omega⟩

@[simp]
theorem caseEightLastAlphaIndex_val
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (caseEightLastAlphaIndex i).val = i.val - 1 := rfl

theorem caseEightLastAlphaIndex_succ
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (caseEightLastAlphaIndex i).succ = ⟨i.val, i.lt_large⟩ := by
  have hiPos := i.pos
  apply Fin.ext
  change i.val - 1 + 1 = i.val
  omega

/-- The odd-primary-product route, after substituting the final beta
formula. -/
theorem caseEight_gapOne_beta_bound_of_primaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hformula : b.alphaValue (caseEightLastAlphaIndex i) =
      ((b.order (caseEightLastAlphaIndex i).succ - base : Int) : Rat))
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))))
    (hcomparison : base ≤ c.order (evenTargetPreviousIndex i)) :
    b.representationAlphaValue c i ≤
      b.alphaValue (caseEightLastAlphaIndex i) := by
  rw [hformula, caseEightLastAlphaIndex_succ]
  exact representationAlphaValue_le_order_sub_of_primaryProduct_odd
    b c i base hodd hcomparison

/-- The comparison-alpha route, after substituting the final beta
formula. -/
theorem caseEight_gapOne_beta_bound_of_comparisonAlpha
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hformula : b.alphaValue (caseEightLastAlphaIndex i) =
      ((b.order (caseEightLastAlphaIndex i).succ - base : Int) : Rat))
    (hiTwo : 2 ≤ i.val)
    (hcomparison : c.alphaValue (evenTargetPreviousAlphaIndex i) ≤
      ((c.order (evenTargetPreviousIndex i) - base : Int) : Rat)) :
    b.representationAlphaValue c i ≤
      b.alphaValue (caseEightLastAlphaIndex i) := by
  rw [hformula, caseEightLastAlphaIndex_succ]
  exact representationAlphaValue_le_order_sub_of_comparisonAlpha
    b c i base hiTwo hcomparison

/-- The representation-half-gap route, after substituting the final beta
formula. -/
theorem caseEight_gapOne_beta_bound_of_crossOrderSum
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int)
    (hformula : b.alphaValue (caseEightLastAlphaIndex i) =
      ((b.order (caseEightLastAlphaIndex i).succ - base : Int) : Rat))
    (hsum : 2 * base + 2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val, i.lt_large⟩ +
        c.order (evenTargetPreviousIndex i)) :
    b.representationAlphaValue c i ≤
      b.alphaValue (caseEightLastAlphaIndex i) := by
  rw [hformula, caseEightLastAlphaIndex_succ]
  exact representationAlphaValue_le_order_sub_of_crossOrderSum
    b c i base hsum

/-- The three concrete numerical exits used in the gap-one branch. -/
inductive CaseEightGapOneBetaEvidence
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (base : Int) : Prop
  | primaryProduct
      (oddOrder : Odd (ordUnit K
        ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1))))
      (comparisonOrder : base ≤ c.order (evenTargetPreviousIndex i))
  | comparisonAlpha
      (two_le : 2 ≤ i.val)
      (alpha_le : c.alphaValue (evenTargetPreviousAlphaIndex i) ≤
        ((c.order (evenTargetPreviousIndex i) - base : Int) : Rat))
  | crossOrderSum
      (sum_le : 2 * base + 2 * (ramificationIndex K : Int) ≤
        b.order ⟨i.val, i.lt_large⟩ +
          c.order (evenTargetPreviousIndex i))

/-- Any of the three paper routes closes the scalar beta estimate. -/
theorem CaseEightGapOneBetaEvidence.beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    {b : GoodBONG q M (n + 2)} {c : GoodBONG q N (n + 2)}
    {i : RepresentationIndex (n + 2) (n + 2)} {base : Int}
    (E : CaseEightGapOneBetaEvidence b c i base)
    (hformula : b.alphaValue (caseEightLastAlphaIndex i) =
      ((b.order (caseEightLastAlphaIndex i).succ - base : Int) : Rat)) :
    b.representationAlphaValue c i ≤
      b.alphaValue (caseEightLastAlphaIndex i) := by
  cases E with
  | primaryProduct hodd hcomparison =>
      exact caseEight_gapOne_beta_bound_of_primaryProduct_odd
        b c i base hformula hodd hcomparison
  | comparisonAlpha hiTwo hcomparison =>
      exact caseEight_gapOne_beta_bound_of_comparisonAlpha
        b c i base hformula hiTwo hcomparison
  | crossOrderSum hsum =>
      exact caseEight_gapOne_beta_bound_of_crossOrderSum
        b c i base hformula hsum

end BONG.GoodBONG

end Bong
