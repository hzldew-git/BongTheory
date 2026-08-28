/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightComplete

/-!
# Beli (2019), Lemma 6.9(ii): type-I right target candidates

On an odd boundary after the canonical right switch, the source order is
one larger than the target order.  The target half-gap bound and the
right-tail estimate `beta_(i+1) <= 1` therefore bound the first two
Definition 4 candidates by `beta_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- On the odd type-I right branch, the target alpha is below the
representation half-gap candidate. -/
theorem lemma69_typeI_right_beta_le_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤ a.representationHalfGap b i := by
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst i.val hright hlast hodd
  have hsourceCurrent : a.order ⟨i.val, i.lt_large⟩ =
      b.order p.succ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    simpa only [p, Fin.val_succ,
      show i.val - 1 + 1 = i.val by omega] using horders.1
  have htargetPrevious :
      b.order ⟨i.val - 1, by have hi := i.lt_large; omega⟩ =
        b.order p.castSucc := by
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hbeta := b.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at hbeta
  have hfinite : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [hsourceCurrent, htargetPrevious]
    push_cast at hbeta ⊢
    linarith
  let rhs : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ)
  have hfinite' : b.alphaValue p ≤ rhs := by
    simpa only [rhs] using hfinite
  unfold representationHalfGap
  change (b.alphaValue p : WithTop ℚ) ≤ (rhs : WithTop ℚ)
  exact_mod_cast hfinite'

/-- On the odd type-I right branch, the target alpha is below the primary
mixed-defect candidate. -/
theorem lemma69_typeI_right_beta_le_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hiNextAlpha : i.val < n + 1 := by
    have hb := D.profile.lastDifference.bound
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  let next : Fin (n + 1) := ⟨i.val, hiNextAlpha⟩
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst i.val hright hlast hodd
  have hsourceCurrent : a.order ⟨i.val, i.lt_large⟩ =
      b.order next.castSucc + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    simpa only [next, Fin.val_castSucc] using horders.1
  have htargetPrevious :
      b.order ⟨i.val - 1, by have hi := i.lt_large; omega⟩ =
        b.order p.castSucc := by
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hnextAlpha := beli2019Lemma69_i_typeI_targetRightTail
    a b D C hfirst hrightLast hdefect i.val hright hlast hodd
  have hendpoint := b.alphaLeftEndpoint_monotone
    (show p ≤ next by
      change p.val ≤ next.val
      simp only [p, next]
      omega)
  have hrecurrence : b.alphaValue p ≤
      ((b.order next.castSucc - b.order p.castSucc : Int) : ℚ) + 1 := by
    unfold alphaLeftEndpoint at hendpoint
    have hnextAlpha' : b.alphaValue next ≤ 1 := by
      simpa only [next] using hnextAlpha
    push_cast at hendpoint ⊢
    linarith
  have hcoefficient : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) := by
    rw [hsourceCurrent, htargetPrevious]
    push_cast at hrecurrence ⊢
    linarith
  have hcoefficientTop : (b.alphaValue p : WithTop ℚ) ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficient
  have hdefectNonneg := a.truncatedPrefixDefect_nonneg
    b (-1) (i.val + 1) (i.val - 1)
  unfold representationPrimaryDefect
  exact hcoefficientTop.trans (le_add_of_nonneg_right hdefectNonneg)

end BONG.GoodBONG

end Bong
