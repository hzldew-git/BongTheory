/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftOrders

/-!
# Beli (2019), Lemma 6.9(ii): type-I left primary candidates

At an even boundary before the first type-I switch, Corollary 2.3 gives the
source-alpha formula used to control both the half-gap and primary candidates
in Definition 4.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Corollary 2.3 gives `alpha_i = R_(i+1) - R_i + 1` on the
normalized left profile. -/
theorem lemma69_typeI_left_alpha_formula
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) :
    a.alphaValue ⟨i.val - 1, by
      have h := i.lt_large
      omega⟩ =
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1, by
          have h := i.lt_large
          omega⟩ : Int) : ℚ) + 1 := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hleftPos : 0 < C.leftSwitch := by omega
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i.val (by omega) hiLeft hiEven
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have h := i.lt_large
    omega⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, by
    have h := i.lt_large
    omega⟩
  have hpreviousOne := lemma69_typeI_left_previousAlpha_eq_one
    a b D C hfirst hleftPos hdefect i.val (by omega) hiLeft hiEven
  have hpreviousOne' : a.alphaValue previous = 1 := by
    simpa only [previous] using hpreviousOne
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ = p.castSucc := by
    apply Fin.ext
    simp only [previous, p, Fin.val_succ, Fin.val_castSucc]
    omega
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hsourceEven : a.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val - 2, by omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.1
  have hadjacentSum : a.adjacentOrderSum previous =
      a.adjacentOrderSum p := by
    unfold adjacentOrderSum
    rw [hpreviousCast, hpreviousSucc, hpCast, hpSucc, hsourceEven]
    ring
  have hconstant := a.beli2009Corollary23 previous p (by
    change i.val - 2 ≤ i.val - 1
    omega) hadjacentSum
  have hrightEndpoint := hconstant.rightEndpoint_eq p (by
    change i.val - 2 ≤ i.val - 1
    omega) le_rfl
  unfold alphaRightEndpoint at hrightEndpoint
  rw [hpSucc, hpreviousSucc, hpreviousOne'] at hrightEndpoint
  rw [hpCast] at hrightEndpoint
  have hformula : a.alphaValue p =
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) + 1 := by
    push_cast at hrightEndpoint ⊢
    linarith
  simpa only [p] using hformula

/-- The source alpha is below Definition 4's half-gap candidate throughout
the type-I left source-alpha branch. -/
theorem lemma69_typeI_left_alpha_le_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) :
    (a.alphaValue ⟨i.val - 1, by
      have h := i.lt_large
      omega⟩ : WithTop ℚ) ≤ a.representationHalfGap b i := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have h := i.lt_large
    omega⟩
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i.val (by omega) hiLeft hiEven
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc - 1 := by
    rw [hpCast, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.2
  have halpha := a.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at halpha
  rw [hpSucc] at halpha
  have hfinite : a.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [← hpCast, htargetPrevious]
    push_cast at halpha ⊢
    linarith
  unfold representationHalfGap
  exact_mod_cast hfinite

/-- The source alpha is below Definition 4's primary defect candidate on the
type-I left source-alpha branch. -/
theorem lemma69_typeI_left_alpha_le_primary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val) :
    (a.alphaValue ⟨i.val - 1, by
      have h := i.lt_large
      omega⟩ : WithTop ℚ) ≤ a.representationPrimaryDefect b i := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have h := i.lt_large
    omega⟩
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i.val (by omega) hiLeft hiEven
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc - 1 := by
    rw [hpCast, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.2
  have halphaFormula := lemma69_typeI_left_alpha_formula
    a b D C hfirst hdefect i hiTwo hiLeft hiEven
  have hnonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := ‹Beli2006AlphaLaws K›)
    (alphaW := ‹Beli2006AlphaLaws K›) b (-1)
    (i.val + 1) (i.val - 1)
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) =
        a.alphaValue p := by
    rw [← hpCast, htargetPrevious]
    have hformula : a.alphaValue p =
        ((a.order ⟨i.val, i.lt_large⟩ -
          a.order p.castSucc : Int) : ℚ) + 1 := by
      simpa only [p, hpCast] using halphaFormula
    push_cast at hformula ⊢
    linarith
  unfold representationPrimaryDefect
  rw [hcoefficient]
  exact le_add_of_nonneg_right hnonnegative

end BONG.GoodBONG

end Bong
