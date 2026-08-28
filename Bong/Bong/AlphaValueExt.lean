/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Invariants

/-!
# Extensionality of BONG alpha invariants

The alpha invariant is computed entirely from the ordered list of nonzero
quadratic values.  This file records that fact across different ambient
quadratic spaces and lattices.  It is useful when a consecutive segment has
been inserted into a larger BONG: the segment may live in a different subtype,
but its scalar values still determine exactly the same alpha candidates.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {qV : QuadraticSpace K V} {qW : QuadraticSpace K W}
  {LV : Lattice K V} {LW : Lattice K W} {n : Nat}

/-- Equal scalar value units give equal order sequences, independently of the
ambient quadratic spaces. -/
theorem order_eq_of_valueUnits_eq
    (a : GoodBONG qV LV n) (b : GoodBONG qW LW n)
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (i : Fin n) :
    a.order i = b.order i := by
  change a.toBONG.order i = b.toBONG.order i
  rw [BONG.order_eq_ordUnit, BONG.order_eq_ordUnit]
  exact congrArg (ordUnit K) (hvalues i)

/-- Equal scalar value units give equal adjacent products. -/
theorem adjacentProduct_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (j : Fin n) :
    a.adjacentProduct j = b.adjacentProduct j := by
  unfold adjacentProduct
  rw [hvalues j.castSucc, hvalues j.succ]

/-- Equal scalar value units give equal adjacent defects. -/
theorem adjacentDefect_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (j : Fin n) :
    a.adjacentDefect j = b.adjacentDefect j := by
  unfold adjacentDefect
  rw [a.adjacentProduct_eq_of_valueUnits_eq b hvalues j]

/-- Equal scalar value units give equal half-gap candidates. -/
theorem halfGapCandidate_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (i : Fin n) :
    a.halfGapCandidate i = b.halfGapCandidate i := by
  unfold halfGapCandidate
  rw [a.order_eq_of_valueUnits_eq b hvalues i.succ,
    a.order_eq_of_valueUnits_eq b hvalues i.castSucc]

/-- Equal scalar value units give equal left-defect candidates. -/
theorem leftDefectCandidate_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i)
    (i j : Fin n) :
    a.leftDefectCandidate i j = b.leftDefectCandidate i j := by
  unfold leftDefectCandidate
  rw [a.order_eq_of_valueUnits_eq b hvalues i.succ,
    a.order_eq_of_valueUnits_eq b hvalues j.castSucc,
    a.adjacentDefect_eq_of_valueUnits_eq b hvalues j]

/-- Equal scalar value units give equal right-defect candidates. -/
theorem rightDefectCandidate_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i)
    (i j : Fin n) :
    a.rightDefectCandidate i j = b.rightDefectCandidate i j := by
  unfold rightDefectCandidate
  rw [a.order_eq_of_valueUnits_eq b hvalues j.succ,
    a.order_eq_of_valueUnits_eq b hvalues i.castSucc,
    a.adjacentDefect_eq_of_valueUnits_eq b hvalues j]

/-- Equal scalar value units identify the complete finite candidate sets. -/
theorem alphaCandidates_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (i : Fin n) :
    a.alphaCandidates i = b.alphaCandidates i := by
  have hhalf := a.halfGapCandidate_eq_of_valueUnits_eq b hvalues i
  have hleft : a.leftDefectCandidate i = b.leftDefectCandidate i := by
    funext j
    exact a.leftDefectCandidate_eq_of_valueUnits_eq b hvalues i j
  have hright : a.rightDefectCandidate i = b.rightDefectCandidate i := by
    funext j
    exact a.rightDefectCandidate_eq_of_valueUnits_eq b hvalues i j
  unfold alphaCandidates
  rw [hhalf, hleft, hright]

/-- Equal scalar value units give equal `WithTop`-valued alpha invariants. -/
theorem alpha_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (i : Fin n) :
    a.alpha i = b.alpha i := by
  have hcandidates := a.alphaCandidates_eq_of_valueUnits_eq b hvalues i
  unfold alpha
  simpa only [hcandidates]

/-- Equal scalar value units give equal rational alpha values. -/
theorem alphaValue_eq_of_valueUnits_eq
    (a : GoodBONG qV LV (n + 1)) (b : GoodBONG qW LW (n + 1))
    (hvalues : ∀ i, a.valueUnit i = b.valueUnit i) (i : Fin n) :
    a.alphaValue i = b.alphaValue i := by
  apply WithTop.coe_injective
  rw [a.coe_alphaValue, b.coe_alphaValue,
    a.alpha_eq_of_valueUnits_eq b hvalues i]

end BONG.GoodBONG

end Bong
