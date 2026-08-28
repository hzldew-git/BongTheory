/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIPivot

/-!
# Beli (2019), Lemma 6.9(i): propagation from the type-I pivot

Once the pivot alpha is at most one, monotonicity of `R_i + alpha_i`
controls the part before the pivot.  Antitonicity of `-R_(i+1) + alpha_i`
and the constant odd-order tail control the part after it.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- A bound at the minimal pivot propagates to every even source alpha on
the left type-I tail. -/
theorem lemma69_i_typeI_leftTailAlpha_le_of_pivot
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch)
    (P : Lemma69TypeILeftPivotData a b D C)
    (hpivotAlpha : a.alphaValue ⟨P.pivot, by
      rcases C.left_even with ⟨d, hd⟩
      have hpivotPrevious := P.pivot_le_previous
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1)
    (k : Nat) (hk : k < C.leftSwitch) (heven : Even k) :
    a.alphaValue ⟨k, by
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpivotBound : P.pivot < n + 1 := by
    have hpivotPrevious := P.pivot_le_previous
    omega
  have hkBound : k < n + 1 := by omega
  let pivotFin : Fin (n + 1) := ⟨P.pivot, hpivotBound⟩
  let kFin : Fin (n + 1) := ⟨k, hkBound⟩
  have hpivotAlpha' : a.alphaValue pivotFin ≤ 1 := by
    simpa only [pivotFin] using hpivotAlpha
  by_cases hkpivot : k ≤ P.pivot
  · have hmono := a.alphaLeftEndpoint_monotone
      (show kFin ≤ pivotFin by
        change k ≤ P.pivot
        exact hkpivot)
    have hkOrder := C.source_to_anchor k
      (hk.le.trans C.left_le_anchor) heven
    have hpivotOrder := C.source_to_anchor P.pivot
      (P.pivot_le_previous.trans (Nat.sub_le C.leftSwitch 2) |>.trans
        C.left_le_anchor) P.pivot_even
    have horders : a.order kFin.castSucc = a.order pivotFin.castSucc := by
      rw [← a.orderSequence_entryOrZero_eq_order kFin.castSucc,
        ← a.orderSequence_entryOrZero_eq_order pivotFin.castSucc]
      change a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero P.pivot
      exact hkOrder.trans hpivotOrder.symm
    unfold alphaLeftEndpoint at hmono
    rw [horders] at hmono
    linarith
  · have hpivotK : P.pivot ≤ k := Nat.le_of_lt (lt_of_not_ge hkpivot)
    have hkPrevious : k ≤ C.leftSwitch - 2 := by
      rcases C.left_even with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      omega
    have hmono := a.alphaRightEndpoint_antitone
      (show pivotFin ≤ kFin by
        change P.pivot ≤ k
        exact hpivotK)
    have hentry := P.tail_next_eq k hpivotK hkPrevious heven
    have horders : a.order kFin.succ = a.order pivotFin.succ := by
      rw [← a.orderSequence_entryOrZero_eq_order kFin.succ,
        ← a.orderSequence_entryOrZero_eq_order pivotFin.succ]
      change a.orderSequence.entryOrZero (k + 1) =
        a.orderSequence.entryOrZero (P.pivot + 1)
      exact hentry
    unfold alphaRightEndpoint at hmono
    rw [horders] at hmono
    linarith

/-- In particular, the alpha immediately before the left-switch crossing is
at most one. -/
theorem lemma69_i_typeI_previousAlpha_le_of_pivot
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch)
    (P : Lemma69TypeILeftPivotData a b D C)
    (hpivotAlpha : a.alphaValue ⟨P.pivot, by
      rcases C.left_even with ⟨d, hd⟩
      have hpivotPrevious := P.pivot_le_previous
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1) :
    a.alphaValue ⟨C.leftSwitch - 2, by
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  apply lemma69_i_typeI_leftTailAlpha_le_of_pivot
    a b D C hleftPos P hpivotAlpha (C.leftSwitch - 2)
  · omega
  · rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

/-- The left neighboring-coordinate estimate with only the pivot alpha
bound remaining. -/
theorem lemma69_v_typeI_leftNeighbor_of_pivotAlpha_le_one
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (P : Lemma69TypeILeftPivotData a b D C)
    (hpivotAlpha : a.alphaValue ⟨P.pivot, by
      rcases C.left_even with ⟨d, hd⟩
      have hpivotPrevious := P.pivot_le_previous
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1) :
    b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
      a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
  apply lemma69_v_typeI_leftNeighbor_of_previousAlpha_le_one
    a b D C hfirst hleftPos
  exact lemma69_i_typeI_previousAlpha_le_of_pivot
    a b D C hleftPos P hpivotAlpha

end BONG.GoodBONG

end Bong
