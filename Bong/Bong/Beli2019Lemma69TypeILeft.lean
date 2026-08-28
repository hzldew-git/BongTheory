/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIPivotAlpha

/-!
# Beli (2019), Lemma 6.9: the type-I left tail

The pivot construction and its alpha estimate now give the source alpha
bound throughout the left tail.  The target bound propagates backwards from
the canonical switch because all even target orders there are equal.
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

/-- The source alpha is at most one at every even index before the left
type-I switch. -/
theorem beli2019Lemma69_i_typeI_sourceLeftTail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hk : k < C.leftSwitch) (heven : Even k) :
    a.alphaValue ⟨k, by
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1 := by
  rcases lemma69_i_typeI_leftPivotData a b D C hleftPos with ⟨P⟩
  apply lemma69_i_typeI_leftTailAlpha_le_of_pivot
    a b D C hleftPos P
  · exact beli2019Lemma69_i_typeI_pivotAlpha
      a b D C hfirst hleftPos P hdefect
  · exact hk
  · exact heven

/-- The target alpha is at most one at every even index before the left
type-I switch. -/
theorem beli2019Lemma69_i_typeI_targetLeftTail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (k : Nat) (hk : k < C.leftSwitch) (heven : Even k) :
    b.alphaValue ⟨k, by
      have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hkPrevious : k ≤ C.leftSwitch - 2 := by
    rcases C.left_even with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    omega
  have hpreviousEven : Even (C.leftSwitch - 2) := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  let kFin : Fin (n + 1) := ⟨k, by omega⟩
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by omega⟩
  have hmono := b.alphaLeftEndpoint_monotone
    (show kFin ≤ previous by
      change k ≤ C.leftSwitch - 2
      exact hkPrevious)
  have hkOrder := C.target_before_left k hk heven
  have hpreviousOrder := C.target_before_left (C.leftSwitch - 2)
    (by omega) hpreviousEven
  have horders : b.order kFin.castSucc = b.order previous.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order kFin.castSucc,
      ← b.orderSequence_entryOrZero_eq_order previous.castSucc]
    change b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero (C.leftSwitch - 2)
    exact hkOrder.trans hpreviousOrder.symm
  unfold alphaLeftEndpoint at hmono
  rw [horders] at hmono
  have hpreviousAlpha :=
    beli2019Lemma69_i_typeI_leftSwitch a b D C hfirst hleftPos
  have hpreviousAlpha' : b.alphaValue previous ≤ 1 := by
    simpa only [previous] using hpreviousAlpha
  linarith

/-- Both source and target alpha bounds on the type-I left tail. -/
theorem beli2019Lemma69_i_typeI_leftTail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hk : k < C.leftSwitch) (heven : Even k) :
    a.alphaValue ⟨k, by
        have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ ≤ 1 ∧
      b.alphaValue ⟨k, by
        have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ ≤ 1 := by
  exact ⟨beli2019Lemma69_i_typeI_sourceLeftTail
      a b D C hfirst hleftPos hdefect k hk heven,
    beli2019Lemma69_i_typeI_targetLeftTail
      a b D C hfirst hleftPos k hk heven⟩

/-- The left neighboring-coordinate estimate of Lemma 6.9(v), with the
type-I pivot input fully discharged. -/
theorem beli2019Lemma69_v_typeI_leftNeighbor
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefect : a.RepresentationDefectCondition b) :
    b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
      a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
  apply lemma69_v_typeI_leftNeighbor_of_previousAlpha_le_one
    a b D C hfirst hleftPos
  apply beli2019Lemma69_i_typeI_sourceLeftTail
    a b D C hfirst hleftPos hdefect (C.leftSwitch - 2)
  · omega
  · rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

end BONG.GoodBONG

end Bong
