/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67TypeICanonical
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019), Lemma 7.6: the initial type-I range

Before the first type-I switch, the relevant even target orders have equal
endpoints.  Lemma 7.4(iii) therefore computes the alternating prefix defect
exactly.  At the last even prefix before the switch, Lemma 7.4(i) gives the
boundary lower bound used in the remaining cases of Lemma 7.6.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The exact equality in Lemma 7.6 strictly before the first type-I
switch.  The natural number `m` is two less than the paper's even index. -/
theorem beli2019Lemma76_early_of_canonical
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (m : Nat) (hmBound : m + 2 < n + 1) (hmEven : Even m)
    (hmEarly : m + 2 < C.leftSwitch) :
    let previous : Fin (n + 1) := ⟨m, by omega⟩
    let current : Fin (n + 1) := ⟨m + 1, by omega⟩
    let critical : ℚ :=
      ((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
        b.alphaValue previous
    b.truncatedPrefixDefect b ((-1) ^ ((m + 2) / 2)) 0 (m + 2) =
        (critical : WithTop ℚ) ∧
      critical = b.alphaValue current := by
  dsimp only
  let i : Fin (n + 1) := ⟨0, by omega⟩
  let j : Fin (n + 1) := ⟨m + 2, hmBound⟩
  have hmTwoEven : Even (m + 2) := by
    rcases hmEven with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hzero := C.target_before_left 0 (by omega) ⟨0, by omega⟩
  have hj := C.target_before_left (m + 2) hmEarly hmTwoEven
  have horder : b.order i.castSucc = b.order j.castSucc := by
    calc
      b.order i.castSucc = b.orderSequence.entryOrZero 0 := by
        symm
        simpa only [i, Fin.val_castSucc] using
          b.orderSequence_entryOrZero_eq_order i.castSucc
      _ = b.orderSequence.entryOrZero (m + 2) := hzero.trans hj.symm
      _ = b.order j.castSucc := by
        simpa only [j, Fin.val_castSucc] using
          b.orderSequence_entryOrZero_eq_order j.castSucc
  have h := b.beli2019Lemma74_iii i j (by
      change 0 < m + 2
      omega) (by
        change Even (m + 2 - 0)
        simpa only [Nat.sub_zero] using hmTwoEven) horder
  simpa only [i, j, Nat.zero_add, Nat.sub_zero,
    show m + 2 - 2 = m by omega,
    show m + 2 - 1 = m + 1 by omega] using h.1

/-- The lower-bound branch of Lemma 7.6 at the last even prefix before
the first type-I switch. -/
theorem beli2019Lemma76_boundary_of_canonical
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch) :
    let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by
      have hleft := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩
    let critical : ℚ :=
      ((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
        b.alphaValue previous
    (critical : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ (C.leftSwitch / 2)) 0 C.leftSwitch := by
  dsimp only
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let i : Fin (n + 1) := ⟨0, by omega⟩
  let j : Fin (n + 1) := ⟨C.leftSwitch - 2, by omega⟩
  have hjEven : Even (C.leftSwitch - 2) := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hzero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have hj := C.target_before_left (C.leftSwitch - 2) (by omega) hjEven
  have horder : b.order i.castSucc = b.order j.castSucc := by
    calc
      b.order i.castSucc = b.orderSequence.entryOrZero 0 := by
        symm
        simpa only [i, Fin.val_castSucc] using
          b.orderSequence_entryOrZero_eq_order i.castSucc
      _ = b.orderSequence.entryOrZero (C.leftSwitch - 2) :=
        hzero.trans hj.symm
      _ = b.order j.castSucc := by
        simpa only [j, Fin.val_castSucc] using
          b.orderSequence_entryOrZero_eq_order j.castSucc
  have h := b.beli2019Lemma74_i i j (by
      change i.val ≤ j.val
      simp only [i, j]
      omega) (by
      change Even (C.leftSwitch - 2 - 0)
      simpa only [Nat.sub_zero] using hjEven) horder
  simpa only [i, j, Nat.zero_add, Nat.sub_zero,
    show C.leftSwitch - 2 + 2 = C.leftSwitch by omega] using h

end BONG.GoodBONG

end Bong
