/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019JordanApproximation

/-!
# Coordinate range forced by Beli (2019), Lemmas 2.18 and 3.7

Inside one strict Jordan block, profile orders repeat after two positions.
Consequently, if either of the two outer two-step inequalities at an
internal coordinate is strict, that coordinate is the first, penultimate,
or last coordinate of its block.  This is the coordinate-free trichotomy
behind the four cases of Lemma 3.7.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG.JordanBlockCoordinates

/-- A strict two-step inequality can occur only at one of the three
coordinates used in Lemma 3.7: the first, penultimate, or last coordinate
of the current strict Jordan block. -/
theorem endpoint_trichotomy_of_twoStep_strict
    (a : BONG.GoodBONG q L (n + 2))
    (C : a.JordanBlockCoordinates) (i : Fin (n + 2))
    (hpositive : 0 < i.val) (hinternal : i.val + 2 < n + 2)
    (hstart : C.start ≤ i.val) (hstop : i.val < C.stop)
    (hstrict :
      a.order ⟨i.val - 1, by omega⟩ <
          a.order ⟨i.val + 1, by omega⟩ ∨
        a.order i < a.order ⟨i.val + 2, hinternal⟩) :
    i.val = C.start ∨ i.val + 1 = C.stop ∨ i.val + 2 = C.stop := by
  by_contra hcases
  push Not at hcases
  have hstartPred : C.start ≤ i.val - 1 := by omega
  have hstopSucc : i.val + 1 < C.stop := by omega
  have hstopTwo : i.val + 2 < C.stop := by omega
  have hleft := C.order_add_two_eq (i.val - 1) hstartPred (by omega)
  have hright := C.order_add_two_eq i.val hstart hstopTwo
  rcases hstrict with hstrict | hstrict
  · apply (ne_of_lt hstrict)
    simpa only [JordanBlockCoordinates.index,
      show i.val - 1 + 2 = i.val + 1 by omega] using hleft
  · apply (ne_of_lt hstrict)
    simpa only [JordanBlockCoordinates.index] using hright

end BONG.GoodBONG.JordanBlockCoordinates

end Bong
