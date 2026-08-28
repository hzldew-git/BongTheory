/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714Types
import Bong.Bong.Beli2019Lemma66

/-!
# Beli (2019), boundary orders in Lemma 7.14

This file adds the stopping clause from the definition of the minimal even
integer `s`.  It yields the lower order needed on the right of the replaced
block.  In type II, equality would make the intervening negative order gap
odd, so the universal parity law improves the lower bound by one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete minimal-endpoint data used in Lemma 7.14.  If the index
`s + 2` exists in the paper's one-based notation, its order has crossed the
threshold defining `s`. -/
structure Lemma714StoppingData
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop
    extends Lemma714MinimalityData b R s where
  at_stop (hs : s + 2 ≤ n + 3) :
    R - 2 * (ramificationIndex K : Int) + 1 <
      b.order ⟨s + 1, by omega⟩

/-- Integrality turns the strict stopping inequality into the next integer
lower bound. -/
theorem lemma714_stopOrder_ge
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s) (hs : s + 2 ≤ n + 3) :
    R - 2 * (ramificationIndex K : Int) + 2 ≤
      b.order ⟨s + 1, by omega⟩ := by
  have h := D.at_stop hs
  omega

/-- In an interior type-I case the first order after the selected segment is
at least `R + 2`. -/
theorem lemma714_typeI_nextOrder_ge
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hI : Lemma714IsTypeI b R s) (hs : s < n + 3) :
    R + 2 ≤ b.order ⟨s, hs⟩ := by
  rcases hI with hend | ⟨hs', horder⟩
  · omega
  · have hfin : (⟨s, hs⟩ : Fin (n + 3)) = ⟨s, hs'⟩ := by
      apply Fin.ext
      rfl
    rwa [hfin]

/-- The paper's parity exclusion in the type-II branch: the order at
`s + 2` is at least `R - 2e + 3`, not merely `R - 2e + 2`. -/
theorem lemma714_typeII_stopOrder_ge
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hII : Lemma714IsTypeII b R s) (hs : s + 2 ≤ n + 3) :
    R - 2 * (ramificationIndex K : Int) + 3 ≤
      b.order ⟨s + 1, by omega⟩ := by
  rcases hII with ⟨hsInterior, hcurrent⟩
  have hnext := b.lemma714_stopOrder_ge R s D hs
  by_contra hnot
  have hnextEq : b.order ⟨s + 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    omega
  let i : Fin (n + 2) := ⟨s, by omega⟩
  have hgapEq : b.orderGap i =
      1 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    change b.order ⟨s + 1, by omega⟩ - b.order ⟨s, by omega⟩ = _
    have hfin : (⟨s, by omega⟩ : Fin (n + 3)) =
        ⟨s, hsInterior⟩ := by
      apply Fin.ext
      rfl
    rw [hfin, hcurrent, hnextEq]
    ring
  have hePos := ramificationIndex_pos (K := K)
  have hgapEven := b.orderGap_even_of_negative i (by
    rw [hgapEq]
    omega)
  rw [hgapEq] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  omega

end BONG.GoodBONG

end Bong
