/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma717Cases
import Bong.Bong.Beli2009TwoAdic

/-!
# Beli (2019), Lemma 7.17: strict stopping-point boundaries

The maximality clause in Lemma 7.17 makes the next entry on the low parity
chain strictly larger than the terminal value.  Together with the
endpoint-above alternative this supplies exactly the two integral order
bounds needed to glue the replacement tower of Lemma 7.18 to its unchanged
suffix.
-/

namespace Bong
open Dyadic
universe u v
namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem sub_one_add_two_eq_add_one {s : Nat} (hs : 2 ≤ s) :
    (s - 1) + 2 = s + 1 := by
  omega

theorem lemma717_suffixSecond_ge
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s) (hs : s + 1 < n + 3) :
    R - 2 * (ramificationIndex K : Int) + 1 ≤
      a.order ⟨s + 1, hs⟩ := by
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  have hleftBound : left.val + 2 < n + 3 := by
    simp [left]
    omega
  have hmono := a.good left hleftBound
  change a.order left ≤ a.order ⟨left.val + 2, hleftBound⟩ at hmono
  have hindex : (⟨left.val + 2, hleftBound⟩ :
      Fin (n + 3)) = ⟨s + 1, hs⟩ := by
    apply Fin.ext
    simpa only [left] using sub_one_add_two_eq_add_one D.two_le
  rw [hindex] at hmono
  have hterminal : a.order left =
      R - 2 * (ramificationIndex K : Int) := by
    simpa [left] using D.terminal
  rw [hterminal] at hmono
  have hne := D.maximal (by omega)
  omega

theorem lemma717_suffixHead_ge
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hendpoint : Lemma717EndpointAbove a R s) (hs : s < n + 3) :
    R + 1 ≤ a.order ⟨s, hs⟩ := by
  rcases hendpoint with hend | ⟨hs', hstrict⟩
  · omega
  · have hindex : (⟨s, hs⟩ : Fin (n + 3)) = ⟨s, hs'⟩ := Fin.ext rfl
    rw [hindex]
    omega

/-- In type III the unchanged head after the selected prefix has order `R`.
The next gap cannot equal the negative odd integer `1 - 2e`; consequently
the second suffix order is one unit stronger than the general maximality
bound.  This is the boundary estimate used in Lemma 7.18(iii). -/
theorem lemma717_typeIII_suffixSecond_ge
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma717StoppingData a R s)
    (typeIII : Lemma717IsTypeIII a R s)
    (hs : s + 1 < n + 3) :
    R - 2 * (ramificationIndex K : Int) + 2 ≤
      a.order ⟨s + 1, hs⟩ := by
  rcases typeIII with ⟨hsHead, hhead⟩
  have hlower := lemma717_suffixSecond_ge a R s D hs
  by_contra hnot
  have hnextEq : a.order ⟨s + 1, hs⟩ =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    omega
  let i : Fin (n + 2) := ⟨s, by omega⟩
  have hgapEq : a.orderGap i =
      1 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    change a.order ⟨s + 1, by omega⟩ - a.order ⟨s, by omega⟩ = _
    have hnextIndex : (⟨s + 1, by omega⟩ : Fin (n + 3)) =
        ⟨s + 1, hs⟩ := Fin.ext rfl
    have hheadIndex : (⟨s, by omega⟩ : Fin (n + 3)) =
        ⟨s, hsHead⟩ := Fin.ext rfl
    rw [hnextIndex, hheadIndex, hnextEq, hhead]
    ring
  have hepos := ramificationIndex_pos (K := K)
  have hgapEven := a.orderGap_even_of_negative i (by
    rw [hgapEq]
    omega)
  rw [hgapEq] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  omega

end BONG.GoodBONG
end Bong
