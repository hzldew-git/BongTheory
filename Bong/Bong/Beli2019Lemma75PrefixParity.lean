/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma75Arithmetic
import Bong.Bong.Beli2019Lemma72Arithmetic

/-!
# Beli (2019), Lemma 7.5: prefix parity

Every order in the alternating segment is congruent to its high order modulo
two.  When the segment starts at the first coordinate, every contained
prefix sum is therefore congruent to its length times that order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Every prefix contained in a Lemma 7.5 segment starting at zero has the
expected order parity. -/
theorem Lemma75ArithmeticConsequences.prefixSum_modEq_of_first_zero
    (b : GoodBONG q L (n + 2)) (first lastPair : Fin (n + 1))
    (R : Int) (C : Lemma75ArithmeticConsequences b first lastPair R)
    (hfirst : first.val = 0)
    (hlastEven : Even (lastPair.val - first.val)) (length : Nat)
    (hlength : length ≤ lastPair.val + 2) :
    Int.ModEq 2 (b.orderSequence.prefixSum length)
      ((length : Int) * R) := by
  apply b.orderSequence.prefixSum_modEq_mul R length
  intro k hk
  have hkBound : k < n + 2 := by
    have hlastBound := lastPair.isLt
    omega
  rw [b.orderSequence_entryOrZero_eq_order ⟨k, hkBound⟩]
  rcases Nat.even_or_odd k with heven | hodd
  · let kPair : Fin (n + 1) := ⟨k, by
      have hlastBound := lastPair.isLt
      rcases heven with ⟨d, hd⟩
      rcases hlastEven with ⟨e, he⟩
      omega⟩
    have hkFirst : first ≤ kPair := by
      apply Fin.mk_le_mk.mpr
      omega
    have hkLast : kPair ≤ lastPair := by
      apply Fin.mk_le_mk.mpr
      rcases heven with ⟨d, hd⟩
      rcases hlastEven with ⟨e, he⟩
      omega
    have hkEven : Even (kPair.val - first.val) := by
      simpa only [hfirst, Nat.sub_zero, kPair] using heven
    have horder := C.even_order kPair hkFirst hkLast hkEven
    have hindex : (⟨k, hkBound⟩ : Fin (n + 2)) = kPair.castSucc := by
      apply Fin.ext
      rfl
    rw [hindex, horder]
  · have hkPos : 0 < k := by
      rcases hodd with ⟨d, hd⟩
      omega
    let kEntry : Fin (n + 2) := ⟨k, hkBound⟩
    have hkFirst : first.val + 1 ≤ kEntry.val := by
      simp only [kEntry, hfirst]
      exact hkPos
    have hkLast : kEntry.val ≤ lastPair.val + 1 := by
      simp only [kEntry]
      omega
    have hkEven : Even (kEntry.val - (first.val + 1)) := by
      rcases hodd with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      simp only [kEntry, hfirst]
      omega
    have horder := C.odd_order kEntry hkFirst hkLast hkEven
    rw [horder, Int.modEq_iff_dvd]
    refine ⟨(ramificationIndex K : Int), ?_⟩
    ring

end BONG.GoodBONG

end Bong
