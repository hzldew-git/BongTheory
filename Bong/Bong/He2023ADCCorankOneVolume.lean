/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankOneTests
import Bong.Bong.He2023ADCOddMaximalStructure

/-!
# The volume argument in the even corank-one ADC classification

An integral lattice has volume order differing from a maximal lattice in
the same ambient space by an even nonnegative integer. A gap at most one
therefore proves maximality, without assuming a converse to Proposition 4.13.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A volume-order gap at most one above a maximal lattice is zero. -/
theorem heADCIsOMaximal_of_volumeOrder_le_add_one
    (hL : Lattice.IsIntegral q L) (hM : Lattice.IsOMaximal r M)
    (ambient : q.IsIsometric r)
    (hvolume : Lattice.volumeOrder q L ≤ Lattice.volumeOrder r M + 1) :
    Lattice.IsOMaximal q L := by
  obtain ⟨P, hLP, hP⟩ := Lattice.exists_oMaximal_superlattice hL
  obtain ⟨f⟩ := Lattice.oMaximal_isIsometric_of_isometric hP hM ambient
  have hvolP := Lattice.volumeOrder_eq_of_isometry f
  obtain ⟨j, hj⟩ := Lattice.exists_volumeOrder_eq_add_two_mul_nat q hLP
  have heq : Lattice.volumeOrder q L = Lattice.volumeOrder q P := by omega
  have hLP' := Lattice.eq_of_le_of_volumeOrder_eq q L P hLP heq
  rwa [hLP']

namespace BONG.GoodBONG

/-- Split the volume sum at the last three coordinates of an odd-rank BONG. -/
theorem heADCOdd_volumeOrder_split (k : Nat) (a : GoodBONG q L (2 * k + 3)) :
    Lattice.volumeOrder q L = a.orderSequence.prefixSum (2 * k) +
      a.order ⟨2 * k, by omega⟩ + a.order ⟨2 * k + 1, by omega⟩ +
      a.order ⟨2 * k + 2, by omega⟩ := by
  rw [a.toBONG.volumeOrder_eq_ordUnit_valueProduct_all]
  change ordUnit K (a.prefixProduct (2 * k + 3)) = _
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum _ le_rfl]
  change a.orderSequence.prefixSum ((2 * k + 2) + 1) = _
  rw [BeliOrderSequence.prefixSum_succ,
    BeliOrderSequence.prefixSum_add_two,
    a.orderSequence.entryOrZero_of_lt (show 2 * k < 2 * k + 3 by omega),
    a.orderSequence.entryOrZero_of_lt (show 2 * k + 1 < 2 * k + 3 by omega),
    a.orderSequence.entryOrZero_of_lt (show 2 * k + 2 < 2 * k + 3 by omega)]
  simp only [orderSequence_at]
  ring

/-- The volume of a displayed odd maximal profile, without needing to
evaluate the common alternating-head sum. -/
theorem heADCOdd_profile_volumeOrder (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (p s : Int) (horders : ∀ i, a.order i =
      heADCMaximalOrderProfile (K := K) k ![0, p, s] ⟨i.val, by omega⟩) :
    Lattice.volumeOrder q L = a.orderSequence.prefixSum (2 * k) + p + s := by
  have hzero : a.order ⟨2 * k, by omega⟩ = 0 := by
    simpa [heADCMaximalOrderProfile] using horders ⟨2 * k, by omega⟩
  have hfirst : a.order ⟨2 * k + 1, by omega⟩ = p := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
      show 2 * k + 1 - 2 * k = 1 by omega] using horders ⟨2 * k + 1, by omega⟩
  have hsecond : a.order ⟨2 * k + 2, by omega⟩ = s := by
    simpa [heADCMaximalOrderProfile, show ¬ 2 * k + 2 < 2 * k by omega,
      show 2 * k + 2 - 2 * k = 2 by omega] using horders ⟨2 * k + 2, by omega⟩
  rw [a.heADCOdd_volumeOrder_split k, hzero, hfirst, hsecond, add_zero]

/-- The shared alternating head contributes the same volume to both BONGs. -/
theorem heADCOdd_prefixSum_eq_of_head_profile (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (b : GoodBONG r M (2 * k + 3))
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (p s : Int) (horders : ∀ i, b.order i =
      heADCMaximalOrderProfile (K := K) k ![0, p, s] ⟨i.val, by omega⟩) :
    a.orderSequence.prefixSum (2 * k) = b.orderSequence.prefixSum (2 * k) := by
  apply BeliOrderSequence.prefixSum_eq_of_entryOrZero_eq_before
  intro j hj
  rw [BeliOrderSequence.entryOrZero_of_lt _ (by omega),
    BeliOrderSequence.entryOrZero_of_lt _ (by omega), orderSequence_at, orderSequence_at]
  have hb := horders ⟨j, by omega⟩
  simp only [heADCMaximalOrderProfile, dif_pos hj] at hb
  exact (hhead ⟨j, hj⟩).trans hb.symm

/-- The unraised final pair and next order at most one already force
maximality, using the proved possible profiles of a maximal superlattice. -/
theorem heADCCorankOne_standardTail_isOMaximal (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (hL : Lattice.IsIntegral q L)
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)))
    (hnext : a.order ⟨2 * k + 2, by omega⟩ ≤ 1) : Lattice.IsOMaximal q L := by
  obtain ⟨P, _, hP⟩ := Lattice.exists_oMaximal_superlattice hL
  let b : GoodBONG q P (2 * k + 3) :=
    (GoodBONG.ofLattice q P).castLength a.toBONG.length_eq_finrank.symm
  obtain ⟨p, s, hps, horders⟩ := b.heADCOddMaximal_orders k hP
  apply heADCIsOMaximal_of_volumeOrder_le_add_one hL hP (QuadraticSpace.isIsometric_refl q)
  have hvolA := a.heADCOdd_volumeOrder_split k
  have hvolB := b.heADCOdd_profile_volumeOrder k p s horders
  have hheads := a.heADCOdd_prefixSum_eq_of_head_profile k b hhead p s horders
  rw [hprevious, hlast, hheads] at hvolA
  rcases hps with ⟨hp, hs⟩ | ⟨hp, hs⟩
  · rcases hs with hs | hs <;> omega
  · omega

end BONG.GoodBONG

end Bong
