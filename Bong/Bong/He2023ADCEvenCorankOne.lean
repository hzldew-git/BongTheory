/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCCorankOneVolume
import Bong.Bong.He2023ADCCorankOneAmbient

/-!
# He (2025), Theorem 6.1

For even n at least two, a dyadic integral lattice of rank n+1 is n-ADC
if and only if it is norm-maximal. All tests, ambient rows and maximal
profiles used in the necessity direction are proved for the actual lattices.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The raised-tail branch of Theorem 6.1 has the same volume as its
actual second-column unit maximal representative. -/
theorem heADCCorankOne_raisedTail_isOMaximal (k : Nat)
    (a : GoodBONG q L (2 * k + 3)) (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (hhead : ∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hprevious : a.order ⟨2 * k, by omega⟩ = 0)
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))
    (hnext : a.order ⟨2 * k + 2, by omega⟩ ≤ 1) : Lattice.IsOMaximal q L := by
  obtain ⟨δ, hδ, hspace⟩ := a.heADCCorankOne_raisedTail_ambient k hADC hlast
  let w := heADCW2Odd k δ
  let b := heADCMaximalGoodBONG w
  have hM := heHuOMaximalLattice_isOMaximal w
  have horders : ∀ i, b.order i = heADCMaximalOrderProfile (K := K) k
      ![0, 2 - 2 * (ramificationIndex K : Int), 0] ⟨i.val, by omega⟩ := by
    have H := (heADC2025Lemma412iiPublished δ hδ k (b.castLength (by omega)) hM.isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
    intro i
    simpa only [order_castLength] using H ⟨i.val, by omega⟩
  apply heADCIsOMaximal_of_volumeOrder_le_add_one hADC.isIntegral hM hspace
  have hvolA := a.heADCOdd_volumeOrder_split k
  have hvolB := b.heADCOdd_profile_volumeOrder k _ _ horders
  have hheads := a.heADCOdd_prefixSum_eq_of_head_profile k b hhead _ _ horders
  rw [hprevious, hlast, hheads] at hvolA
  omega

/-- Theorem 6.1 for a supplied good BONG; its order profile is derived
from the n-ADC predicate, not assumed. -/
theorem heADC2025Theorem61_of_goodBONG (k : Nat) (a : GoodBONG q L (2 * k + 3)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 2) ↔ Lattice.IsOMaximal q L := by
  constructor
  · intro hADC
    obtain ⟨hhead, hprevious, hlast, hnext⟩ := a.heADCEvenCorankOne_orders k hADC
    rcases hlast with hstandard | hraised
    · exact a.heADCCorankOne_standardTail_isOMaximal k hADC.isIntegral hhead hprevious
        hstandard (by omega)
    · exact a.heADCCorankOne_raisedTail_isOMaximal k hADC hhead hprevious hraised (by omega)
  · exact fun h ↦ h.isNADC _

end BONG.GoodBONG

namespace Lattice

/-- He (2025), Theorem 6.1: for even n at least two and rank n+1,
dyadic n-ADC lattices are exactly the norm-maximal lattices. -/
theorem heADC2025Theorem61 (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat)
    (hn : 2 ≤ n) (heven : Even n) (hrank : finrank K V = n + 1) :
    IsNADC.{u, u, u} q L n ↔ IsOMaximal q L := by
  obtain ⟨k, hk⟩ := heven
  let p := k - 1
  have hnval : n = 2 * p + 2 := by dsimp only [p]; omega
  let a : BONG.GoodBONG q L (2 * p + 3) :=
    (BONG.GoodBONG.ofLattice q L).castLength (by omega)
  simpa only [hnval] using a.heADC2025Theorem61_of_goodBONG p

end Lattice

end Bong
