/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenFirstTests

/-!
# The second-column tests in He (2025), Lemma 6.4(iii)

The discriminant test includes rank two. The square second-column test
is admitted only in the ranks where Definition 4.1 defines that space.
Both targets are actual maximal lattices, with their profiles proved.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The displayed quaternary tail is one alternating pair followed by
the raised binary endpoint. -/
theorem heADCMaximalOrderProfile_raisedFour (k : Nat) (i : Fin (4 + 2 * k)) :
    heADCMaximalOrderProfile (K := K) k
      ![0, -(2 * (ramificationIndex K : Int)), 1,
        1 - 2 * (ramificationIndex K : Int)] i =
      heADCMaximalOrderProfile (K := K) (k + 1)
        ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩ := by
  by_cases hi : i.val < 2 * k
  · simp [heADCMaximalOrderProfile, hi, show i.val < 2 * (k + 1) by omega]
  · have hcases : i.val = 2 * k ∨ i.val = 2 * k + 1 ∨
        i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 := by omega
    have heven : Even (2 * k) := ⟨k, by omega⟩
    have hodd : ¬ Even (2 * k + 1) := by rintro ⟨z, hz⟩; omega
    rcases hcases with h | h | h | h
    · simp [heADCMaximalOrderProfile, h, heven, show 2 * k < 2 * (k + 1) by omega]
    · simp [heADCMaximalOrderProfile, h, hodd, show ¬ 2 * k + 1 < 2 * k by omega,
        show 2 * k + 1 < 2 * (k + 1) by omega, show 2 * k + 1 - 2 * k = 1 by omega]
    · simp [heADCMaximalOrderProfile, h, show ¬ 2 * k + 2 < 2 * k by omega,
        show ¬ 2 * k + 2 < 2 * (k + 1) by omega,
        show 2 * k + 2 - 2 * k = 2 by omega,
        show 2 * k + 2 - 2 * (k + 1) = 0 by omega]
    · simp [heADCMaximalOrderProfile, h, show ¬ 2 * k + 3 < 2 * k by omega,
        show ¬ 2 * k + 3 < 2 * (k + 1) by omega,
        show 2 * k + 3 - 2 * k = 3 by omega,
        show 2 * k + 3 - 2 * (k + 1) = 1 by omega]

/-- The actual second-column tests at 1 and Delta have the raised binary
endpoint profile. Their rank restrictions come from the named-space domain. -/
theorem heADCEvenSecondTest_orders (k : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined k c)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (i : Fin (2 * k + 2)) :
    (heADCMaximalGoodBONG (heADCW2Even k c hdefined)).order i =
      heADCMaximalOrderProfile (K := K) k
        ![1, 1 - 2 * (ramificationIndex K : Int)] ⟨i.val, by omega⟩ := by
  rcases hc with hOne | hDelta
  · subst c
    cases k with
    | zero =>
        rcases hdefined with hpos | hnonsquare
        · omega
        · exact False.elim (hnonsquare ⟨1, by simp⟩)
    | succ k =>
        let b := (heADCMaximalGoodBONG (heADCW2Even (k + 1) (1 : Kˣ) hdefined)).castLength
          (by omega : 2 * (k + 1) + 2 = 4 + 2 * k)
        have hprofile := (heADC2025Lemma411iiOnePublished k b
          (heHuOMaximalLattice_isOMaximal _).isIntegral
          (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
        have h := hprofile ⟨i.val, by omega⟩
        rw [heADCMaximalOrderProfile_raisedFour] at h
        simpa only [b, order_castLength] using h
  · subst c
    let b := (heADCMaximalGoodBONG (heADCW2Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      hdefined)).castLength (by omega : 2 * k + 2 = 2 + 2 * k)
    have hprofile := (heADC2025Lemma411iiDeltaPublished k b
      (heHuOMaximalLattice_isOMaximal _).isIntegral
      (QuadraticSpace.isIsometric_refl _)).mp (Lattice.isIsometric_refl _ _)
    simpa only [b, order_castLength] using hprofile ⟨i.val, by omega⟩

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He (2025), Lemma 6.4(iii), on the two named second-column tests.
The short discriminant branch has an empty alternating head, not a
nonexistent penultimate head pair. -/
theorem heADC2025Lemma64iii {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined k c)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hL : Lattice.IsIntegral q L)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k c hdefined))
      L (heADCN2Even k c hdefined).lattice) :
    ∃ hrank : 2 * k ≤ m,
      (∀ i : Fin (2 * k), a.order ⟨i.val, by omega⟩ =
        if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
      ((a.order ⟨2 * k, by omega⟩ = 0 ∧
        (a.order ⟨2 * k + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) ∨
          a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))) ∨
        (a.order ⟨2 * k, by omega⟩ = 1 ∧
          a.order ⟨2 * k + 1, by omega⟩ = 1 - 2 * (ramificationIndex K : Int))) := by
  letI : Module.Finite K V := L.moduleFinite
  have hrank : 2 * k ≤ m := by
    obtain ⟨f⟩ := hrep
    have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
    rw [finrank_fin_fun, ← a.toBONG.length_eq_finrank] at hle
    omega
  let b := heADCMaximalGoodBONG (heADCW2Even k c hdefined)
  have B := heADCEvenSecondTest_orders (K := K) k c hdefined hc
  have hprev : b.order ⟨2 * k, by omega⟩ = 1 := by
    simpa [b, heADCMaximalOrderProfile] using B ⟨2 * k, by omega⟩
  have hlast : b.order ⟨2 * k + 1, by omega⟩ =
      1 - 2 * (ramificationIndex K : Int) := by
    simpa [b, heADCMaximalOrderProfile, show ¬ 2 * k + 1 < 2 * k by omega,
      show 2 * k + 1 - 2 * k = 1 by omega] using B ⟨2 * k + 1, by omega⟩
  have C := (a.heADC2025Theorem36 (by omega) hrep.ambient b).mp hrep
  have O := (a.representationOrderCondition_iff b (by omega)).mp C.orderCondition
  have hpair := O.pairSum_le (2 * k) (by omega)
  have hpair' : a.order ⟨2 * k, by omega⟩ + a.order ⟨2 * k + 1, by omega⟩ ≤
      2 - 2 * (ramificationIndex K : Int) := by
    simp only [orderSequence_at, hprev, hlast] at hpair
    omega
  let j : Fin (m + 1) := ⟨2 * k, by omega⟩
  have hgap := a.orderGap_ge_neg_two_mul_e j
  change -(2 * (ramificationIndex K : Int)) ≤
    a.order ⟨2 * k + 1, by omega⟩ - a.order ⟨2 * k, by omega⟩ at hgap
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have hnonneg := ((a.heHu2022Proposition27i hL).oddIndexed
    ⟨2 * k, by omega⟩ ⟨2 * k, by omega⟩ le_rfl heven heven).1
  refine ⟨hrank, ?_, ?_⟩
  · intro i
    have hk : 0 < k := by have := i.isLt; omega
    have hheadOdd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    have hheadEven : Even (2 * k - 2) := ⟨k - 1, by omega⟩
    have hheadPrev : b.order ⟨2 * k - 2, by omega⟩ = 0 := by
      simpa [b, heADCMaximalOrderProfile, show 2 * k - 2 < 2 * k by omega,
        hheadEven] using B ⟨2 * k - 2, by omega⟩
    have hheadLast : b.order ⟨2 * k - 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      simpa [b, heADCMaximalOrderProfile, show 2 * k - 1 < 2 * k by omega,
        Nat.not_even_iff_odd.mpr hheadOdd] using B ⟨2 * k - 1, by omega⟩
    have P := a.heADCAlternatingPrefix_of_represented_endpoint b hrank hL hrep
      ⟨2 * k - 1, by omega⟩ hheadOdd (by simpa only [Nat.sub_sub] using hheadPrev)
      hheadLast
    rcases Nat.even_or_odd i.val with hi | hi
    · have hnext : i.val + 1 ≤ 2 * k - 1 := by obtain ⟨z, hz⟩ := hi; omega
      have h := P.pairOrdersAndDefects ⟨i.val + 1, by omega⟩ (by simpa using hnext)
        (Even.add_one hi)
      simpa only [Nat.add_sub_cancel, if_pos hi] using h.1
    · have h := P.pairOrdersAndDefects ⟨i.val, by omega⟩ (by simp; omega) hi
      simpa only [if_neg (Nat.not_even_iff_odd.mpr hi)] using h.2.1
  · have hcases : a.order ⟨2 * k, by omega⟩ = 0 ∨ a.order ⟨2 * k, by omega⟩ = 1 := by
      omega
    rcases hcases with hzero | hone
    · left
      refine ⟨hzero, ?_⟩
      have he := ramificationIndex_pos (K := K)
      by_contra hnot
      have hlastValue : a.order ⟨2 * k + 1, by omega⟩ =
          1 - 2 * (ramificationIndex K : Int) := by omega
      have hodd : Odd (a.orderGap j) := by
        change Odd (a.order ⟨2 * k + 1, by omega⟩ - a.order ⟨2 * k, by omega⟩)
        rw [hlastValue, hzero]
        exact ⟨-(ramificationIndex K : Int), by ring⟩
      have hpositive := a.heADC2025Corollary32i j hodd
      change 0 < a.order ⟨2 * k + 1, by omega⟩ - a.order ⟨2 * k, by omega⟩ at hpositive
      omega
    · exact Or.inr ⟨hone, by omega⟩

end BONG.GoodBONG

end Bong
