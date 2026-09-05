/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenFirstTests

/-!
# The first-column defect assertion in He (2025), Lemma 6.4(i)

The unconditional order statement includes equal source and target rank.
The positive next-order assertion is quantified only when that index exists;
no extra rank hypothesis is imposed on the unconditional statement.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG
open scoped Classical

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A square product identifies the two relative quadratic defects. -/
theorem heADCQuadraticDefect_eq_of_squareProduct (x y : Kˣ)
    (h : IsSquare (x * y)) : quadraticDefect K x = quadraticDefect K y := by
  obtain ⟨s, hs⟩ := h
  have hfactor : x = y⁻¹ * s ^ 2 := by
    rw [pow_two, ← hs]
    simp [mul_assoc, mul_comm]
  rw [hfactor, quadraticDefect_mul_square, quadraticDefect_inv]

/-- The two first-column parameters have precisely the two defects printed
in Lemma 6.4(i). -/
theorem heADCEvenFirstTest_parameterDefect (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit) :
    quadraticDefect K c =
      if c = 1 then ⊤ else ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  classical
  rcases hc with hOne | hDelta
  · subst c
    rw [if_pos (rfl : (1 : Kˣ) = 1)]
    exact quadraticDefect_eq_top_of_isSquare (K := K) ⟨1, by simp⟩
  · have hdefect : quadraticDefect K c = (2 * ramificationIndex K : Nat) := by
      rw [hDelta]
      exact (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect
    have hne : c ≠ 1 := by
      intro hOne
      have htop : quadraticDefect K c = ⊤ :=
        quadraticDefect_eq_top_of_isSquare (K := K) (by simp [hOne])
      exact ENat.coe_ne_top _ (hdefect.symm.trans htop)
    simpa only [if_neg hne] using hdefect

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A represented first-column test forces the entire alternating prefix,
including when source and target have equal rank. -/
theorem heADCEvenFirstTest_alternatingOrders {m : Nat} (a : GoodBONG q L (m + 2))
    (k : Nat) (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hL : Lattice.IsIntegral q L)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
      L (heADCN1Even k c).lattice) :
    ∃ hrank : 2 * k ≤ m, ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)) := by
  letI : Module.Finite K V := L.moduleFinite
  have hrank : 2 * k ≤ m := by
    obtain ⟨f⟩ := hrep
    have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
    rw [finrank_fin_fun, ← a.toBONG.length_eq_finrank] at hle
    omega
  let b := heADCMaximalGoodBONG (heADCW1Even k c)
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  have hprev : b.order ⟨2 * k, by omega⟩ = 0 := by
    simpa [b, heven] using heADCEvenFirstTest_orders (K := K) k c hc ⟨2 * k, by omega⟩
  have hlast : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    simpa [b, Nat.not_even_iff_odd.mpr hodd] using
      heADCEvenFirstTest_orders (K := K) k c hc ⟨2 * k + 1, by omega⟩
  have C := a.heADCAlternatingPrefix_of_represented_endpoint b hrank hL hrep
    ⟨2 * k + 1, by omega⟩ hodd (by simpa using hprev) hlast
  refine ⟨hrank, ?_⟩
  intro i
  rcases Nat.even_or_odd i.val with hi | hi
  · have hnext : i.val + 1 ≤ 2 * k + 1 := by obtain ⟨z, hz⟩ := hi; omega
    have h := C.pairOrdersAndDefects ⟨i.val + 1, by omega⟩ (by simpa using hnext)
      (Even.add_one hi)
    simpa only [Nat.add_sub_cancel, if_pos hi] using h.1
  · have h := C.pairOrdersAndDefects ⟨i.val, by omega⟩ (by simp; omega) hi
    simpa only [if_neg (Nat.not_even_iff_odd.mpr hi)] using h.2.1

/-- A positive next order identifies the signed source determinant prefix
with the parameter of the represented first-column test, at the level of
the actual relative quadratic defect. -/
theorem heADCEvenFirstTest_signedPrefixDefect {m : Nat} (a : GoodBONG q L (m + 2))
    (k : Nat) (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
      L (heADCN1Even k c).lattice)
    (hrank : 2 * k < m) (hpos : 0 < a.order ⟨2 * k + 2, by omega⟩) :
    quadraticDefect K ((-1 : Kˣ) ^ (k + 1) * a.prefixProduct (2 * k + 2)) =
      quadraticDefect K c := by
  let b := heADCMaximalGoodBONG (heADCW1Even k c)
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  have hlast : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    simpa [b, Nat.not_even_iff_odd.mpr hodd] using
      heADCEvenFirstTest_orders (K := K) k c hc ⟨2 * k + 1, by omega⟩
  have hcompare := a.heADCComparisonPrefix_isSquare_of_strict_crossGap b hrank hrep
    (by rw [hlast]; simpa using hpos)
  have hdet := heADCMaximalGoodBONG_prefixProduct_det_square (heADCW1Even k c)
  have h := isSquare_mul_trans _ (b.prefixProduct (2 * k + 2)) _ hcompare hdet
  rw [diagonalUnitDeterminant_heHuEvenFirst] at h
  apply heADCQuadraticDefect_eq_of_squareProduct
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- He (2025), Lemma 6.4(i), with both named first-column tests and both
exact defect values. The next-order implication is restricted only by the
existence of its index; the order assertion also applies in equal rank. -/
theorem heADC2025Lemma64i {m : Nat} (a : GoodBONG q L (m + 2)) (k : Nat) (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hL : Lattice.IsIntegral q L)
    (hrep : Lattice.Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
      L (heADCN1Even k c).lattice) :
    ∃ hrank : 2 * k ≤ m,
      (∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
        if Even i.val then 0 else -(2 * (ramificationIndex K : Int))) ∧
      (∀ hnext : 2 * k < m, 0 < a.order ⟨2 * k + 2, by omega⟩ →
        quadraticDefect K ((-1 : Kˣ) ^ (k + 1) * a.prefixProduct (2 * k + 2)) =
          if c = 1 then ⊤ else ((2 * ramificationIndex K : Nat) : ℕ∞)) := by
  obtain ⟨hrank, horders⟩ := a.heADCEvenFirstTest_alternatingOrders k c hc hL hrep
  refine ⟨hrank, horders, ?_⟩
  intro hnext hpos
  exact (a.heADCEvenFirstTest_signedPrefixDefect k c hc hrep hnext hpos).trans
    (heADCEvenFirstTest_parameterDefect c hc)

end BONG.GoodBONG

end Bong
