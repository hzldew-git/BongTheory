/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma315
import Bong.Bong.He2022ClassicLemma43
import Bong.Bong.HeHu2022Proposition35iii

/-!
# He (2024), Lemma 7.10(iii): the two large C witnesses

This file proves the integral-representation upgrade used in the minimality
argument.  For a parameter of defect zero or one, either displayed
`C_j^(n+2)(c)` represents every classic rank-`n` target that its ambient
quadratic space represents.  The later finite-table layer supplies the
ambient-space classification and identifies the single omitted row.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type v} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}

namespace BONG.GoodBONG

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem negOne_double_pow_mul (k : Nat) (c : Kˣ) :
    (-1 : Kˣ) ^ k * ((-1 : Kˣ) ^ k * c) = c := by
  rw [← mul_assoc, ← pow_add]
  rw [(show Even (k + k) from ⟨k, by omega⟩).neg_one_pow]
  simp

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem negOne_double_pow_mul_square (k : Nat) (c s : Kˣ) :
    (-1 : Kˣ) ^ k * ((-1 : Kˣ) ^ k * (s ^ 2 * c)) = c * s ^ 2 := by
  rw [← mul_assoc, ← pow_add]
  rw [(show Even (k + k) from ⟨k, by omega⟩).neg_one_pow]
  simp [mul_comm]

/-- Lemma 7.10(iii), ambient exactness for the first small column.  A
compatible pair in ranks `n` and `n+2` makes the large `C₂` space the
unique codimension-two target which misses the small `C₁` space. -/
theorem he2022ClassicLemma710iii_largeC2_missesExactly_C1
    (pairs : Nat) (c cSharp : Kˣ)
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)) :
    HeHuMissesExactly
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp) := by
  have hfirstLift := heHuTowerModel_succ_hyperbolicLift
    (K := K) pairs (heHuBinaryFirst c)
  have hsecondLift := heHuTowerModel_succ_hyperbolicLift
    (K := K) pairs (heHuBinaryTwist c cSharp)
  exact (heHuUniqueExcludingFirst_of_hyperbolicPairs
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC2 (K := K) pairs c cSharp)
    (heClassicEvenC1 (K := K) (pairs + 1) c)
    (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
    smallPair largePair
    (by
      simpa only [heClassicEvenC1, heClassicScaledHyperbolicTower_zero,
        heHuBinaryFirst] using hfirstLift)
    (by
      simpa only [heClassicEvenC2, heClassicScaledHyperbolicTower_zero,
        heHuBinaryTwist] using hsecondLift)).exactness

/-- Lemma 7.10(iii), ambient exactness for the second small column.  The
large `C₁` space is the unique codimension-two target which misses the
small `C₂` space. -/
theorem he2022ClassicLemma710iii_largeC1_missesExactly_C2
    (pairs : Nat) (c cSharp : Kˣ)
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)) :
    HeHuMissesExactly
      (heClassicEvenC2 (K := K) pairs c cSharp)
      (heClassicEvenC1 (K := K) (pairs + 1) c) := by
  have hfirstLift := heHuTowerModel_succ_hyperbolicLift
    (K := K) pairs (heHuBinaryFirst c)
  have hsecondLift := heHuTowerModel_succ_hyperbolicLift
    (K := K) pairs (heHuBinaryTwist c cSharp)
  exact (heHuUniqueExcludingSecond_of_hyperbolicPairs
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC2 (K := K) pairs c cSharp)
    (heClassicEvenC1 (K := K) (pairs + 1) c)
    (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
    smallPair largePair
    (by
      simpa only [heClassicEvenC1, heClassicScaledHyperbolicTower_zero,
        heHuBinaryFirst] using hfirstLift)
    (by
      simpa only [heClassicEvenC2, heClassicScaledHyperbolicTower_zero,
        heHuBinaryTwist] using hsecondLift)).exactness

/-- Lemma 7.10(iii), first source column: the exact large `C₁` lattice
represents every classic target whose ambient space it represents. -/
theorem he2022ClassicLemma710iii_C1_represents_of_ambient
    (pairs : Nat) (c : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hd : d = 0 ∨ d = 1)
    (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ))
    (b : GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (ambient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c)).Represents r) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c))
      r
      (heHuExactRealization
        (heClassicEvenC1 (K := K) (pairs + 1) c)
        (heClassicEvenC1_adjacentAdmissible (pairs + 1) c hc)
        (heClassicEvenC1_weakTwoStep (pairs + 1) c hc)).lattice
      M := by
  let a := heClassicEvenC1GoodBONG (K := K) (pairs + 1) c hc
  have hAClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c))
      (heHuExactRealization
        (heClassicEvenC1 (K := K) (pairs + 1) c)
        (heClassicEvenC1_adjacentAdmissible (pairs + 1) c hc)
        (heClassicEvenC1_weakTwoStep (pairs + 1) c hc)).lattice :=
    heClassicEvenC1_isClassicIntegral (K := K) (pairs + 1) c hc
  have hRn : a.order ⟨2 * pairs + 1, by omega⟩ = 0 := by
    simp only [a, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [Nat.mul_add, Nat.add_assoc]
  have hRnOne : a.order ⟨2 * pairs + 2, by omega⟩ = 0 := by
    simp only [a, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    simp [Nat.mul_add, Nat.add_assoc]
  have hterminal :
      (a.order ⟨2 * pairs + 3, by omega⟩ = 0 ∧
          a.alphaValue ⟨2 * pairs + 2, by omega⟩ = 1 ∧
          defectOrder (K := K)
            (((-1 : Kˣ) ^ (pairs + 2)) *
              a.prefixProduct (2 * pairs + 4)) = 1) ∨
        a.order ⟨2 * pairs + 3, by omega⟩ = 1 := by
    rcases hd with rfl | rfl
    · right
      simp only [a, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
      rw [heClassicEvenC1_order]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      simp only [if_true]
      simpa using hcOrder
    · left
      have hOrderZero : ordUnit K c = 0 := by
        simpa using hcOrder
      refine ⟨?_, ?_, ?_⟩
      · simp only [a, heClassicEvenC1GoodBONG,
          heHuExactGoodBONG_order]
        rw [heClassicEvenC1_order]
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        simp only [if_true]
        simpa using hOrderZero
      · have hAll := heClassicEvenC1_alpha_eq_one
          (K := K) (pairs + 1) c 1 hc (Or.inr rfl)
          hOrderZero (by simpa using hcDefect)
        exact hAll ⟨2 * pairs + 2, by omega⟩
      · have hPrefix := heClassicEvenC1_prefixProduct_full
          (K := K) (pairs + 1) c hc
        change a.prefixProduct (2 * pairs + 4) =
          (-1 : Kˣ) ^ (pairs + 2) * c at hPrefix
        rw [hPrefix, negOne_double_pow_mul, hcDefect]
        norm_num
  exact a.he2022ClassicLemma315i pairs b hAClassic hBClassic
    hRn hRnOne hterminal ambient

/-- Lemma 7.10(iii), second source column.  The sharp parameter contributes
only a square to the signed full determinant, so the same defect split
applies. -/
theorem he2022ClassicLemma710iii_C2_represents_of_ambient
    (pairs : Nat) (c cSharp : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ))
    (b : GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (ambient :
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)).Represents r) :
    Lattice.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
      r
      (heHuExactRealization
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
        (heClassicEvenC2_adjacentAdmissible
          (pairs + 1) c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep
          (pairs + 1) c cSharp hc hcSharp)).lattice
      M := by
  let a := heClassicEvenC2GoodBONG
    (K := K) (pairs + 1) c cSharp hc hcSharp
  have hAClassic : Lattice.IsClassicIntegral
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
      (heHuExactRealization
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
        (heClassicEvenC2_adjacentAdmissible
          (pairs + 1) c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep
          (pairs + 1) c cSharp hc hcSharp)).lattice :=
    heClassicEvenC2_isClassicIntegral
      (K := K) (pairs + 1) c cSharp hc hcSharp
  have hRn : a.order ⟨2 * pairs + 1, by omega⟩ = 0 := by
    simp only [a, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order (pairs + 1) c cSharp hcSharp]
    simp [Nat.mul_add, Nat.add_assoc]
  have hRnOne : a.order ⟨2 * pairs + 2, by omega⟩ = 0 := by
    simp only [a, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order (pairs + 1) c cSharp hcSharp]
    simp [Nat.mul_add, Nat.add_assoc]
  have hterminal :
      (a.order ⟨2 * pairs + 3, by omega⟩ = 0 ∧
          a.alphaValue ⟨2 * pairs + 2, by omega⟩ = 1 ∧
          defectOrder (K := K)
            (((-1 : Kˣ) ^ (pairs + 2)) *
              a.prefixProduct (2 * pairs + 4)) = 1) ∨
        a.order ⟨2 * pairs + 3, by omega⟩ = 1 := by
    rcases hd with rfl | rfl
    · right
      simp only [a, heClassicEvenC2GoodBONG,
        heHuExactGoodBONG_order]
      rw [heClassicEvenC2_order (pairs + 1) c cSharp hcSharp]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      simp only [if_true]
      simpa using hcOrder
    · left
      have hOrderZero : ordUnit K c = 0 := by
        simpa using hcOrder
      refine ⟨?_, ?_, ?_⟩
      · simp only [a, heClassicEvenC2GoodBONG,
          heHuExactGoodBONG_order]
        rw [heClassicEvenC2_order (pairs + 1) c cSharp hcSharp]
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        simp only [if_true]
        simpa using hOrderZero
      · have hAll := heClassicEvenC2_alpha_eq_one
          (K := K) (pairs + 1) c cSharp 1 hc hcSharp
          (Or.inr rfl) hOrderZero (by simpa using hcDefect)
        exact hAll ⟨2 * pairs + 2, by omega⟩
      · have hPrefix := heClassicEvenC2_prefixProduct_full
          (K := K) (pairs + 1) c cSharp hc hcSharp
        change a.prefixProduct (2 * pairs + 4) =
          (-1 : Kˣ) ^ (pairs + 2) * (cSharp ^ 2 * c) at hPrefix
        rw [hPrefix, negOne_double_pow_mul_square,
          defectOrder_mul_square, hcDefect]
        norm_num
  exact a.he2022ClassicLemma315i pairs b hAClassic hBClassic
    hRn hRnOne hterminal ambient

/-- The large first-column exact lattice misses the small second-column
exact lattice.  This is stronger than ambient nonrepresentation because an
integral representation would induce the forbidden ambient one. -/
theorem he2022ClassicLemma710iii_largeC1_misses_C2
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)) :
    ¬ Lattice.Represents
      (coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c))
      (coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (heHuExactRealization
        (heClassicEvenC1 (K := K) (pairs + 1) c)
        (heClassicEvenC1_adjacentAdmissible (pairs + 1) c hc)
        (heClassicEvenC1_weakTwoStep (pairs + 1) c hc)).lattice
      (heHuExactRealization
        (heClassicEvenC2 (K := K) pairs c cSharp)
        (heClassicEvenC2_adjacentAdmissible pairs c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep pairs c cSharp hc hcSharp)).lattice := by
  intro hrep
  apply (he2022ClassicLemma710iii_largeC1_missesExactly_C2
    pairs c cSharp smallPair largePair).misses
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (heClassicEvenC2 (K := K) pairs c cSharp)
    (heClassicEvenC1 (K := K) (pairs + 1) c)).mp hrep.ambient

/-- The large second-column exact lattice misses the small first-column
exact lattice. -/
theorem he2022ClassicLemma710iii_largeC2_misses_C1
    (pairs : Nat) (c cSharp : Kˣ)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)) :
    ¬ Lattice.Represents
      (coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
      (coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs c))
      (heHuExactRealization
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
        (heClassicEvenC2_adjacentAdmissible
          (pairs + 1) c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep
          (pairs + 1) c cSharp hc hcSharp)).lattice
      (heHuExactRealization
        (heClassicEvenC1 (K := K) pairs c)
        (heClassicEvenC1_adjacentAdmissible pairs c hc)
        (heClassicEvenC1_weakTwoStep pairs c hc)).lattice := by
  intro hrep
  apply (he2022ClassicLemma710iii_largeC2_missesExactly_C1
    pairs c cSharp smallPair largePair).misses
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    (heClassicEvenC1 (K := K) pairs c)
    (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)).mp hrep.ambient

/-- The large first-column lattice represents every classic rank-`n`
target outside the ambient isometry class of the small second-column row.
This is the integral half of the deletion witness in Lemma 7.10(iii). -/
theorem he2022ClassicLemma710iii_largeC1_represents_other
    (pairs : Nat) (c cSharp : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hd : d = 0 ∨ d = 1)
    (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ))
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
    (b : GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs c cSharp))) :
    Lattice.Represents
      (coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c))
      r
      (heHuExactRealization
        (heClassicEvenC1 (K := K) (pairs + 1) c)
        (heClassicEvenC1_adjacentAdmissible (pairs + 1) c hc)
        (heClassicEvenC1_weakTwoStep (pairs + 1) c hc)).lattice
      M := by
  have hdiag := (he2022ClassicLemma710iii_largeC1_missesExactly_C2
    pairs c cSharp smallPair largePair).represents_other b.valueUnit hother
  have hspace :
      (coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c)).Represents
        (coefficientDiagonalSpace b.valueUnit) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      b.valueUnit (heClassicEvenC1 (K := K) (pairs + 1) c)).2 hdiag
  have hambient :
      (coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) (pairs + 1) c)).Represents r :=
    hspace.trans ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  exact he2022ClassicLemma710iii_C1_represents_of_ambient
    pairs c d hc hd hcOrder hcDefect b hBClassic hambient

/-- The large second-column lattice represents every classic rank-`n`
target outside the ambient isometry class of the small first-column row.
Together with ambient exactness, this supplies the other deletion witness
in Lemma 7.10(iii). -/
theorem he2022ClassicLemma710iii_largeC2_represents_other
    (pairs : Nat) (c cSharp : Kˣ) (d : Int)
    (hc : 0 ≤ ordUnit K c) (hcSharp : ordUnit K cSharp = 0)
    (hd : d = 0 ∨ d = 1) (hcOrder : ordUnit K c = 1 - d)
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ))
    (smallPair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c cSharp))
    (largePair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) (pairs + 1) c)
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
    (b : GoodBONG r M (2 * pairs + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hother : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (heClassicEvenC1 (K := K) pairs c))) :
    Lattice.Represents
      (coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp))
      r
      (heHuExactRealization
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)
        (heClassicEvenC2_adjacentAdmissible
          (pairs + 1) c cSharp hc hcSharp)
        (heClassicEvenC2_weakTwoStep
          (pairs + 1) c cSharp hc hcSharp)).lattice
      M := by
  have hdiag := (he2022ClassicLemma710iii_largeC2_missesExactly_C1
    pairs c cSharp smallPair largePair).represents_other b.valueUnit hother
  have hspace :
      (coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)).Represents
        (coefficientDiagonalSpace b.valueUnit) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      b.valueUnit
      (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)).2 hdiag
  have hambient :
      (coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) (pairs + 1) c cSharp)).Represents r :=
    hspace.trans ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  exact he2022ClassicLemma710iii_C2_represents_of_ambient
    pairs c cSharp d hc hcSharp hd hcOrder hcDefect b hBClassic hambient

end BONG.GoodBONG

end Bong
