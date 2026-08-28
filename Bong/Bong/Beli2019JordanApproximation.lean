/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Approximation

/-!
# Beli (2019), Lemma 3.2: approximations inside a Jordan block

The two initial approximations are the determinant of the preceding Jordan
part and its product with a norm generator of the current component.  The
alternating order pattern then propagates each seed two positions at a time.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n N : Nat}

namespace JordanBlockCoordinates

variable {b : GoodBONG q L N}

/-- Orders two positions apart agree while all three indices remain in one
Jordan block. -/
theorem order_add_two_eq (C : JordanBlockCoordinates b)
    (i : Nat) (hstart : C.start ≤ i) (hnext : i + 2 < C.stop) :
    b.order (C.index i (by omega)) =
      b.order (C.index (i + 2) hnext) := by
  have hparity : (i - C.start) % 2 = 0 ∨
      (i - C.start) % 2 = 1 := by
    omega
  rcases hparity with hzero | hone
  · have hnextParity : (i + 2 - C.start) % 2 = 0 := by
      omega
    exact ((C.beli2009Lemma213_i i hstart (by omega)).1 hzero).trans
      ((C.beli2009Lemma213_i (i + 2) (by omega) hnext).1
        hnextParity).symm
  · have hnextParity : (i + 2 - C.start) % 2 = 1 := by
      omega
    exact ((C.beli2009Lemma213_i i hstart (by omega)).2 hone).trans
      ((C.beli2009Lemma213_i (i + 2) (by omega) hnext).2
        hnextParity).symm

end JordanBlockCoordinates

/-- The two starting approximations in Beli (2019), Lemma 3.2.

`leftDet` represents `det F L_(k-1)`.  `normGenerator` represents `A_k`;
the mathematical input establishing the two seed approximations is kept
separate from the formal two-step induction. -/
structure JordanApproximationSeeds
    (b : GoodBONG q L (n + 2)) (C : b.JordanBlockCoordinates) where
  leftDet : Kˣ
  normGenerator : Kˣ
  evenSeed : b.IsPrefixApproximation C.start leftDet
  oddSeed : ∀ _h : C.start + 1 < C.stop,
    b.IsPrefixApproximation (C.start + 1) (normGenerator * leftDet)

namespace JordanApproximationSeeds

variable {b : GoodBONG q L (n + 2)} {C : b.JordanBlockCoordinates}

/-- Every checked Jordan interval has canonical formal seeds: the actual
prefix product at its left endpoint and the first BONG value in the block.
The content of Lemma 3.2 is not their existence but their replacement by
Jordan-determinant and norm-generator representatives with controlled square
classes. -/
noncomputable def canonical
    (b : GoodBONG q L (n + 2)) (C : b.JordanBlockCoordinates) :
    JordanApproximationSeeds b C where
  leftDet := b.prefixProduct C.start
  normGenerator := b.valueUnit C.firstIndex
  evenSeed := b.isPrefixApproximation_prefixProduct C.start
  oddSeed := by
    intro hnext
    have hstart : C.start < n + 2 :=
      C.start_lt_stop.trans_le C.stop_le
    have hprefix := b.toBONG.prefixProduct_succ C.start hstart
    have hvalue : b.valueUnit C.firstIndex =
        b.valueUnit ⟨C.start, hstart⟩ := by
      rfl
    have hproduct :
        b.valueUnit C.firstIndex * b.prefixProduct C.start =
          b.prefixProduct (C.start + 1) := by
      rw [hvalue]
      change b.toBONG.valueUnit ⟨C.start, hstart⟩ *
          b.toBONG.prefixProduct C.start =
        b.toBONG.prefixProduct (C.start + 1)
      rw [hprefix]
      exact mul_comm _ _
    rw [hproduct]
    exact b.isPrefixApproximation_prefixProduct (C.start + 1)

/-- Lemma 3.2(i): the even-parity approximation obtained from the
determinant of the preceding Jordan part. -/
theorem evenApproximation [Beli2006AlphaLaws.{u, v} K]
    (S : JordanApproximationSeeds b C) (k : Nat)
    (hpos : C.start + 2 * k < C.stop) :
    b.IsPrefixApproximation (C.start + 2 * k)
      ((-1 : Kˣ) ^ k * S.leftDet) := by
  induction k with
  | zero =>
      simpa using S.evenSeed
  | succ k ih =>
      have hprev : C.start + 2 * k < C.stop := by
        omega
      have hnext : (C.start + 2 * k) + 2 < n + 2 := by
        have hstop := C.stop_le
        omega
      have houter :
          b.order ⟨C.start + 2 * k, by omega⟩ =
            b.order ⟨(C.start + 2 * k) + 2, hnext⟩ := by
        simpa [JordanBlockCoordinates.index] using
          C.order_add_two_eq (C.start + 2 * k) (by omega) (by omega)
      have hstep :=
        b.isPrefixApproximation_neg_add_two_of_outerOrders_eq_any
          (C.start + 2 * k) ((-1 : Kˣ) ^ k * S.leftDet)
          hnext houter (ih hprev)
      convert hstep using 1
      · omega
      · simp [pow_succ, mul_comm]

/-- Lemma 3.2(ii), before absorbing the alternating sign into the choice of
the two-sided norm generator. -/
theorem oddApproximation [Beli2006AlphaLaws.{u, v} K]
    (S : JordanApproximationSeeds b C) (k : Nat)
    (hpos : C.start + 1 + 2 * k < C.stop) :
    b.IsPrefixApproximation (C.start + 1 + 2 * k)
      ((-1 : Kˣ) ^ k * (S.normGenerator * S.leftDet)) := by
  induction k with
  | zero =>
      simpa using S.oddSeed (by omega)
  | succ k ih =>
      have hprev : C.start + 1 + 2 * k < C.stop := by
        omega
      have hnext : (C.start + 1 + 2 * k) + 2 < n + 2 := by
        have hstop := C.stop_le
        omega
      have houter :
          b.order ⟨C.start + 1 + 2 * k, by omega⟩ =
            b.order ⟨(C.start + 1 + 2 * k) + 2, hnext⟩ := by
        simpa [JordanBlockCoordinates.index] using
          C.order_add_two_eq (C.start + 1 + 2 * k) (by omega) (by omega)
      have hstep :=
        b.isPrefixApproximation_neg_add_two_of_outerOrders_eq_any
          (C.start + 1 + 2 * k)
          ((-1 : Kˣ) ^ k * (S.normGenerator * S.leftDet))
          hnext houter (ih hprev)
      convert hstep using 1
      · omega
      · simp [pow_succ, mul_assoc, mul_comm]

/-- The even-parity half of the common-approximation argument requires only
the determinant seeds; no comparison of norm-generator choices is needed. -/
theorem commonApproximation_even_of_squareEquivalentSeeds
    [Beli2006AlphaLaws.{u, v} K]
    {M : Lattice K V}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {C : a.JordanBlockCoordinates} {D : b.JordanBlockCoordinates}
    (S : JordanApproximationSeeds a C)
    (T : JordanApproximationSeeds b D)
    (hstart : C.start = D.start)
    (hevenSeed : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2)
    (i k : Nat) (hi : i = C.start + 2 * k)
    (hC : i < C.stop) (hD : i < D.stop) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i X ∧ b.IsPrefixApproximation i X := by
  have hiD : i = D.start + 2 * k := by omega
  let X := (-1 : Kˣ) ^ k * S.leftDet
  refine ⟨X, ?_, ?_⟩
  · simpa only [X, ← hi] using S.evenApproximation k (by omega)
  · rcases hevenSeed with ⟨s, hs⟩
    have hT := T.evenApproximation k (by omega)
    have hmul :
        (-1 : Kˣ) ^ k * T.leftDet = X * s ^ 2 := by
      rw [hs]
      simp only [X]
      ac_rfl
    rw [← hiD, hmul] at hT
    exact (b.isPrefixApproximation_mul_square_iff i X s).mp hT

/-- The odd-parity half uses only the square class of the combined
norm-generator and determinant seed. -/
theorem commonApproximation_odd_of_squareEquivalentSeeds
    [Beli2006AlphaLaws.{u, v} K]
    {M : Lattice K V}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {C : a.JordanBlockCoordinates} {D : b.JordanBlockCoordinates}
    (S : JordanApproximationSeeds a C)
    (T : JordanApproximationSeeds b D)
    (hstart : C.start = D.start)
    (hoddSeed : ∃ s : Kˣ,
      T.normGenerator * T.leftDet =
        (S.normGenerator * S.leftDet) * s ^ 2)
    (i k : Nat) (hi : i = C.start + 1 + 2 * k)
    (hC : i < C.stop) (hD : i < D.stop) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i X ∧ b.IsPrefixApproximation i X := by
  have hiD : i = D.start + 1 + 2 * k := by omega
  let X := (-1 : Kˣ) ^ k * (S.normGenerator * S.leftDet)
  refine ⟨X, ?_, ?_⟩
  · simpa only [X, ← hi] using S.oddApproximation k (by omega)
  · rcases hoddSeed with ⟨s, hs⟩
    have hT := T.oddApproximation k (by omega)
    have hmul :
        (-1 : Kˣ) ^ k * (T.normGenerator * T.leftDet) =
          X * s ^ 2 := by
      rw [hs]
      simp only [X]
      ac_rfl
    rw [← hiD, hmul] at hT
    exact (b.isPrefixApproximation_mul_square_iff i X s).mp hT

/-- Two Jordan blocks with the same left boundary and square-equivalent
even and odd seeds admit a common approximation at every coordinate lying
in both blocks.  This is the scalar core of the first paragraph of Beli
(2019), Lemma 5.13(i); the later Section 5 calculation is responsible only
for identifying the relevant blocks and proving the two seed square-class
relations. -/
theorem commonApproximation_of_squareEquivalentSeeds
    [Beli2006AlphaLaws.{u, v} K]
    {M : Lattice K V}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {C : a.JordanBlockCoordinates} {D : b.JordanBlockCoordinates}
    (S : JordanApproximationSeeds a C)
    (T : JordanApproximationSeeds b D)
    (hstart : C.start = D.start)
    (hevenSeed : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2)
    (hoddSeed : ∃ s : Kˣ,
      T.normGenerator * T.leftDet =
        (S.normGenerator * S.leftDet) * s ^ 2)
    (i : Nat) (hleft : C.start ≤ i)
    (hC : i < C.stop) (hD : i < D.stop) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i X ∧ b.IsPrefixApproximation i X := by
  rcases Nat.even_or_odd (i - C.start) with heven | hodd
  · rcases heven with ⟨k, hk⟩
    have hiC : i = C.start + 2 * k := by omega
    have hiD : i = D.start + 2 * k := by omega
    let X := (-1 : Kˣ) ^ k * S.leftDet
    refine ⟨X, ?_, ?_⟩
    · simpa only [X, ← hiC] using S.evenApproximation k (by omega)
    · rcases hevenSeed with ⟨s, hs⟩
      have hT := T.evenApproximation k (by omega)
      have hmul :
          (-1 : Kˣ) ^ k * T.leftDet = X * s ^ 2 := by
        rw [hs]
        simp only [X]
        ac_rfl
      rw [← hiD, hmul] at hT
      exact (b.isPrefixApproximation_mul_square_iff i X s).mp hT
  · rcases hodd with ⟨k, hk⟩
    have hiC : i = C.start + 1 + 2 * k := by omega
    have hiD : i = D.start + 1 + 2 * k := by omega
    let X := (-1 : Kˣ) ^ k * (S.normGenerator * S.leftDet)
    refine ⟨X, ?_, ?_⟩
    · simpa only [X, ← hiC] using S.oddApproximation k (by omega)
    · rcases hoddSeed with ⟨s, hs⟩
      have hT := T.oddApproximation k (by omega)
      have hmul :
          (-1 : Kˣ) ^ k * (T.normGenerator * T.leftDet) =
            X * s ^ 2 := by
        rw [hs]
        simp only [X]
        ac_rfl
      rw [← hiD, hmul] at hT
      exact (b.isPrefixApproximation_mul_square_iff i X s).mp hT

end JordanApproximationSeeds

end BONG.GoodBONG

end Bong
