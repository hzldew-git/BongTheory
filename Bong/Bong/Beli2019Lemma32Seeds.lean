/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019JordanApproximation

/-!
# Beli (2019), Lemma 3.2: the two Jordan-boundary seeds

This file isolates exactly the cited local inputs in the two base cases of
Lemma 3.2.  The even seed uses O'Meara 93:28(i), namely determinant
congruence modulo the fundamental ideal.  The odd seed uses Beli (2009),
Lemma 2.13(iii) and Corollary 2.17(i), namely congruence of two norm
generators at the normalized weight depth.

All conversions from ideal congruence to relative quadratic defect are proved
here from the concrete valuation definition.  Thus the remaining source
obligations are precisely the two lattice-theoretic congruences, not an
opaque approximation assertion.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The precise determinant input used at the even boundary of Lemma 3.2.
At the empty boundary the determinant is one.  At an internal boundary,
O'Meara 93:28(i) supplies the displayed congruence, while Beli (2009),
Lemma 2.16(ii), supplies the comparison between the fundamental-ideal order
and the prefix alpha cap. -/
structure Omeara9328DeterminantSeedData
    (b : GoodBONG q L (n + 2)) (C : b.JordanBlockCoordinates) where
  leftDet : Kˣ
  boundary :
    (C.start = 0 ∧ leftDet = 1) ∨
      ∃ fundamental : Lattice.OrderedFractionalIdeal K,
        0 ≤ fundamental.order ∧
        ordUnit K (b.prefixProduct C.start) = ordUnit K leftDet ∧
        UnitsCongruentModulo (b.prefixProduct C.start) leftDet
          fundamental.carrier ∧
        b.prefixAlphaCap C.start ≤
          (((fundamental.order : Int) : ℚ) : WithTop ℚ)

namespace Omeara9328DeterminantSeedData

variable {b : GoodBONG q L (n + 2)} {C : b.JordanBlockCoordinates}

/-- O'Meara 93:28(i), after the scalar congruence-to-defect conversion,
gives the even seed of Beli (2019), Lemma 3.2. -/
theorem evenSeed (D : Omeara9328DeterminantSeedData b C) :
    b.IsPrefixApproximation C.start D.leftDet := by
  rcases D.boundary with ⟨hstart, hdet⟩ |
      ⟨fundamental, hnonnegative, horder, hcongruent, hcap⟩
  · rw [hstart, hdet]
    simpa only [GoodBONG.prefixProduct, BONG.prefixProduct_zero] using
      b.isPrefixApproximation_prefixProduct 0
  · have hcongruentPower : UnitsCongruentModulo
        (b.prefixProduct C.start) D.leftDet
        (Lattice.powerIdeal (K := K) fundamental.order) := by
      rw [← fundamental.carrier_eq_powerIdeal]
      exact hcongruent
    have hdefect :=
      intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
        (b.prefixProduct C.start) D.leftDet fundamental.order
        hnonnegative horder hcongruentPower
    unfold IsPrefixApproximation
    exact hcap.trans (by simpa only [mul_comm] using hdefect)

end Omeara9328DeterminantSeedData

/-- The precise norm-generator input used at the odd boundary of Lemma 3.2.
The normalized weight depth is integral by Corollary 2.17(i), and Lemma
2.13(iii) identifies the first BONG value as a norm generator of the same
scale layer. -/
structure Beli2009NormGeneratorSeedData
    (b : GoodBONG q L (n + 2)) (C : b.JordanBlockCoordinates)
    (normGenerator : Kˣ) (hnext : C.start + 1 < C.stop) where
  depth : Int
  depth_nonnegative : 0 ≤ depth
  depth_eq_alpha :
    (depth : ℚ) = b.alphaValue ⟨C.start, by
      have hstop := C.stop_le
      omega⟩
  same_order :
    ordUnit K (b.valueUnit C.firstIndex) = ordUnit K normGenerator
  congruent : UnitsCongruentModulo (b.valueUnit C.firstIndex) normGenerator
    (Lattice.powerIdeal (K := K) depth)
  firstStep_descending :
    b.order (C.index (C.start + 1) hnext) ≤ b.order C.firstIndex

namespace Beli2009NormGeneratorSeedData

variable {b : GoodBONG q L (n + 2)} {C : b.JordanBlockCoordinates}
  {normGenerator : Kˣ} {hnext : C.start + 1 < C.stop}

/-- The even-boundary determinant approximation is already deep enough for
the next alpha when the first two orders in the Jordan block descend.  This
is the `P1` inequality used on lines 1560--1562 of Beli (2019 v2). -/
theorem currentAlpha_le_evenSeedDefect
    [Beli2006AlphaLaws.{u, v} K]
    (D : Beli2009NormGeneratorSeedData b C normGenerator hnext)
    (leftDet : Kˣ) (heven : b.IsPrefixApproximation C.start leftDet) :
    (b.alphaValue ⟨C.start, by
        have hstop := C.stop_le
        omega⟩ : WithTop ℚ) ≤
      defectOrder (K := K) (leftDet * b.prefixProduct C.start) := by
  unfold IsPrefixApproximation at heven
  by_cases hzero : C.start = 0
  · rw [hzero] at heven
    rw [b.prefixAlphaCap_zero] at heven
    have hbound : (b.alphaValue ⟨0, by omega⟩ : WithTop ℚ) ≤
        defectOrder (K := K) (leftDet * b.prefixProduct 0) :=
      le_top.trans heven
    simpa only [hzero] using hbound
  · have hstartPos : 0 < C.start := Nat.pos_of_ne_zero hzero
    have hstartBound : C.start < n + 1 := by
      have hstop := C.stop_le
      omega
    let previous : Fin (n + 1) := ⟨C.start - 1, by omega⟩
    let current : Fin (n + 1) := ⟨C.start, hstartBound⟩
    have hpreviousNext : previous.val + 1 < n + 1 := by
      dsimp only [previous]
      omega
    have hp1 := (b.alpha_p1 previous hpreviousNext).2
    have hcurrentIndex :
        (⟨previous.val + 1, hpreviousNext⟩ : Fin (n + 1)) = current := by
      apply Fin.ext
      dsimp only [previous, current]
      omega
    rw [hcurrentIndex] at hp1
    have hcurrentSucc :
        current.succ = C.index (C.start + 1) hnext := by
      apply Fin.ext
      rfl
    have hpreviousSucc : previous.succ = C.firstIndex := by
      apply Fin.ext
      change C.start - 1 + 1 = C.start
      omega
    have hdescending :
        b.order current.succ ≤ b.order previous.succ := by
      rw [hcurrentSucc, hpreviousSucc]
      exact D.firstStep_descending
    have hdescendingQ :
        (b.order current.succ : ℚ) ≤ (b.order previous.succ : ℚ) := by
      exact_mod_cast hdescending
    have halpha : b.alphaValue current ≤ b.alphaValue previous := by
      unfold alphaRightEndpoint at hp1
      push_cast at hp1
      linarith
    rw [b.prefixAlphaCap_of_internal hstartPos (by omega)] at heven
    have halphaTop : (b.alphaValue current : WithTop ℚ) ≤
        (b.alphaValue previous : WithTop ℚ) := by
      exact_mod_cast halpha
    change (b.alphaValue current : WithTop ℚ) ≤
      defectOrder (K := K) (leftDet * b.prefixProduct C.start)
    exact halphaTop.trans (by simpa only [previous] using heven)

/-- Beli (2009), Lemma 2.13(iii) and Corollary 2.17(i), after the concrete
congruence-to-defect conversion, give the norm-generator factor at the odd
seed. -/
theorem alpha_le_normGeneratorProductDefect
    (D : Beli2009NormGeneratorSeedData b C normGenerator hnext) :
    (b.alphaValue ⟨C.start, by
        have hstop := C.stop_le
        omega⟩ : WithTop ℚ) ≤
      defectOrder (K := K)
        (normGenerator * b.valueUnit C.firstIndex) := by
  have hdefect :=
    intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
      (b.valueUnit C.firstIndex) normGenerator D.depth
      D.depth_nonnegative D.same_order D.congruent
  rw [D.depth_eq_alpha] at hdefect
  simpa only [mul_comm] using hdefect

/-- The two base estimates combine by the quadratic-defect domination
principle to give the odd seed of Lemma 3.2. -/
theorem oddSeed
    [Beli2006AlphaLaws.{u, v} K]
    (D : Beli2009NormGeneratorSeedData b C normGenerator hnext)
    (leftDet : Kˣ) (heven : b.IsPrefixApproximation C.start leftDet) :
    b.IsPrefixApproximation (C.start + 1) (normGenerator * leftDet) := by
  have hstart : C.start < n + 2 := C.start_lt_stop.trans_le C.stop_le
  have hprefix := b.toBONG.prefixProduct_succ C.start hstart
  have hvalue : b.valueUnit C.firstIndex =
      b.valueUnit ⟨C.start, hstart⟩ := rfl
  have hproduct :
      (leftDet * b.prefixProduct C.start) *
          (normGenerator * b.valueUnit C.firstIndex) =
        (normGenerator * leftDet) * b.prefixProduct (C.start + 1) := by
    rw [hvalue]
    change (leftDet * b.toBONG.prefixProduct C.start) *
        (normGenerator * b.toBONG.valueUnit ⟨C.start, hstart⟩) =
      (normGenerator * leftDet) *
        b.toBONG.prefixProduct (C.start + 1)
    rw [hprefix]
    ac_rfl
  have hboundaryPos : 0 < C.start + 1 := by omega
  have hboundaryLt : C.start + 1 < n + 2 :=
    hnext.trans_le C.stop_le
  unfold IsPrefixApproximation
  rw [b.prefixAlphaCap_of_internal hboundaryPos hboundaryLt]
  calc
    (b.alphaValue ⟨C.start + 1 - 1, by omega⟩ : WithTop ℚ) ≤
        min
          (defectOrder (K := K) (leftDet * b.prefixProduct C.start))
          (defectOrder (K := K)
            (normGenerator * b.valueUnit C.firstIndex)) := by
      apply le_min
      · simpa only [Nat.add_sub_cancel] using
          D.currentAlpha_le_evenSeedDefect leftDet heven
      · simpa only [Nat.add_sub_cancel] using
          D.alpha_le_normGeneratorProductDefect
    _ ≤ defectOrder (K := K)
        ((leftDet * b.prefixProduct C.start) *
          (normGenerator * b.valueUnit C.firstIndex)) :=
      defectOrder_mul_ge_min _ _
    _ = defectOrder (K := K)
        ((normGenerator * leftDet) * b.prefixProduct (C.start + 1)) := by
      rw [hproduct]

end Beli2009NormGeneratorSeedData

namespace JordanApproximationSeeds

variable {b : GoodBONG q L (n + 2)} {C : b.JordanBlockCoordinates}

/-- Assemble the two cited base cases into the seed object consumed by the
already formalized two-step induction of Lemma 3.2. -/
def ofOmeara9328AndNormGenerator
    [Beli2006AlphaLaws.{u, v} K]
    (determinant : Omeara9328DeterminantSeedData b C)
    (normGenerator : Kˣ)
    (normData : ∀ hnext : C.start + 1 < C.stop,
      Beli2009NormGeneratorSeedData b C normGenerator hnext) :
    JordanApproximationSeeds b C where
  leftDet := determinant.leftDet
  normGenerator := normGenerator
  evenSeed := determinant.evenSeed
  oddSeed hnext :=
    (normData hnext).oddSeed determinant.leftDet determinant.evenSeed

end JordanApproximationSeeds

end BONG.GoodBONG

end Bong
