/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal
import Bong.Dyadic.ValuationUnitDefect

/-!
# Beli (2019), Lemma 7.9(ii): the odd-coordinate defect bound

An even-order square class has defect at least one.  This follows directly
from perfectness of the residue field, without the paper-specific two-adic
classification interface.  Together with P2, this proves the arithmetic core
of the odd-coordinate branch in condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The arithmetic core of the odd-coordinate branch in Lemma 7.9(ii). -/
theorem lemma79_ii_of_odd_coordinate_bounds
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≤
      c.orderSequence.entryOrZero (i.val - 1))
    (hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val)
    (hAlphaUpper : b.representationAlphaValue c i ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        c.orderSequence.entryOrZero (i.val - 1) + 1 : Int) : ℚ))
    (heven : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hcurrentStrict :
      b.orderSequence.entryOrZero (i.val - 1) <
        c.orderSequence.entryOrZero (i.val - 1)
  · have hshiftNonpos :
        ((b.orderSequence.entryOrZero (i.val - 1) -
          c.orderSequence.entryOrZero (i.val - 1) + 1 : Int) : ℚ) ≤ 0 := by
      exact_mod_cast (show b.orderSequence.entryOrZero (i.val - 1) -
        c.orderSequence.entryOrZero (i.val - 1) + 1 ≤ 0 by omega)
    have hAlphaNonpos : b.representationAlphaValue c i ≤ 0 :=
      hAlphaUpper.trans hshiftNonpos
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤ 0 := by
        exact_mod_cast hAlphaNonpos
      _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
        b.truncatedPrefixDefect_nonneg c 1 i.val i.val
  · have hcurrentEq :
        b.orderSequence.entryOrZero (i.val - 1) =
          c.orderSequence.entryOrZero (i.val - 1) :=
      le_antisymm hcurrent (le_of_not_gt hcurrentStrict)
    have hAlphaOne : b.representationAlphaValue c i ≤ 1 := by
      calc
        b.representationAlphaValue c i ≤
            ((b.orderSequence.entryOrZero (i.val - 1) -
              c.orderSequence.entryOrZero (i.val - 1) + 1 : Int) : ℚ) :=
          hAlphaUpper
        _ = 1 := by rw [hcurrentEq]; norm_num
    have hiPrevious : i.val - 1 < n + 1 := by
      have := i.pos
      have := i.lt_large
      omega
    have hiAlphaPrevious : i.val - 1 < n := by
      have := i.pos
      have := i.lt_large
      omega
    let previous : Fin n := ⟨i.val - 1, hiAlphaPrevious⟩
    have previousSucc : previous.succ = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      simp only [previous, Fin.succ_mk]
      have := i.pos
      omega
    have previousCast :
        previous.castSucc = ⟨i.val - 1, hiPrevious⟩ := by
      apply Fin.ext
      rfl
    by_cases hbeta : (1 : ℚ) ≤ b.alphaValue previous
    · by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
      · have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
            (1 * b.prefixProduct i.val * c.prefixProduct i.val) := by
          simpa only [one_mul] using
            defectOrder_one_le_of_even
              (b.prefixProduct i.val * c.prefixProduct i.val)
                (heven hcurrentEq)
        have hbCap : (1 : WithTop ℚ) ≤ b.prefixAlphaCap i.val := by
          rw [b.prefixAlphaCap_of_internal i.pos i.lt_large]
          exact_mod_cast hbeta
        have hcCap : (1 : WithTop ℚ) ≤ c.prefixAlphaCap i.val := by
          rw [c.prefixAlphaCap_of_internal i.pos i.lt_large]
          exact_mod_cast hgamma
        have htruncated : (1 : WithTop ℚ) ≤
            b.truncatedPrefixDefect c 1 i.val i.val := by
          unfold truncatedPrefixDefect
          exact le_min hraw (le_min hbCap hcCap)
        exact (show (b.representationAlphaValue c i : WithTop ℚ) ≤ 1 by
          exact_mod_cast hAlphaOne).trans htruncated
      · have hgammaZero : c.alphaValue previous = 0 := by
          by_contra hne
          exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
        have hgap := (c.alpha_p2 previous).2.mp hgammaZero
        rw [orderGap, previousSucc, previousCast] at hgap
        have hnext : b.orderSequence.entryOrZero i.val -
            c.orderSequence.entryOrZero (i.val - 1) ≤
              -(2 * (ramificationIndex K : Int)) := by
          have hgap' : c.orderSequence.entryOrZero i.val -
              c.orderSequence.entryOrZero (i.val - 1) =
                -(2 * (ramificationIndex K : Int)) := by
            simpa only [
              BeliOrderSequence.entryOrZero_of_lt c.orderSequence
                i.lt_large,
              BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
              orderSequence_at] using hgap
          omega
        have hhalf : b.representationHalfGap c i ≤ 0 := by
          unfold representationHalfGap
          norm_cast
          simp only [Rat.divInt_eq_div]
          have hnext' : b.order ⟨i.val, i.lt_large⟩ -
              c.order ⟨i.val - 1, hiPrevious⟩ ≤
                -(2 * (ramificationIndex K : Int)) := by
            simpa only [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              i.lt_large,
              BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
              orderSequence_at]
              using hnext
          have hnextQ :
              ((b.order ⟨i.val, i.lt_large⟩ -
                c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) ≤
                  -(2 * (ramificationIndex K : ℚ)) := by
            exact_mod_cast hnext'
          linarith
        calc
          (b.representationAlphaValue c i : WithTop ℚ) =
              b.representationAlpha c i := b.coe_representationAlphaValue c i
          _ ≤ b.representationHalfGap c i :=
            b.representationAlpha_le_halfGap c i
          _ ≤ 0 := hhalf
          _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
            b.truncatedPrefixDefect_nonneg c 1 i.val i.val
    · have hbetaZero : b.alphaValue previous = 0 := by
        by_contra hne
        exact hbeta (b.one_le_alphaValue_of_ne_zero previous hne)
      have hgap := (b.alpha_p2 previous).2.mp hbetaZero
      rw [orderGap, previousSucc, previousCast] at hgap
      have hnext : b.orderSequence.entryOrZero i.val -
          c.orderSequence.entryOrZero (i.val - 1) =
            -(2 * (ramificationIndex K : Int)) := by
        have hgap' : b.orderSequence.entryOrZero i.val -
            b.orderSequence.entryOrZero (i.val - 1) =
              -(2 * (ramificationIndex K : Int)) := by
          simpa only [
            BeliOrderSequence.entryOrZero_of_lt b.orderSequence
              i.lt_large,
            BeliOrderSequence.entryOrZero_of_lt b.orderSequence hiPrevious,
            orderSequence_at] using hgap
        omega
      have hhalf : b.representationHalfGap c i ≤ 0 := by
        unfold representationHalfGap
        norm_cast
        simp only [Rat.divInt_eq_div]
        have hnext' : b.order ⟨i.val, i.lt_large⟩ -
            c.order ⟨i.val - 1, hiPrevious⟩ =
              -(2 * (ramificationIndex K : Int)) := by
          simpa only [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            i.lt_large,
            BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
            orderSequence_at]
            using hnext
        have hnextQ :
            ((b.order ⟨i.val, i.lt_large⟩ -
              c.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) =
                -(2 * (ramificationIndex K : ℚ)) := by
          exact_mod_cast hnext'
        linarith
      calc
        (b.representationAlphaValue c i : WithTop ℚ) =
            b.representationAlpha c i := b.coe_representationAlphaValue c i
        _ ≤ b.representationHalfGap c i :=
          b.representationAlpha_le_halfGap c i
        _ ≤ 0 := hhalf
        _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
          b.truncatedPrefixDefect_nonneg c 1 i.val i.val

/-- The primary candidate bounds a representation alpha by the next source
alpha.  This is the first inequality in case 2 of the proof of 2.1(ii). -/
theorem representationAlphaValue_le_primary_nextAlpha
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1) :
    a.representationAlphaValue b i ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
        a.alphaValue ⟨i.val, by omega⟩ := by
  apply WithTop.coe_le_coe.mp
  rw [a.coe_representationAlphaValue b i]
  calc
    a.representationAlpha b i ≤ a.representationPrimaryDefect b i :=
      a.representationAlpha_le_primary b i
    _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.prefixAlphaCap (i.val + 1) := by
      unfold representationPrimaryDefect
      exact add_le_add_right
        (a.truncatedPrefixDefect_le_leftCap b (-1)
          (i.val + 1) (i.val - 1)) _
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
        a.alphaValue ⟨i.val, by omega⟩ : ℚ) := by
      rw [a.prefixAlphaCap_of_internal (by omega) hiNext]
      norm_cast

/-- Case 2 of the proof of 2.1(ii), with the profile-specific estimate on
the next source alpha supplied explicitly. -/
theorem lemma79_ii_of_odd_coordinate
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hnextAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        b.orderSequence.entryOrZero i.val + 1 : Int) : ℚ))
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≤
      c.orderSequence.entryOrZero (i.val - 1))
    (hpair : b.orderSequence.entryOrZero (i.val - 1) +
        b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero i.val)
    (heven : b.orderSequence.entryOrZero (i.val - 1) =
      c.orderSequence.entryOrZero (i.val - 1) →
      Even (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiPrevious : i.val - 1 < n + 1 := by omega
  have hcandidate := b.representationAlphaValue_le_primary_nextAlpha
    c i hiNext
  have hcandidate' : b.representationAlphaValue c i ≤
      ((b.orderSequence.entryOrZero i.val -
        c.orderSequence.entryOrZero (i.val - 1) : Int) : ℚ) +
        b.alphaValue ⟨i.val, by omega⟩ := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      i.lt_large,
      BeliOrderSequence.entryOrZero_of_lt c.orderSequence hiPrevious,
      orderSequence_at] using hcandidate
  have hnextAlpha' := hnextAlpha
  push_cast at hnextAlpha'
  have hAlphaUpper : b.representationAlphaValue c i ≤
      ((b.orderSequence.entryOrZero (i.val - 1) -
        c.orderSequence.entryOrZero (i.val - 1) + 1 : Int) : ℚ) := by
    calc
      b.representationAlphaValue c i ≤
          ((b.orderSequence.entryOrZero i.val -
            c.orderSequence.entryOrZero (i.val - 1) : Int) : ℚ) +
            b.alphaValue ⟨i.val, by omega⟩ := hcandidate'
      _ ≤ ((b.orderSequence.entryOrZero (i.val - 1) -
          c.orderSequence.entryOrZero (i.val - 1) + 1 : Int) : ℚ) := by
        push_cast
        linarith [hnextAlpha']
  exact b.lemma79_ii_of_odd_coordinate_bounds c i hcurrent hpair
    hAlphaUpper heven

end BONG.GoodBONG

end Bong
