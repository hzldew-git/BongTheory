/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralDual
import Bong.Bong.Beli2019SectionFourCentralParity
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 4.5(i)

This file proves the forward half of Lemma 4.5.  The nonterminal prefix
representation is obtained from condition 2.1(iii) at the following central
boundary.  At the terminal boundary the following prefix is the complete
ambient BONG, so the concrete coordinate change between the two full BONGs
replaces that unavailable central index.

The Hilbert-symbol assertion is proved from the two capped defects printed in
the paper; it is not an additional local-field law.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The two conclusions of Lemma 4.5(i). -/
structure SectionFourLemma45ForwardCertificate
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop where
  middleCurrent : DiagonalRepresents
    (b.prefixValues i.val i.current_le_sameRank)
    (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large))
  hilbert : hilbertSymbol K
    (a.prefixProduct i.val * b.prefixProduct i.val)
    (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)) = 1

/-- The primary candidate for `C_i` gives the lower bound
`T_i-R_(i+1)+C_i <= d[-a_(1,i+1)c_(1,i-1)]`. -/
theorem sectionFourLemma45_shiftedCurrentAlpha_le_currentDefect
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    (((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
        a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationAlpha c (i.current i.lt_large.le) ≤
      a.centralCurrentDefect c i := by
  have hprimary :=
    a.representationAlpha_le_primary c (i.current i.lt_large.le)
  unfold representationPrimaryDefect at hprimary
  unfold centralCurrentDefect
  change a.representationAlpha c (i.current i.lt_large.le) ≤
      (((a.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) at hprimary
  let shift : ℚ := ((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
    a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)
  let opposite : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  change (shift : WithTop ℚ) +
      a.representationAlpha c (i.current i.lt_large.le) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)
  have hprimary' : a.representationAlpha c (i.current i.lt_large.le) ≤
      (opposite : WithTop ℚ) +
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [opposite] using hprimary
  have hcoeff :
      (shift : WithTop ℚ) + (opposite : WithTop ℚ) = 0 := by
    dsimp only [shift, opposite]
    norm_cast
    ring
  calc
    _ ≤ (shift : WithTop ℚ) +
        ((opposite : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :=
      add_le_add_right hprimary' _
    _ = a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      rw [← add_assoc, hcoeff, zero_add]

/-- The shifted comparison in Lemma 4.5 dominates the lower expression used
in the final average contradiction. -/
theorem sectionFourLemma45_centralLower_le_shiftedCurrentAlpha
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    a.centralSecondaryLower c i hiNext ≤
      (((a.order ⟨i.val + 1, hiNext⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
        a.representationAlpha b (i.current i.lt_large.le) := by
  let base : ℚ := ((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hiNext⟩ -
      c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  have hadd := add_le_add_left hshift (base : WithTop ℚ)
  have hleftCoeff :
      (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩ -
          a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
        ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + (base : WithTop ℚ) := by
    dsimp only [base]
    norm_cast
    ring
  have hrightCoeff :
      (((a.order ⟨i.val + 1, hiNext⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          (base : WithTop ℚ) := by
    dsimp only [base]
    norm_cast
    ring
  unfold centralSecondaryLower
  rw [hleftCoeff, hrightCoeff]
  calc
    _ =
        (((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) :
              ℚ) : WithTop ℚ) + a.representationAlpha c i.previous) +
          (base : WithTop ℚ) := by ac_rfl
    _ ≤ (((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) +
        (base : WithTop ℚ) := hadd
    _ = _ := by ac_rfl

/-- The adjacent pair `(a_(i+1),a_(i+2))` gives the upper comparison used
to force the strict capped-defect triangle in Lemma 4.5. -/
theorem sectionFourLemma45_currentAlpha_le_shiftedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1) :
    a.representationAlpha c (i.current i.lt_large.le) ≤
      (((a.order ⟨i.val + 1, hiNext⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
  let p : Fin n := ⟨i.val, by omega⟩
  let capShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let nextShift : ℚ := ((a.order ⟨i.val + 1, hiNext⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let gap : ℚ := (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
    (a.order ⟨i.val + 1, hiNext⟩ : ℚ)
  have hcap := (a.representationAlpha_le_prime
    c (i.current i.lt_large.le)).trans
      (a.representationAlphaPrime_le_primaryLeftCap
        c (i.current i.lt_large.le))
  simp only [CentralRepresentationIndex.current] at hcap
  rw [a.prefixAlphaCap_of_internal (by omega) hiNext] at hcap
  have hpIndex : (⟨i.val + 1 - 1, by omega⟩ : Fin n) = p := by
    apply Fin.ext
    simp only [p]
    omega
  rw [hpIndex] at hcap
  have houter : a.representationAlpha c (i.current i.lt_large.le) ≤
      (capShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := by
    simpa only [capShift, CentralRepresentationIndex.current] using hcap
  have hadjacentRaw := a.order_sub_add_alpha_le_cappedAdjacent p
  have hpCast : p.castSucc = (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ = (⟨i.val + 1, hiNext⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hpCast, hpSucc] at hadjacentRaw
  push_cast at hadjacentRaw
  have hgapEq : (gap : WithTop ℚ) =
      (((a.order ⟨i.val, i.lt_large⟩ : ℚ) : WithTop ℚ) -
        ((a.order ⟨i.val + 1, hiNext⟩ : ℚ) : WithTop ℚ)) := by
    dsimp only [gap]
    norm_cast
  have hadjacent : (gap : WithTop ℚ) +
      (a.alphaValue p : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    rw [hgapEq]
    simpa only [p] using hadjacentRaw
  have hcoeff : (nextShift : WithTop ℚ) + (gap : WithTop ℚ) =
      (capShift : WithTop ℚ) := by
    dsimp only [nextShift, gap, capShift]
    norm_cast
    push_cast
    ring
  calc
    a.representationAlpha c (i.current i.lt_large.le) ≤
        (capShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := houter
    _ = (nextShift : WithTop ℚ) +
        ((gap : WithTop ℚ) + (a.alphaValue p : WithTop ℚ)) := by
      rw [← add_assoc, hcoeff]
    _ ≤ (nextShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) :=
      add_le_add_right hadjacent _

/-- In the nonterminal prime branch of Lemma 4.5, the following middle
alpha is large enough to activate condition 2.1(iii) at the next boundary. -/
theorem sectionFourLemma45_currentAlpha_le_shiftedNextAlpha_of_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hcross : b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val + 1, hiNext⟩)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le))
    (hnextPrime :
      a.representationAlpha b
          (nextRepresentationIndex (i.current i.lt_large.le) hiNext) =
        a.representationAlphaPrime b
          (nextRepresentationIndex (i.current i.lt_large.le) hiNext)) :
    a.representationAlpha c (i.current i.lt_large.le) ≤
      (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
        a.representationAlpha b
          (nextRepresentationIndex (i.current i.lt_large.le) hiNext) := by
  let current := i.current i.lt_large.le
  let next := nextRepresentationIndex current hiNext
  let middleShift : ℚ := ((b.order ⟨i.val, i.lt_large⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let sourceShift : ℚ := ((a.order ⟨i.val + 1, hiNext⟩ -
    c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
  let primary := a.representationPrimaryDefect b next
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val
  let adjacentDefect :=
    a.truncatedPrefixDefect a (-1) (i.val + 2) i.val
  let comparisonDefect :=
    a.truncatedPrefixDefect b 1 i.val i.val
  have hlower := a.sectionFourLemma45_centralLower_le_shiftedCurrentAlpha
    b c i hiNext hshift
  have hupper := a.centralCurrentAlpha_le_leftAverage c i hiNext
  have hbaseline : a.centralSecondaryLower c i hiNext ≤
      (sourceShift : WithTop ℚ) +
        a.representationAlpha b (i.current i.lt_large.le) := by
    simpa only [sourceShift] using hlower
  change a.representationAlpha c (i.current i.lt_large.le) ≤
    (middleShift : WithTop ℚ) + a.representationAlpha b next
  have hprimaryBound :
      a.representationAlpha c (i.current i.lt_large.le) ≤
        (middleShift : WithTop ℚ) + primary := by
    by_contra hnot
    have hstrict : (middleShift : WithTop ℚ) + primary <
        a.representationAlpha c (i.current i.lt_large.le) :=
      lt_of_not_ge hnot
    have hprimaryForm : (middleShift : WithTop ℚ) + primary =
        (sourceShift : WithTop ℚ) + sourceDefect := by
      dsimp only [primary, middleShift, sourceShift, sourceDefect, next,
        current, nextRepresentationIndex, CentralRepresentationIndex.current]
      unfold representationPrimaryDefect
      simp only [Nat.add_sub_cancel]
      rw [← add_assoc]
      congr 1
      norm_cast
      ring
    have houterAdjacentRaw :=
      a.sectionFourLemma45_currentAlpha_le_shiftedAdjacent c i hiNext
    rw [← a.truncatedPrefixDefect_comm a (-1) (i.val + 2) i.val]
      at houterAdjacentRaw
    have houterAdjacent :
        a.representationAlpha c (i.current i.lt_large.le) ≤
          (sourceShift : WithTop ℚ) + adjacentDefect := by
      simpa only [sourceShift, adjacentDefect] using houterAdjacentRaw
    have hsourceStrict : sourceDefect < adjacentDefect := by
      apply (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp
      calc
        (sourceShift : WithTop ℚ) + sourceDefect =
            (middleShift : WithTop ℚ) + primary := hprimaryForm.symm
        _ < a.representationAlpha c (i.current i.lt_large.le) := hstrict
        _ ≤ (sourceShift : WithTop ℚ) + adjacentDefect := houterAdjacent
    have htriangleRaw :=
      a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b a
        (i.val + 2) i.val i.val (by
          simpa only [sourceDefect, adjacentDefect] using hsourceStrict)
    rw [b.truncatedPrefixDefect_comm a 1 i.val i.val] at htriangleRaw
    have htriangle : sourceDefect = comparisonDefect := by
      simpa only [sourceDefect, comparisonDefect] using htriangleRaw
    have hABRaw := habDefect (i.current i.lt_large.le)
    rw [a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hABRaw
    have hAB : a.representationAlpha b (i.current i.lt_large.le) ≤
        comparisonDefect := by
      simpa only [comparisonDefect, CentralRepresentationIndex.current]
        using hABRaw
    have hcandidateLower :
        (sourceShift : WithTop ℚ) +
            a.representationAlpha b (i.current i.lt_large.le) ≤
          (middleShift : WithTop ℚ) + primary := by
      calc
        (sourceShift : WithTop ℚ) +
            a.representationAlpha b (i.current i.lt_large.le) ≤
          (sourceShift : WithTop ℚ) + comparisonDefect :=
            add_le_add_right hAB _
        _ = (sourceShift : WithTop ℚ) + sourceDefect := by
          rw [htriangle]
        _ = (middleShift : WithTop ℚ) + primary := hprimaryForm.symm
    exact a.sectionFourForwardSecondaryContradiction c i hiNext htrigger
      (hbaseline.trans (hcandidateLower.trans hstrict.le)) hupper
  by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
  · let secondary :=
      a.representationSecondaryPreviousDefect b next hinterior
    have hiTwo : i.val + 2 < n + 1 := by
      simpa only [next, current, nextRepresentationIndex,
        CentralRepresentationIndex.current] using hinterior.2
    have hcrossNext : b.order ⟨next.val - 2, by
          have := next.lt_large
          omega⟩ ≤ a.order ⟨next.val, next.lt_large⟩ := by
      change b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ ≤
        a.order ⟨i.val + 1, hiNext⟩
      exact hcross.le
    have hprimeNormal :=
      a.representationAlphaPrime_eq_min_primary_previous
        b next hinterior hcrossNext
    have hsecondaryBound :
        a.representationAlpha c (i.current i.lt_large.le) ≤
          (middleShift : WithTop ℚ) + secondary := by
      by_contra hnot
      have hstrict : (middleShift : WithTop ℚ) + secondary <
          a.representationAlpha c (i.current i.lt_large.le) :=
        lt_of_not_ge hnot
      have htwoStepRaw := a.orderSequence.twoStep i.val hiTwo
      have htwoStep : a.order ⟨i.val, i.lt_large⟩ ≤
          a.order ⟨i.val + 2, hiTwo⟩ := by
        change a.orderSequence.entry i.val i.lt_large ≤
          a.orderSequence.entry (i.val + 2) hiTwo
        exact htwoStepRaw
      let primaryShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : ℚ)
      let secondaryShift : ℚ := ((a.order ⟨next.val, next.lt_large⟩ +
        a.order ⟨next.val + 1, hinterior.2⟩ -
        b.order ⟨next.val - 2, by have := next.le_small; omega⟩ -
        b.order ⟨next.val - 1, by have := next.le_small; omega⟩ : Int) : ℚ)
      let commonDefect :=
        a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)
      have hsecondaryDefect :
          a.truncatedPrefixDefect b (-1) next.val (next.val - 2) =
            commonDefect := by
        dsimp only [next, current, nextRepresentationIndex,
          CentralRepresentationIndex.current, commonDefect]
        congr 1 <;> omega
      have hsecondaryShiftForm : secondaryShift =
          ((a.order ⟨i.val + 1, hiNext⟩ +
            a.order ⟨i.val + 2, hiTwo⟩ -
            b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
            b.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) := by
        dsimp only [secondaryShift, next, current, nextRepresentationIndex,
          CentralRepresentationIndex.current]
        congr 1 <;> omega
      have hshiftCoe : sourceShift + primaryShift ≤
          middleShift + secondaryShift := by
        rw [hsecondaryShiftForm]
        dsimp only [sourceShift, primaryShift, middleShift]
        push_cast
        have htwoStepQ :
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) ≤
              (a.order ⟨i.val + 2, hiTwo⟩ : ℚ) := by
          exact_mod_cast htwoStep
        linarith
      have hAlphaPrimary :=
        a.representationAlpha_le_primary b (i.current i.lt_large.le)
      have hcandidateLower :
          (sourceShift : WithTop ℚ) +
              a.representationAlpha b (i.current i.lt_large.le) ≤
            (middleShift : WithTop ℚ) + secondary := by
        change (sourceShift : WithTop ℚ) +
            a.representationAlpha b (i.current i.lt_large.le) ≤
          (middleShift : WithTop ℚ) +
            ((secondaryShift : WithTop ℚ) +
              a.truncatedPrefixDefect b (-1) next.val (next.val - 2))
        have hprimaryForm : a.representationPrimaryDefect b
            (i.current i.lt_large.le) =
            (primaryShift : WithTop ℚ) + commonDefect := by
          dsimp only [primaryShift, commonDefect]
          unfold representationPrimaryDefect
          simp only [CentralRepresentationIndex.current]
        calc
          (sourceShift : WithTop ℚ) +
              a.representationAlpha b (i.current i.lt_large.le) ≤
            (sourceShift : WithTop ℚ) +
              a.representationPrimaryDefect b (i.current i.lt_large.le) :=
                add_le_add_right hAlphaPrimary _
          _ = ((sourceShift + primaryShift : ℚ) : WithTop ℚ) +
              commonDefect := by rw [hprimaryForm, ← add_assoc, ← WithTop.coe_add]
          _ ≤ ((middleShift + secondaryShift : ℚ) : WithTop ℚ) +
              commonDefect := add_le_add (by exact_mod_cast hshiftCoe) le_rfl
          _ = (middleShift : WithTop ℚ) +
              ((secondaryShift : WithTop ℚ) +
                a.truncatedPrefixDefect b (-1) next.val (next.val - 2)) := by
            rw [hsecondaryDefect]
            norm_num [add_assoc]
      exact a.sectionFourForwardSecondaryContradiction c i hiNext htrigger
        (hbaseline.trans (hcandidateLower.trans hstrict.le)) hupper
    rw [hnextPrime, hprimeNormal, add_min]
    exact le_min hprimaryBound hsecondaryBound
  · have hprimeEndpoint :=
      a.representationAlphaPrime_eq_primary_of_not_interior
        b next hinterior
    rw [hnextPrime, hprimeEndpoint]
    exact hprimaryBound

/-- In the nonterminal branch of Lemma 4.5(i), the outer trigger propagates
to the following central boundary.  If the following alpha is non-prime this
is Lemma 2.14; in the prime case it is the numerical calculation on lines
2557--2576. -/
theorem sectionFourLemma45_nextAlphaTrigger
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hiNext : i.val + 1 < n + 1)
    (htrigger : a.centralAlphaTrigger c i)
    (hcross : b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val + 1, hiNext⟩)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    a.centralAlphaTrigger b
      { val := i.val + 1
        one_lt := by have := i.one_lt; omega
        lt_large := hiNext
        le_small_succ := by omega } := by
  let current := i.current i.lt_large.le
  let next := nextRepresentationIndex current hiNext
  let j : CentralRepresentationIndex (n + 1) (n + 1) :=
    { val := i.val + 1
      one_lt := by have := i.one_lt; omega
      lt_large := hiNext
      le_small_succ := by omega }
  have hjSmall : j.val ≤ n + 1 := by
    dsimp only [j]
    omega
  by_cases hne : a.representationAlpha b next ≠
      a.representationAlphaPrime b next
  · have hne' : a.representationAlpha b (j.current hjSmall) ≠
        a.representationAlphaPrime b (j.current hjSmall) := by
      simpa only [j, next, current, nextRepresentationIndex,
        CentralRepresentationIndex.current] using hne
    simpa only [j] using
      a.centralAlphaTrigger_of_current_alpha_ne_prime b le_rfl
        hab.orderCondition hab.defectCondition j hjSmall hne'
  · have hnextPrime : a.representationAlpha b next =
        a.representationAlphaPrime b next := not_ne_iff.mp hne
    have hbound :=
      a.sectionFourLemma45_currentAlpha_le_shiftedNextAlpha_of_prime
        b c hab.defectCondition i hiNext htrigger hcross hshift hnextPrime
    have houter := htrigger.2
    unfold centralAlphaTrigger
    refine ⟨?_, ?_⟩
    · change b.order ⟨i.val + 1 - 2, by omega⟩ <
        a.order ⟨i.val + 1, hiNext⟩
      convert hcross using 1 <;> congr 1 <;> omega
    · unfold centralAdjustedAlpha at houter ⊢
      rw [dif_pos i.lt_large.le] at houter
      rw [dif_pos hjSmall]
      rw [← a.coe_representationAlphaValue c i.previous,
        ← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hshift
      rw [← a.coe_representationAlphaValue c (i.current i.lt_large.le),
        ← a.coe_representationAlphaValue b next] at hbound
      norm_cast at houter hshift hbound ⊢
      push_cast at houter hshift hbound ⊢
      dsimp only [j, next, current, nextRepresentationIndex,
        CentralRepresentationIndex.previous,
        CentralRepresentationIndex.current] at houter hshift hbound ⊢
      simp only [Nat.add_sub_cancel] at houter hshift hbound ⊢
      linarith

/-- The representation conclusion of Lemma 4.5(i).  At an interior boundary
condition (iii) is activated one step to the right; at `i = n - 1` the target
prefix is the complete ambient BONG. -/
theorem sectionFourLemma45_middleCurrent_represents
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiNext : i.val + 1 < n + 1,
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩) ∨
        i.val + 1 = n + 1)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    DiagonalRepresents
      (b.prefixValues i.val i.current_le_sameRank)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  rcases hboundary with ⟨hiNext, hcross⟩ | hend
  · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
      { val := i.val + 1
        one_lt := by have := i.one_lt; omega
        lt_large := hiNext
        le_small_succ := by omega }
    have hnextTrigger := a.sectionFourLemma45_nextAlphaTrigger
      b c hab i hiNext htrigger hcross hshift
    change a.centralAlphaTrigger b j at hnextTrigger
    have hrep := hab.centralRepresentations j hnextTrigger
    exact prefixRepresents_cast b a (by
      dsimp only [j]
      omega) rfl hrep
  · have hprefix := b.prefixValues_represents_of_le
      i.val (n + 1) (by omega) le_rfl
    have hfull := b.fullPrefix_represents a
    exact prefixRepresents_cast b a rfl hend.symm (hprefix.trans hfull)

/-- The outer trigger and the shifted comparison make the two raw defects in
Lemma 4.5(i) have sum strictly larger than `2e`. -/
theorem sectionFourLemma45_twoE_lt_truncatedDefectSum
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 i.val i.val +
        a.centralCurrentDefect c i := by
  have hAB := habDefect (i.current i.lt_large.le)
  rw [a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hAB
  have hcurrent := a.sectionFourLemma45_shiftedCurrentAlpha_le_currentDefect c i
  have hlower :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.representationAlpha b (i.current i.lt_large.le) +
          ((((c.order ⟨i.val - 1, by have := i.lt_large; omega⟩ -
              a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            a.representationAlpha c (i.current i.lt_large.le)) := by
    have hsum := htrigger.2
    unfold centralAdjustedAlpha at hsum
    rw [dif_pos (show i.val ≤ n + 1 from i.lt_large.le)] at hsum
    rw [← a.coe_representationAlphaValue c i.previous,
      ← a.coe_representationAlphaValue b (i.current i.lt_large.le)] at hshift
    rw [← a.coe_representationAlphaValue b (i.current i.lt_large.le),
      ← a.coe_representationAlphaValue c (i.current i.lt_large.le)]
    norm_cast at hsum hshift ⊢
    push_cast at hsum hshift ⊢
    linarith
  exact hlower.trans_le (add_le_add hAB hcurrent)

/-- The Hilbert-symbol conclusion of Lemma 4.5(i). -/
theorem sectionFourLemma45_hilbert
    [HilbertSymbolLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    hilbertSymbol K
      (a.prefixProduct i.val * b.prefixProduct i.val)
      (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)) = 1 := by
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  have hsum := a.sectionFourLemma45_twoE_lt_truncatedDefectSum
    b c habDefect i htrigger hshift
  apply hsum.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
  · unfold centralCurrentDefect
    simpa only [neg_one_mul] using
      (a.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))

/-- Beli (2019), Lemma 4.5(i), with the paper's interior/terminal boundary
alternative made explicit. -/
theorem sectionFourLemma45_forward
    [Beli2006AlphaLaws.{u, v} K] [HilbertSymbolLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hboundary :
      (∃ hiNext : i.val + 1 < n + 1,
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩) ∨
        i.val + 1 = n + 1)
    (hshift :
      ((((-a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ : Int) : Int) : ℚ) :
            WithTop ℚ) + a.representationAlpha c i.previous ≤
        ((((-a.order ⟨i.val, i.lt_large⟩ : Int) : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b (i.current i.lt_large.le)) :
    SectionFourLemma45ForwardCertificate a b c i where
  middleCurrent := a.sectionFourLemma45_middleCurrent_represents
    b c hab i htrigger hboundary hshift
  hilbert := a.sectionFourLemma45_hilbert
    b c hab.defectCondition i htrigger hshift

end BONG.GoodBONG

end Bong
