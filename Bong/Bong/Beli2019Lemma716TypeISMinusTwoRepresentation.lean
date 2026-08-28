/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeISMinusOne

/-!
# Beli (2019), Lemma 7.16(ii): the embedded Lemma 2.19 step

In the exceptional type-I boundary the comparison prefix through
`c_(s-2)` has to be represented by the original prefix through `a_s`.
This is the `l-j=3` instance of Lemma 2.19 used in the paper.  The proof
below derives it from the revised four representation conditions: either
condition (iii') applies at the next central index, or condition (iv)
applies one index earlier.  At the terminal rank the common ambient
quadratic space supplies the representation directly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]

/-- The exact `l-j=3` instance of Lemma 2.19 needed at the exceptional
type-I boundary of Lemma 7.16(ii). -/
theorem lemma716_typeI_sMinusTwo_prefixRepresents
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hsFour : 4 ≤ s)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hsourceLast : a.order ⟨s - 1, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 1)
    (hcomparisonLast : c.order ⟨s - 3, by
      have := D.le_rank
      omega⟩ = R - 2 * (ramificationIndex K : Int) + 1)
    (hmixed :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
        a.truncatedPrefixDefect c (-1) s (s - 2)) :
    DiagonalRepresents
      (c.prefixValues (s - 2) (by
        have := D.le_rank
        omega))
      (a.prefixValues s D.le_rank) := by
  by_cases hsInterior : s < n + 3
  · let sourceNext : Fin (n + 3) := ⟨s, hsInterior⟩
    let comparisonNext : Fin (n + 3) := ⟨s - 2, by
      have := D.le_rank
      omega⟩
    have hsourceNext : R + 2 ≤ a.order sourceNext := by
      simpa only [sourceNext] using
        a.lemma714_typeI_nextOrder_ge R s hI hsInterior
    by_cases hcross : c.order comparisonNext < a.order sourceNext
    · let i : CentralRepresentationIndex (n + 3) (n + 3) :=
        { val := s
          one_lt := by omega
          lt_large := hsInterior
          le_small_succ := by omega }
      have hthreshold :
          (((2 * (ramificationIndex K : ℚ) +
              (c.order comparisonNext : ℚ) -
              (a.order sourceNext : ℚ) : ℚ)) : WithTop ℚ) <
            (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
        apply WithTop.coe_lt_coe.mpr
        have hcrossQ : (c.order comparisonNext : ℚ) <
            (a.order sourceNext : ℚ) := by
          exact_mod_cast hcross
        linarith
      have hcurrentNonneg : (0 : WithTop ℚ) ≤
          a.centralCurrentDefect c i := by
        unfold centralCurrentDefect
        exact a.truncatedPrefixDefect_nonneg c (-1) (i.val + 1)
          (i.val - 1)
      have hprevious :
          (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
            a.centralPreviousDefect c i := by
        unfold centralPreviousDefect
        simpa only [i] using hmixed
      have htrigger : a.centralDefectTrigger c i := by
        unfold centralDefectTrigger
        dsimp only [i]
        constructor
        · simpa only [comparisonNext, sourceNext] using hcross
        · have hsum :
              (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ≤
                a.centralPreviousDefect c i +
                  a.centralCurrentDefect c i :=
            hprevious.trans (le_add_of_nonneg_right hcurrentNonneg)
          have hthreshold' :
              (((2 * (ramificationIndex K : ℚ) +
                  (c.order ⟨s - 2, by omega⟩ : ℚ) -
                  (a.order ⟨s, hsInterior⟩ : ℚ) : ℚ)) : WithTop ℚ) <
                (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
            simpa only [comparisonNext, sourceNext] using hthreshold
          exact hthreshold'.trans_le hsum
      have hlarge := hac.centralRepresentations i htrigger
      have hsmall := c.prefixValues_represents_of_le
        (s - 2) (s - 1) (by omega) (by omega)
      exact hsmall.trans (by simpa only [i] using hlarge)
    · have hsourceLe : a.order sourceNext ≤ c.order comparisonNext :=
        le_of_not_gt hcross
      let i : LongRepresentationIndex (n + 3) (n + 3) :=
        { val := s - 1
          one_lt := by omega
          succ_lt_large := by
            omega
          le_small_succ := by
            omega }
      have htrigger : a.longRepresentationTrigger c i := by
        unfold longRepresentationTrigger
        dsimp only [i]
        constructor
        · rw [dif_pos (show s - 1 ≤ n + 3 by omega)]
          have hsourceIndex :
              (⟨s - 1 + 1, by omega⟩ : Fin (n + 3)) = sourceNext := by
            apply Fin.ext
            dsimp only [sourceNext]
            omega
          have hcomparisonIndex :
              (⟨s - 1 - 1, by omega⟩ : Fin (n + 3)) =
                comparisonNext := by
            apply Fin.ext
            dsimp only [comparisonNext]
            omega
          rw [hsourceIndex, hcomparisonIndex]
          exact hsourceLe
        · constructor
          · have hcomparisonLast' :
                c.order ⟨s - 1 - 2, by omega⟩ =
                  R - 2 * (ramificationIndex K : Int) + 1 := by
              have hindex :
                  (⟨s - 1 - 2, by omega⟩ : Fin (n + 3)) =
                    ⟨s - 3, by omega⟩ := by
                apply Fin.ext
                simp only [Fin.val_mk]
                omega
              rw [hindex]
              exact hcomparisonLast
            have hsourceNext' :
                R + 2 ≤ a.order ⟨s - 1 + 1, by omega⟩ := by
              have hindex :
                  (⟨s - 1 + 1, by omega⟩ : Fin (n + 3)) =
                    sourceNext := by
                apply Fin.ext
                dsimp only [sourceNext]
                omega
              rw [hindex]
              exact hsourceNext
            rw [hcomparisonLast']
            omega
          · have hsourceLast' :
                a.order ⟨s - 1, by omega⟩ =
                  R - 2 * (ramificationIndex K : Int) + 1 := by
              simpa only using hsourceLast
            have hcomparisonLast' :
                c.order ⟨s - 1 - 2, by omega⟩ =
                  R - 2 * (ramificationIndex K : Int) + 1 := by
              have hindex :
                  (⟨s - 1 - 2, by omega⟩ : Fin (n + 3)) =
                    ⟨s - 3, by omega⟩ := by
                apply Fin.ext
                simp only [Fin.val_mk]
                omega
              rw [hindex]
              exact hcomparisonLast
            rw [hsourceLast', hcomparisonLast']
      have hleftLength : i.val - 1 = s - 2 := by
        dsimp only [i]
        omega
      have hrightLength : i.val + 1 = s := by
        dsimp only [i]
        omega
      exact prefixRepresents_cast c a hleftLength hrightLength
        (hac.longRepresentations i htrigger)
  · have hsFull : s = n + 3 := by
      have := D.le_rank
      omega
    have hprefix := c.prefixValues_represents_of_le
      (s - 2) (n + 3) (by omega) le_rfl
    have hrepresented := hprefix.trans (c.fullPrefix_represents a)
    exact prefixRepresents_cast c a rfl hsFull.symm hrepresented

end BONG.GoodBONG

end Bong
