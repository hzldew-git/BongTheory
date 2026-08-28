/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EqualRank
import Bong.Bong.Beli2019Remark87
import Bong.Bong.Beli2019FullRankDefect
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.Beli2009ClassificationPropagation

/-!
# Beli (2019), Lemma 9.4

For ternary lattices in one quadratic space whose first and third good-BONG
orders all agree, the four conditions of Theorem 2.1 are equivalent to the
two endpoint alpha inequalities.  In the paper the four-condition relation
is denoted by `N ≤ M`; here it is kept explicit as `RepresentationConditions`
so that this lemma does not use the main theorem whose sufficiency proof it
helps complete.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- At the first ternary boundary, the mixed capped prefix defect is at
least the target's first alpha when the target alpha is no larger than the
source alpha. -/
private theorem lemma94_firstPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order 0 = a.order 2)
    (houterB : b.order 0 = b.order 2)
    (hfirstAlpha : a.alphaValue 0 ≤ b.alphaValue 0) :
    (a.alphaValue 0 : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 1 1 := by
  have hlocalA := a.alpha_pair_le_adjacentDefects 0 (by omega) houterA
  have hlocalB := b.alpha_pair_le_adjacentDefects 0 (by omega) houterB
  have hbaseFull : comparisonPrefixDefect a b 3 = ⊤ := by
    unfold comparisonPrefixDefect comparisonPrefixUnit
    rw [a.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl,
      b.prefixProduct_eq_valueProduct_of_rank_le 3 le_rfl,
      a.defectOrder_fullPrefixProduct_mul_eq_top b]
  have hfull : (a.alphaValue 0 : WithTop ℚ) ≤
      comparisonPrefixDefect a b 3 := by
    rw [hbaseFull]
    exact le_top
  have htarget : (a.alphaValue 0 : WithTop ℚ) ≤
      b.adjacentDefect 1 := by
    have hfirstAlpha' : (a.alphaValue 0 : WithTop ℚ) ≤
        (b.alphaValue 0 : WithTop ℚ) := by
      exact_mod_cast hfirstAlpha
    exact hfirstAlpha'.trans hlocalB.2
  have hraw : (a.alphaValue 0 : WithTop ℚ) ≤
      comparisonPrefixDefect a b 1 :=
    (le_min hfull (le_min hlocalA.2 htarget)).trans
      (comparisonPrefixDefect_reverse_add_two a b 1 (by omega))
  unfold truncatedPrefixDefect
  apply le_min
  · simpa only [one_mul, comparisonPrefixDefect, comparisonPrefixUnit]
      using hraw
  · apply le_min
    · rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      exact le_rfl
    · rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
      simpa using (show (a.alphaValue 0 : WithTop ℚ) ≤
        (b.alphaValue 0 : WithTop ℚ) by exact_mod_cast hfirstAlpha)

/-- At the second ternary boundary, the mixed capped prefix defect is at
least the source's second alpha when that alpha is no larger than the
target alpha. -/
private theorem lemma94_secondPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order 0 = a.order 2)
    (houterB : b.order 0 = b.order 2)
    (hsecondAlpha : b.alphaValue 1 ≤ a.alphaValue 1) :
    (b.alphaValue 1 : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 2 2 := by
  have hlocalA := a.alpha_pair_le_adjacentDefects 0 (by omega) houterA
  have hlocalB := b.alpha_pair_le_adjacentDefects 0 (by omega) houterB
  have hbaseZero : comparisonPrefixDefect a b 0 = ⊤ :=
    comparisonPrefixDefect_zero a b
  have hzero : (b.alphaValue 1 : WithTop ℚ) ≤
      comparisonPrefixDefect a b 0 := by
    rw [hbaseZero]
    exact le_top
  have hsource : (b.alphaValue 1 : WithTop ℚ) ≤
      a.adjacentDefect 0 := by
    have hsecondAlpha' : (b.alphaValue 1 : WithTop ℚ) ≤
        (a.alphaValue 1 : WithTop ℚ) := by
      exact_mod_cast hsecondAlpha
    exact hsecondAlpha'.trans hlocalA.1
  have hraw : (b.alphaValue 1 : WithTop ℚ) ≤
      comparisonPrefixDefect a b 2 :=
    (le_min hzero (le_min hsource hlocalB.1)).trans
      (comparisonPrefixDefect_add_two a b 0 (by omega))
  unfold truncatedPrefixDefect
  apply le_min
  · simpa only [one_mul, comparisonPrefixDefect, comparisonPrefixUnit]
      using hraw
  · apply le_min
    · rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      simpa using (show (b.alphaValue 1 : WithTop ℚ) ≤
        (a.alphaValue 1 : WithTop ℚ) by exact_mod_cast hsecondAlpha)
    · rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
      exact le_rfl

/-- Beli (2019), Lemma 9.4.  The hypotheses spell out
`R₁ = R₃`, `S₁ = S₃`, and `R₁ = S₁`; together they are the paper's
`R₁ = R₃ = S₁ = S₃`. -/
theorem beli2019Lemma94
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG q M 3)
    (houterA : a.order 0 = a.order 2)
    (houterB : b.order 0 = b.order 2)
    (hfirstOrder : a.order 0 = b.order 0) :
    RepresentationConditions a b (Nat.le_refl 2) ↔
      a.alphaValue 0 ≤ b.alphaValue 0 ∧
        b.alphaValue 1 ≤ a.alphaValue 1 := by
  have hlastOrder : a.order 2 = b.order 2 :=
    houterA.symm.trans (hfirstOrder.trans houterB)
  let remarkA := a.beli2019Remark87 (0 : Fin 1) houterA
  let remarkB := b.beli2019Remark87 (0 : Fin 1) houterB
  constructor
  · intro conditions
    have hweight := a.weightSequence_le_of_representationConditions b
      conditions.orderCondition conditions.defectCondition
    have hfirstWeight := hweight.first_le (by omega)
    have hfirstWeight' :
        (a.order 0 : ℚ) + a.alphaValue 0 ≤
          (b.order 0 : ℚ) + b.alphaValue 0 := by
      change a.weightSequence.value ⟨0, by omega⟩ ≤
        b.weightSequence.value ⟨0, by omega⟩ at hfirstWeight
      have hindex : (⟨0, by omega⟩ : Fin 4) =
          ⟨2 * (0 : Fin 2).val, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hindex, a.weightSequence_even, b.weightSequence_even]
        at hfirstWeight
      exact hfirstWeight
    have hfirst : a.alphaValue 0 ≤ b.alphaValue 0 := by
      have horder : (a.order 0 : ℚ) = (b.order 0 : ℚ) := by
        exact_mod_cast hfirstOrder
      linarith
    have hlastWeight :
        a.weightSequence.entry 3 (by omega) ≤
          b.weightSequence.entry 3 (by omega) := by
      rcases hweight.compare 3 (by omega) with h | ⟨_, hnext, _⟩
      · exact h
      · omega
    have hlastWeight' :
        (a.order 2 : ℚ) - a.alphaValue 1 ≤
          (b.order 2 : ℚ) - b.alphaValue 1 := by
      change a.weightSequence.value ⟨3, by omega⟩ ≤
        b.weightSequence.value ⟨3, by omega⟩ at hlastWeight
      have hindex : (⟨3, by omega⟩ : Fin 4) =
          ⟨2 * (1 : Fin 2).val + 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hindex, a.weightSequence_odd, b.weightSequence_odd]
        at hlastWeight
      exact hlastWeight
    have hsecond : b.alphaValue 1 ≤ a.alphaValue 1 := by
      have horder : (a.order 2 : ℚ) = (b.order 2 : ℚ) := by
        exact_mod_cast hlastOrder
      linarith
    exact ⟨hfirst, hsecond⟩
  · rintro ⟨hfirstAlpha, hsecondAlpha⟩
    have hmiddleOrder : a.order 1 ≤ b.order 1 := by
      have ha : a.alphaValue 1 =
          ((a.order 0 - a.order 1 : Int) : ℚ) + a.alphaValue 0 := by
        simpa [remark87CurrentAlpha, remark87PreviousValue,
          remark87MiddleValue, remark87PreviousAlpha] using
            remarkA.currentAlpha_eq
      have hb : b.alphaValue 1 =
          ((b.order 0 - b.order 1 : Int) : ℚ) + b.alphaValue 0 := by
        simpa [remark87CurrentAlpha, remark87PreviousValue,
          remark87MiddleValue, remark87PreviousAlpha] using
            remarkB.currentAlpha_eq
      have horder : (a.order 0 : ℚ) = (b.order 0 : ℚ) := by
        exact_mod_cast hfirstOrder
      push_cast at ha hb
      have hmiddleOrderQ : (a.order 1 : ℚ) ≤ (b.order 1 : ℚ) := by
        linarith
      exact_mod_cast hmiddleOrderQ
    have hfirstDefect := lemma94_firstPrefixDefect a b houterA houterB
      hfirstAlpha
    have hsecondDefect := lemma94_secondPrefixDefect a b houterA houterB
      hsecondAlpha
    have hfirstSelf :
        a.truncatedPrefixDefect b (-1) 2 0 =
          (a.alphaValue 1 : WithTop ℚ) := by
      calc
        a.truncatedPrefixDefect b (-1) 2 0 =
            a.truncatedPrefixDefect a (-1) 2 0 :=
          a.truncatedPrefixDefect_zero_right_eq_self b (-1) 2
        _ = a.truncatedPrefixDefect a (-1) 0 2 :=
          a.truncatedPrefixDefect_comm a (-1) 2 0
        _ = (a.alphaValue 1 : WithTop ℚ) :=
          remarkA.previousCappedDefect_eq
    have hsecondSelf :
        a.truncatedPrefixDefect b (-1) 3 1 =
          (b.alphaValue 0 : WithTop ℚ) := by
      calc
        a.truncatedPrefixDefect b (-1) 3 1 =
            b.truncatedPrefixDefect b (-1) 3 1 :=
          b.truncatedPrefixDefect_fullLeft_invariant a b (-1) 1
        _ = b.truncatedPrefixDefect b (-1) 1 3 :=
          b.truncatedPrefixDefect_comm b (-1) 3 1
        _ = (b.alphaValue 0 : WithTop ℚ) :=
          remarkB.currentCappedDefect_eq
    have hprimaryFirst :
        a.representationPrimaryDefect b
            (⟨1, by omega, by omega, by omega⟩ :
              RepresentationIndex 3 3) =
          (a.alphaValue 0 : WithTop ℚ) := by
      unfold representationPrimaryDefect
      simp only [hfirstSelf]
      have ha : a.alphaValue 1 =
          ((a.order 0 - a.order 1 : Int) : ℚ) + a.alphaValue 0 := by
        simpa [remark87CurrentAlpha, remark87PreviousValue,
          remark87MiddleValue, remark87PreviousAlpha] using
            remarkA.currentAlpha_eq
      have horder : (a.order 0 : ℚ) = (b.order 0 : ℚ) := by
        exact_mod_cast hfirstOrder
      norm_cast
      push_cast at ha ⊢
      linarith
    have hprimarySecond :
        a.representationPrimaryDefect b
            (⟨2, by omega, by omega, by omega⟩ :
              RepresentationIndex 3 3) =
          (b.alphaValue 1 : WithTop ℚ) := by
      unfold representationPrimaryDefect
      simp only [hsecondSelf]
      have hb : b.alphaValue 1 =
          ((b.order 0 - b.order 1 : Int) : ℚ) + b.alphaValue 0 := by
        simpa [remark87CurrentAlpha, remark87PreviousValue,
          remark87MiddleValue, remark87PreviousAlpha] using
            remarkB.currentAlpha_eq
      have horder : (a.order 2 : ℚ) = (b.order 0 : ℚ) := by
        exact_mod_cast houterA.symm.trans hfirstOrder
      norm_cast
      push_cast at hb ⊢
      linarith
    refine
      { orderCondition := ?_
        defectCondition := ?_
        centralRepresentations := ?_
        longRepresentations := ?_ }
    · intro i
      fin_cases i
      · exact Or.inl hfirstOrder.le
      · exact Or.inl hmiddleOrder
      · exact Or.inl hlastOrder.le
    · intro i
      have hi : i.val = 1 ∨ i.val = 2 := by
        have := i.pos
        have := i.lt_large
        omega
      rcases hi with hi | hi
      · have hieq : i =
            (⟨1, by omega, by omega, by omega⟩ :
              RepresentationIndex 3 3) := by
          cases i
          simp_all
        rw [hieq]
        calc
          (a.representationAlphaValue b
              (⟨1, by omega, by omega, by omega⟩ :
                RepresentationIndex 3 3) : WithTop ℚ) =
              a.representationAlpha b
                (⟨1, by omega, by omega, by omega⟩ :
                  RepresentationIndex 3 3) :=
            a.coe_representationAlphaValue b _
          _ ≤ a.representationPrimaryDefect b _ :=
            a.representationAlpha_le_primary b _
          _ = (a.alphaValue 0 : WithTop ℚ) := hprimaryFirst
          _ ≤ a.truncatedPrefixDefect b 1 1 1 := hfirstDefect
      · have hieq : i =
            (⟨2, by omega, by omega, by omega⟩ :
              RepresentationIndex 3 3) := by
          cases i
          simp_all
        rw [hieq]
        calc
          (a.representationAlphaValue b
              (⟨2, by omega, by omega, by omega⟩ :
                RepresentationIndex 3 3) : WithTop ℚ) =
              a.representationAlpha b
                (⟨2, by omega, by omega, by omega⟩ :
                  RepresentationIndex 3 3) :=
            a.coe_representationAlphaValue b _
          _ ≤ a.representationPrimaryDefect b _ :=
            a.representationAlpha_le_primary b _
          _ = (b.alphaValue 1 : WithTop ℚ) := hprimarySecond
          _ ≤ a.truncatedPrefixDefect b 1 2 2 := hsecondDefect
    · intro i htrigger
      have hi : i.val = 2 := by
        have := i.one_lt
        have := i.lt_large
        omega
      have hleftIndex :
          (⟨i.val - 2, by omega⟩ : Fin 3) = (0 : Fin 3) := by
        apply Fin.ext
        simp [hi]
      have hrightIndex :
          (⟨i.val, by omega⟩ : Fin 3) = (2 : Fin 3) := by
        apply Fin.ext
        simp [hi]
      have heq : b.order 0 = a.order 2 :=
        houterB.trans hlastOrder.symm
      have hlt := htrigger.1
      rw [hleftIndex, hrightIndex, heq] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro i
      have := i.one_lt
      have := i.succ_lt_large
      omega

end BONG.GoodBONG

end Bong
