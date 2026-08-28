/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Current
import Bong.Bong.Beli2019Lemma214Previous
import Bong.Bong.Beli2019SectionFourCentralParity

/-!
# Beli (2019), Section 4: both central alphas attain their half gaps

This file formalizes the first case in the proof of Theorem 2.1(iii).
When both adjusted alphas are strictly larger than their unprimed versions,
Lemma 2.14 activates the two adjacent prefix representations.  Their two
half-gap values have sum strictly larger than `2e`, so Lemma 1.5(i) supplies
the required outer representation.
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

/-- Lemma 2.14 supplies the `(a,b)` representation at the central boundary
when `A_i` is strictly below `A'_i`. -/
theorem middlePrevious_represents_of_current_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hne : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le)) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) := by
  apply hab.centralRepresentations i
  exact a.centralAlphaTrigger_of_current_alpha_ne_prime b le_rfl
    hab.orderCondition hab.defectCondition i i.lt_large.le hne

/-- Lemma 2.14 supplies the `(b,c)` representation at the central boundary
when `B_(i-1)` is strictly below `B'_(i-1)`. -/
theorem sourceCurrent_represents_of_previous_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 1)) (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hne : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (b.prefixValues i.val i.current_le_sameRank) := by
  apply hbc.centralRepresentations i
  exact b.centralAlphaTrigger_of_previous_alpha_ne_prime c le_rfl
    hbc.orderCondition hbc.defectCondition i i.lt_large.le hne

/-- The same strict inequality also activates condition (iii) one boundary
earlier.  At the lower endpoint `i = 2`, its source prefix is empty and the
representation is vacuous, exactly as stipulated in the paper. -/
theorem sourcePrevious_represents_of_previous_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 1)) (c : GoodBONG q N (n + 1))
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hne : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 2) (by
        have := i.lt_large
        omega))
      (b.prefixValues (i.val - 1) i.previous_le_sameRank) := by
  by_cases hi : i.val = 2
  · exact DiagonalRepresents.of_source_length_eq_zero
      (c.prefixValues (i.val - 2) (by
        have := i.lt_large
        omega))
      (b.prefixValues (i.val - 1) i.previous_le_sameRank) (by omega)
  · let j : CentralRepresentationIndex (n + 1) (n + 1) :=
      { val := i.val - 1
        one_lt := by
          have := i.one_lt
          omega
        lt_large := by
          have := i.lt_large
          omega
        le_small_succ := by
          have := i.le_small_succ
          omega }
    have hjSmall : j.val ≤ n + 1 := by
      dsimp only [j]
      have := i.lt_large
      omega
    have hne' : b.representationAlpha c (j.current hjSmall) ≠
        b.representationAlphaPrime c (j.current hjSmall) := by
      simpa only [j, CentralRepresentationIndex.current,
        CentralRepresentationIndex.previous] using hne
    have htrigger := b.centralAlphaTrigger_of_current_alpha_ne_prime
      c le_rfl hbc.orderCondition hbc.defectCondition j hjSmall hne'
    have hrep := hbc.centralRepresentations j htrigger
    have hsub : i.val - 1 - 1 = i.val - 2 := by omega
    exact prefixRepresents_cast c b hsub rfl (by
      simpa only [j] using hrep)

/-- The two exact half gaps telescope.  The outer strict order comparison
therefore makes their sum strictly larger than `2e`. -/
theorem twoE_lt_current_previous_halfGap_sum
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (hcross : c.order ⟨i.val - 2, by
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      a.representationHalfGap b (i.current i.lt_large.le) +
        b.representationHalfGap c i.previous := by
  have hcrossQ :
      (c.order ⟨i.val - 2, by
        have := i.le_small_succ
        omega⟩ : ℚ) < (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcross
  simp only [representationHalfGap, CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous, Nat.sub_sub, one_add_one_eq_two]
  norm_cast
  simp only [Rat.divInt_eq_div]
  push_cast at hcrossQ ⊢
  norm_num [div_eq_mul_inv] at hcrossQ ⊢
  have hpositive : (0 : ℚ) <
      ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
        (c.order ⟨i.val - 2, by
          have := i.le_small_succ
          omega⟩ : ℚ)) / 2 := by
    apply div_pos
    · apply sub_pos.mpr
      exact_mod_cast hcross
    · norm_num
  ring_nf at ⊢
  linarith

/-- The first parity diagram closes the case in which both relevant
unprimed alphas attain their half-gap candidates. -/
theorem sectionFourCentralCertificate_of_both_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i)
    (hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le))
    (hneBC : b.representationAlpha c i.previous ≠
      b.representationAlphaPrime c i.previous) :
    CentralRepresentationCertificate a b c i := by
  have hmiddle := a.middlePrevious_represents_of_current_alpha_ne_prime
    b hab i hneAB
  have hsource := b.sourceCurrent_represents_of_previous_alpha_ne_prime
    c hbc i hneBC
  apply CentralRepresentationCertificate.of_caseI_truncatedDefects
    hmiddle hsource
  have habBound := hab.defectCondition (i.current i.lt_large.le)
  have hbcBound := hbc.defectCondition i.previous
  have hAlphaAB :=
    (a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      b (i.current i.lt_large.le) hneAB).1
  have hAlphaBC :=
    (b.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      c i.previous hneBC).1
  rw [a.coe_representationAlphaValue b (i.current i.lt_large.le),
    hAlphaAB] at habBound
  rw [b.coe_representationAlphaValue c i.previous, hAlphaBC] at hbcBound
  have hhalf := a.twoE_lt_current_previous_halfGap_sum b c i htrigger.1
  apply hhalf.trans_le
  simpa only [CentralRepresentationIndex.current,
    CentralRepresentationIndex.previous] using add_le_add habBound hbcBound

end BONG.GoodBONG

end Bong
