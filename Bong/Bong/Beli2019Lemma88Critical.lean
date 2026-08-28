/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Induction
import Bong.Bong.DiagonalTernaryCore

/-!
# Beli (2019), Lemma 8.8: the critical half-gap configuration

This file treats the residue-two boundary left after the direct binary
branches.  It derives the exact second-alpha and projected-tail identities
used by the exceptional induction, and packages the return from a successful
tail transformation to the binary branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- At the half-gap, the alpha of the first binary prefix is necessarily the
global first alpha. -/
theorem firstBinaryAlpha_eq_alpha_of_halfGap
    (b : GoodBONG q L (N + 2))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1))) :
    b.firstBinaryAlpha =
      (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
  apply le_antisymm
  · unfold firstBinaryAlpha
    calc
      min (b.halfGapCandidate (0 : Fin (N + 1)))
          (b.leftDefectCandidate (0 : Fin (N + 1))
            (0 : Fin (N + 1))) ≤
          b.halfGapCandidate (0 : Fin (N + 1)) := min_le_left _ _
      _ = (b.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
        rw [← b.coe_halfGapValue]
        exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm
  · unfold firstBinaryAlpha
    apply le_min
    · rw [← b.coe_halfGapValue]
      exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf
        |>.le
    · rw [b.coe_alphaValue]
      exact b.alpha_le_leftDefectCandidate le_rfl

/-- If the first alpha attains its half-gap, P1 bounds the second alpha below
by the complementary defect. -/
theorem lemma88ComplementaryDefect_le_secondAlpha_of_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2))) :
    b.lemma88ComplementaryDefect ≤
      b.alphaValue (1 : Fin (N + 2)) := by
  have hmono := b.alphaLeftEndpoint_monotone
    (show (0 : Fin (N + 2)) ≤ (1 : Fin (N + 2)) by
      exact Fin.zero_le _)
  unfold alphaLeftEndpoint at hmono
  unfold AttainsHalfGap halfGapValue orderGap at hhalf
  unfold lemma88ComplementaryDefect
  change
    (b.order (0 : Fin (N + 3)) : ℚ) +
        b.alphaValue (0 : Fin (N + 2)) ≤
      (b.order (1 : Fin (N + 3)) : ℚ) +
        b.alphaValue (1 : Fin (N + 2)) at hmono
  change
    b.alphaValue (0 : Fin (N + 2)) =
      ((b.order (1 : Fin (N + 3)) -
        b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hhalf
  change
    (ramificationIndex K : ℚ) -
        ((b.order (1 : Fin (N + 3)) -
          b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 ≤
      b.alphaValue (1 : Fin (N + 2))
  push_cast at hmono hhalf ⊢
  linarith

/-- In rank at least three, equality of the raw first adjacent defect with
the complementary value also gives equality for the bracketed defect once
the second-alpha lower bound is known. -/
theorem lemma88FirstCappedDefect_eq_complementary
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (hsecond : b.lemma88ComplementaryDefect ≤
      b.alphaValue (1 : Fin (N + 2))) :
    b.lemma88FirstCappedDefect =
      (b.lemma88ComplementaryDefect : WithTop ℚ) := by
  rw [lemma88FirstCappedDefect, truncatedPrefixDefect]
  have hraw :
      defectOrder (K := K)
          ((-1) * b.prefixProduct 0 * b.prefixProduct 2) =
        b.adjacentDefect (0 : Fin (N + 2)) := by
    simpa using
      b.defectOrder_prefixPair_eq_adjacentDefect (0 : Fin (N + 2))
  rw [hraw, b.prefixAlphaCap_zero,
    b.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega)]
  simp only [min_eq_right le_top]
  rw [hadjacent]
  exact min_eq_left (by exact_mod_cast hsecond)

/-- In the critical residue-two configuration, failure of exception (b)
forces the second alpha to equal the complementary defect. -/
theorem secondAlpha_eq_complementary_of_not_exceptionB
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2)))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (hnotB : ¬Nonempty b.Beli2019Lemma88ExceptionB) :
    b.alphaValue (1 : Fin (N + 2)) =
      b.lemma88ComplementaryDefect := by
  have hlower :=
    b.lemma88ComplementaryDefect_le_secondAlpha_of_halfGap hhalf
  have hcapped :=
    b.lemma88FirstCappedDefect_eq_complementary hadjacent hlower
  apply le_antisymm
  · apply le_of_not_gt
    intro hstrict
    apply hnotB
    exact ⟨{
      residueTwo := hresidueTwo
      cappedDefect_eq := hcapped
      nextAlpha_strict := fun _ => hstrict
    }⟩
  · exact hlower

/-- The only alpha candidate at the second index which does not come from
the projected tail is the left candidate based at the first adjacent pair.
In the critical configuration that candidate dominates the tail half-gap;
this is exactly the inequality `R₁ ≤ R₃` from goodness. -/
theorem tailHalfGapCandidate_le_firstLeftDefectCandidate
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    b.tail.halfGapCandidate (0 : Fin (N + 1)) ≤
      b.leftDefectCandidate (1 : Fin (N + 2))
        (0 : Fin (N + 2)) := by
  unfold halfGapCandidate leftDefectCandidate
  simp only [b.order_goodTail]
  rw [hadjacent]
  apply WithTop.coe_le_coe.mpr
  unfold lemma88ComplementaryDefect orderGap
  change
    (((b.order (2 : Fin (N + 3)) -
        b.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) ≤
      ((b.order (2 : Fin (N + 3)) -
          b.order (0 : Fin (N + 3)) : Int) : ℚ) +
        ((ramificationIndex K : ℚ) -
          ((b.order (1 : Fin (N + 3)) -
            b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2)
  have hgood := b.good (⟨0, by omega⟩ : Fin (N + 3)) (by
    change 0 + 2 < N + 3
    omega)
  have hgoodQ :
      (b.order (0 : Fin (N + 3)) : ℚ) ≤
        (b.order (2 : Fin (N + 3)) : ℚ) := by
    exact_mod_cast hgood
  push_cast
  linarith

/-- Under the critical adjacent-defect equality, the first alpha of the
projected tail is no larger than the second alpha of the original BONG. -/
theorem tailAlpha_zero_le_secondAlpha_of_adjacent_eq_complementary
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    (b.tail.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) ≤
      (b.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  rw [b.tail.coe_alphaValue, b.coe_alphaValue]
  change b.tail.alpha (0 : Fin (N + 1)) ≤
    Finset.min' (b.alphaCandidates (1 : Fin (N + 2)))
      (b.alphaCandidates_nonempty (1 : Fin (N + 2)))
  apply Finset.le_min'
  intro y hy
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
  · have htail :=
      b.tail.alpha_le_halfGapCandidate (0 : Fin (N + 1))
    rw [b.halfGapCandidate_tail] at htail
    have hindex : (0 : Fin (N + 1)).succ =
        (1 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex] at htail
    exact htail
  · by_cases hj : j = (0 : Fin (N + 2))
    · subst j
      exact (b.tail.alpha_le_halfGapCandidate (0 : Fin (N + 1))).trans
        (b.tailHalfGapCandidate_le_firstLeftDefectCandidate hadjacent)
    · have hj' : j = (1 : Fin (N + 2)) := by
        apply Fin.ext
        change j.1 = 1
        have := hji
        change j.1 ≤ 1 at this
        have hjpos : 0 < j.1 := by
          by_contra hnot
          have : j.1 = 0 := by omega
          exact hj (Fin.ext this)
        omega
      subst j
      have htail := b.tail.alpha_le_leftDefectCandidate
        (i := (0 : Fin (N + 1))) (j := (0 : Fin (N + 1))) le_rfl
      rw [b.leftDefectCandidate_tail] at htail
      simpa using htail
  · have hjlower : 1 ≤ j.1 := by
      change (1 : Nat) ≤ j.1 at hij
      exact hij
    let jTail : Fin (N + 1) := ⟨j.1 - 1, by omega⟩
    have hsucc : jTail.succ = j := by
      apply Fin.ext
      simp only [jTail, Fin.val_succ]
      omega
    have htail := b.tail.alpha_le_rightDefectCandidate
      (i := (0 : Fin (N + 1))) (j := jTail) (Fin.zero_le _)
    rw [b.rightDefectCandidate_tail] at htail
    rw [hsucc] at htail
    simpa using htail

/-- Combining the preceding inequality with the general head-deletion
inequality gives the exact identity used in the induction proof. -/
theorem tailAlpha_zero_eq_secondAlpha_of_adjacent_eq_complementary
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ)) :
    b.tail.alphaValue (0 : Fin (N + 1)) =
      b.alphaValue (1 : Fin (N + 2)) := by
  apply WithTop.coe_injective
  apply le_antisymm
  · exact b.tailAlpha_zero_le_secondAlpha_of_adjacent_eq_complementary
      hadjacent
  · exact b.alphaValue_shift_le_tail (0 : Fin (N + 1))

/-- General form of the preceding candidate comparison.  The extra
left-defect candidate introduced by restoring the head dominates the
corresponding tail half-gap because adjacent order sums are monotone. -/
theorem tailHalfGapCandidate_le_firstLeftDefectCandidate_at
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (i : Fin (N + 1)) :
    b.tail.halfGapCandidate i ≤
      b.leftDefectCandidate i.succ (0 : Fin (N + 2)) := by
  have hsum := b.adjacentOrderSum_monotone
    (show (0 : Fin (N + 2)) ≤ i.succ by exact Fin.zero_le _)
  unfold adjacentOrderSum at hsum
  unfold halfGapCandidate leftDefectCandidate
  simp only [b.order_goodTail]
  rw [hadjacent]
  apply WithTop.coe_le_coe.mpr
  unfold lemma88ComplementaryDefect orderGap
  have hmiddle : i.castSucc.succ = i.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hmiddle]
  have hsumQ :
      (b.order (0 : Fin (N + 2)).castSucc : ℚ) +
          (b.order (0 : Fin (N + 2)).succ : ℚ) ≤
        (b.order i.succ.castSucc : ℚ) +
          (b.order i.succ.succ : ℚ) := by
    exact_mod_cast hsum
  push_cast
  linarith

/-- Every projected-tail alpha agrees with the next alpha of the original
good BONG in the critical complementary configuration. -/
theorem tailAlpha_eq_shift_of_adjacent_eq_complementary
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (i : Fin (N + 1)) :
    b.tail.alphaValue i = b.alphaValue i.succ := by
  apply WithTop.coe_injective
  apply le_antisymm
  · rw [b.tail.coe_alphaValue, b.coe_alphaValue]
    change b.tail.alpha i ≤
      Finset.min' (b.alphaCandidates i.succ)
        (b.alphaCandidates_nonempty i.succ)
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
    · have htail := b.tail.alpha_le_halfGapCandidate i
      rw [b.halfGapCandidate_tail] at htail
      exact htail
    · by_cases hj : j = (0 : Fin (N + 2))
      · subst j
        exact (b.tail.alpha_le_halfGapCandidate i).trans
          (b.tailHalfGapCandidate_le_firstLeftDefectCandidate_at
            hadjacent i)
      · have hjpos : 0 < j.1 := by
          by_contra hnot
          have : j.1 = 0 := by omega
          exact hj (Fin.ext this)
        let jTail : Fin (N + 1) := ⟨j.1 - 1, by omega⟩
        have hsucc : jTail.succ = j := by
          apply Fin.ext
          simp only [jTail, Fin.val_succ]
          omega
        have hjTailLe : jTail ≤ i := by
          change j.1 - 1 ≤ i.1
          change j.1 ≤ i.succ.1 at hji
          simp only [Fin.val_succ] at hji
          omega
        have htail := b.tail.alpha_le_leftDefectCandidate
          (i := i) (j := jTail) hjTailLe
        rw [b.leftDefectCandidate_tail, hsucc] at htail
        exact htail
    · have hjlower : i.1 + 1 ≤ j.1 := by
        change i.succ.1 ≤ j.1 at hij
        simpa only [Fin.val_succ] using hij
      let jTail : Fin (N + 1) := ⟨j.1 - 1, by omega⟩
      have hsucc : jTail.succ = j := by
        apply Fin.ext
        simp only [jTail, Fin.val_succ]
        omega
      have hiLeTail : i ≤ jTail := by
        change i.1 ≤ j.1 - 1
        omega
      have htail := b.tail.alpha_le_rightDefectCandidate
        (i := i) (j := jTail) hiLeTail
      rw [b.rightDefectCandidate_tail, hsucc] at htail
      exact htail
  · exact b.alphaValue_shift_le_tail i

/-- Consequently the projected-tail alpha itself is the complementary
defect whenever exception (b) is absent in the critical configuration. -/
theorem tailAlpha_zero_eq_complementary_of_not_exceptionB
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2)))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (hnotB : ¬Nonempty b.Beli2019Lemma88ExceptionB) :
    b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect := by
  rw [b.tailAlpha_zero_eq_secondAlpha_of_adjacent_eq_complementary
    hadjacent]
  exact b.secondAlpha_eq_complementary_of_not_exceptionB hhalf
    hresidueTwo hadjacent hnotB

/-- If the projected tail is itself exceptional, its half-gap equality and
the critical complementary alpha identity force `R₁ = R₃`. -/
theorem firstThirdOrders_eq_of_tailExceptional
    (b : GoodBONG q L (N + 3))
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect)
    (htailExceptional : b.tail.Beli2019Lemma88Exceptional) :
    b.order (0 : Fin (N + 3)) = b.order (2 : Fin (N + 3)) := by
  have htailHalf := htailExceptional.1
  unfold AttainsHalfGap halfGapValue orderGap at htailHalf
  simp only [b.order_goodTail] at htailHalf
  change
    b.tail.alphaValue (0 : Fin (N + 1)) =
      ((b.order (2 : Fin (N + 3)) -
        b.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at htailHalf
  unfold lemma88ComplementaryDefect orderGap at htailAlpha
  change
    b.tail.alphaValue (0 : Fin (N + 1)) =
      (ramificationIndex K : ℚ) -
        ((b.order (1 : Fin (N + 3)) -
          b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 at htailAlpha
  have hordersQ : (b.order (0 : Fin (N + 3)) : ℚ) =
      (b.order (2 : Fin (N + 3)) : ℚ) := by
    push_cast at htailHalf htailAlpha ⊢
    linarith
  exact_mod_cast hordersQ

/-- When `R₁ = R₃`, the complementary defect of the projected tail is the
first half-gap of the original good BONG. -/
theorem tailComplementaryDefect_eq_firstHalfGap_of_orders_eq
    (b : GoodBONG q L (N + 3))
    (horders : b.order (0 : Fin (N + 3)) =
      b.order (2 : Fin (N + 3))) :
    b.tail.lemma88ComplementaryDefect =
      b.halfGapValue (0 : Fin (N + 2)) := by
  unfold lemma88ComplementaryDefect halfGapValue orderGap
  simp only [b.order_goodTail]
  change
    (ramificationIndex K : ℚ) -
        ((b.order (2 : Fin (N + 3)) -
          b.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 =
      ((b.order (1 : Fin (N + 3)) -
        b.order (0 : Fin (N + 3)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)
  have hordersQ : (b.order (0 : Fin (N + 3)) : ℚ) =
      (b.order (2 : Fin (N + 3)) : ℚ) := by
    exact_mod_cast horders
  push_cast
  linarith

/-- Hence nontriviality of the adjacent Hilbert symbol proves anisotropy of
the first ternary prefix. -/
theorem firstThreeAnisotropic_of_adjacent_hilbert_ne_one
    (b : GoodBONG q L (N + 3))
    (hne : hilbertSymbol K
      (b.adjacentProduct (0 : Fin (N + 2)))
      (b.adjacentProduct (1 : Fin (N + 2))) ≠ 1) :
    b.Lemma88FirstThreeAnisotropic (by omega) := by
  intro z hquadratic
  by_contra hz
  apply hne
  have hcoefficients :
      (fun i : Fin 3 =>
        ![b.value ⟨0, by omega⟩, b.value ⟨1, by omega⟩,
          b.value ⟨2, by omega⟩] i) =
        b.lemma88FirstThreeValues (by omega) := by
    funext i
    fin_cases i <;> simp [lemma88FirstThreeValues]
  rw [← hcoefficients] at hquadratic
  have hquadraticUnits :
      diagonalQuadratic
        (fun i : Fin 3 =>
          ![(b.valueUnit ⟨0, by omega⟩ : K),
            (b.valueUnit ⟨1, by omega⟩ : K),
            (b.valueUnit ⟨2, by omega⟩ : K)] i) z = 0 := by
    simpa only [coe_valueUnit] using hquadratic
  have hproducts :
      hilbertSymbol K
          (-(b.valueUnit ⟨0, by omega⟩ *
            b.valueUnit ⟨1, by omega⟩))
          (-(b.valueUnit ⟨1, by omega⟩ *
            b.valueUnit ⟨2, by omega⟩)) = 1 := by
    apply hilbertSymbol_eq_one_of_diagonalTernary_isotropic
      (b.valueUnit ⟨0, by omega⟩)
      (b.valueUnit ⟨1, by omega⟩)
      (b.valueUnit ⟨2, by omega⟩) z hz hquadraticUnits
  have htwo : (⟨2, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [htwo] at hproducts
  simpa [adjacentProduct] using hproducts

set_option maxHeartbeats 1200000 in
-- The dependent exception witness makes elaboration of this proof expensive.
/-- Exception (b) for an exceptional projected tail propagates to exception
(c) for the original good BONG.  The two complementary adjacent defects add
to `2e`, so Lemma 8.2(iii) makes the ternary Hilbert symbol nontrivial; the
preceding algebraic equivalence then supplies anisotropy. -/
theorem tailExceptionB_implies_exceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (b : GoodBONG q L (N + 3))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect)
    (htailExceptional : b.tail.Beli2019Lemma88Exceptional)
    (B : b.tail.Beli2019Lemma88ExceptionB) :
    Nonempty b.Beli2019Lemma88ExceptionC := by
  have horders := b.firstThirdOrders_eq_of_tailExceptional
    htailAlpha htailExceptional
  have htailComplement :=
    b.tailComplementaryDefect_eq_firstHalfGap_of_orders_eq horders
  have htailAdjacent :=
    b.tail.adjacentDefect_zero_eq_complementary_of_lemma88ExceptionB B
  have hsecondAdjacent :
      b.adjacentDefect (1 : Fin (N + 2)) =
        (b.halfGapValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    have hshift := b.adjacentDefect_tail (0 : Fin (N + 1))
    rw [htailAdjacent, htailComplement] at hshift
    have hindex : (0 : Fin (N + 1)).succ =
        (1 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex] at hshift
    exact hshift.symm
  have hsum :
      defectOrder (K := K)
          (b.adjacentProduct (0 : Fin (N + 2))) +
          defectOrder (K := K)
            (b.adjacentProduct (1 : Fin (N + 2))) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    change b.adjacentDefect (0 : Fin (N + 2)) +
        b.adjacentDefect (1 : Fin (N + 2)) = _
    rw [hadjacent, hsecondAdjacent]
    exact_mod_cast b.lemma88ComplementaryDefect_add_halfGap
  have hhilbert : hilbertSymbol K
      (b.adjacentProduct (0 : Fin (N + 2)))
      (b.adjacentProduct (1 : Fin (N + 2))) ≠ 1 :=
    hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
      B.residueTwo (b.adjacentProduct (0 : Fin (N + 2)))
        (b.adjacentProduct (1 : Fin (N + 2))) hsum
  let hthree : 3 ≤ N + 3 := by omega
  refine ⟨{
    residueTwo := B.residueTwo
    rank_three := hthree
    outerOrders_eq := horders
    laterAlpha_strict := ?_
    firstThree_anisotropic := ?_
  }⟩
  · intro hfour
    have htailThree : 3 ≤ N + 2 := by omega
    let secondTail : Fin (N + 1) := ⟨1, by omega⟩
    let third : Fin (N + 2) := ⟨2, by omega⟩
    change b.halfGapValue (0 : Fin (N + 2)) < b.alphaValue third
    have hstrictTail : b.tail.lemma88ComplementaryDefect <
        b.tail.alphaValue secondTail :=
      B.nextAlpha_strict htailThree
    have hshift := b.tailAlpha_eq_shift_of_adjacent_eq_complementary
      hadjacent secondTail
    have hindex : secondTail.succ = third := by
      apply Fin.ext
      dsimp only [secondTail, third, Fin.val_succ]
    rw [hindex] at hshift
    calc
      b.halfGapValue (0 : Fin (N + 2)) =
          b.tail.lemma88ComplementaryDefect := htailComplement.symm
      _ < b.tail.alphaValue secondTail := hstrictTail
      _ = b.alphaValue third := hshift
  · exact b.firstThreeAnisotropic_of_adjacent_hilbert_ne_one hhilbert

namespace Beli2019TailReplacementData

variable {b : GoodBONG q L (N + 3)}

/-- In residue cardinality two, a tail multiplier having the same finite
defect as the first adjacent product strictly raises their product defect.
Thus a successful tail transformation breaks the critical complementary
equality. -/
theorem complementary_lt_firstAdjacentDefect
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    (D : b.Beli2019TailReplacementData)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect) :
    (b.lemma88ComplementaryDefect : WithTop ℚ) <
      D.transformed.adjacentDefect (0 : Fin (N + 2)) := by
  have hepsilon : defectOrder (K := K) D.epsilon =
      (b.lemma88ComplementaryDefect : WithTop ℚ) := by
    exact D.epsilon_defect.trans
      (congrArg (fun x : ℚ => (x : WithTop ℚ)) htailAlpha)
  have hadjacentOrder :
      defectOrder (K := K)
          (b.adjacentProduct (0 : Fin (N + 2))) =
        (b.lemma88ComplementaryDefect : WithTop ℚ) := by
    exact hadjacent
  have hquadraticEq : quadraticDefect K D.epsilon =
      quadraticDefect K (b.adjacentProduct (0 : Fin (N + 2))) :=
    quadraticDefect_eq_of_defectOrder_eq D.epsilon
      (b.adjacentProduct (0 : Fin (N + 2)))
      (hepsilon.trans hadjacentOrder.symm)
  have hfinite : quadraticDefect K D.epsilon ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe D.epsilon
      b.lemma88ComplementaryDefect hepsilon
  have hstrictRaw := beli2019Lemma81_ii_strict hresidueTwo D.epsilon
    (b.adjacentProduct (0 : Fin (N + 2))) hquadraticEq hfinite
  have hstrict := defectOrder_lt_of_quadraticDefect_lt D.epsilon
    (D.epsilon * b.adjacentProduct (0 : Fin (N + 2))) hstrictRaw
  unfold adjacentDefect
  rw [D.firstAdjacentProduct_eq, ← hepsilon]
  exact hstrict

end Beli2019TailReplacementData

/-- The completed successful-tail subcase of the critical half-gap
induction.  Lemma 8.1(ii) destroys the complementary adjacent-defect
equality after splicing the tail transform, the direct half-gap binary
theorem then applies, and the resulting transformation is composed back to
the original good BONG. -/
theorem beli2019Lemma88_critical_of_tailTransform
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2)))
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hadjacent : b.adjacentDefect (0 : Fin (N + 2)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ))
    (hnotA : ¬b.Beli2019Lemma88ExceptionA)
    (hnotB : ¬Nonempty b.Beli2019Lemma88ExceptionB)
    (T : b.tail.Beli2019FirstValueTransform) :
    Nonempty b.Beli2019FirstValueTransform := by
  have htailAlpha :=
    b.tailAlpha_zero_eq_complementary_of_not_exceptionB hhalf
      hresidueTwo hadjacent hnotB
  rcases b.tailReplacementData_of_firstValueTransform T with ⟨D⟩
  have hstrictAdjacent := D.complementary_lt_firstAdjacentDefect
    hresidueTwo hadjacent htailAlpha
  have halphas := b.alpha_invariant D.transformed
  have horders := b.order_invariant D.transformed
  have hhalfValue :
      D.transformed.halfGapValue (0 : Fin (N + 2)) =
        b.halfGapValue (0 : Fin (N + 2)) := by
    unfold halfGapValue orderGap
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc]
  have hhalfTransformed :
      D.transformed.AttainsHalfGap (0 : Fin (N + 2)) := by
    unfold AttainsHalfGap
    rw [← halphas (0 : Fin (N + 2)), hhalfValue]
    exact hhalf
  have hcomp : D.transformed.lemma88ComplementaryDefect =
      b.lemma88ComplementaryDefect := by
    unfold lemma88ComplementaryDefect orderGap
    rw [← horders (0 : Fin (N + 2)).succ,
      ← horders (0 : Fin (N + 2)).castSucc]
  have hadjacentNe :
      D.transformed.adjacentDefect (0 : Fin (N + 2)) ≠
        (D.transformed.lemma88ComplementaryDefect : WithTop ℚ) := by
    rw [hcomp]
    exact ne_of_gt hstrictAdjacent
  have hrealized : IsValuationUnitDefect (K := K)
      (b.alphaValue (0 : Fin (N + 2))) := by
    by_contra hnot
    exact hnotA hnot
  rcases hrealized with ⟨reference, hrefUnit, hrefDefect⟩
  have hrefDefectTransformed : defectOrder (K := K) reference =
      (D.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) :=
    hrefDefect.trans (congrArg (fun x : ℚ => (x : WithTop ℚ))
      (halphas (0 : Fin (N + 2))))
  have hbinary :=
    D.transformed.firstBinaryAlpha_eq_alpha_of_halfGap hhalfTransformed
  rcases
      D.transformed.beli2019Lemma88_halfGap_binary_of_adjacent_ne_complementary
        reference hrefUnit hrefDefectTransformed hbinary hhalfTransformed
          hadjacentNe with ⟨S⟩
  exact ⟨D.compose_firstValueTransform S⟩

end BONG.GoodBONG

end Bong
