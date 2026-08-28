/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93Corollary811
import Bong.Bong.Beli2019Lemma93LowCandidates
import Bong.Bong.Beli2019Lemma91SecondOrder

/-!
# Beli (2019), Lemma 9.3: ordinary Case 1

Corollary 8.11 gives every source-side head-deletion alpha equality, whereas
Lemma 9.2 gives the target-side equalities from the third tail boundary on.
This asymmetric information already transports every comparison alpha after
the first two tail boundaries.  Thus the remaining arithmetic in Case 1 is
exactly the paper's analysis of `A₂` and `A₃`.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n N : Nat}

private theorem representationIndex_eq_of_val_eq_caseOne
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- Mixed primary-candidate transport: later target equalities and all source
equalities suffice from the second tail boundary onward. -/
theorem representationPrimaryDefect_tail_eq_shift_of_targetLater_sourceAll
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 1 < i.val) :
    a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b i.tailShift := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 1) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq
    halphaB (i.val - 1) (by omega) (by omega)
  have hdefect := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    b hhead (-1) (i.val + 1) (i.val - 1) (by omega) (by omega)
      hcapA hcapB
  unfold representationPrimaryDefect
  rw [a.order_goodTail, b.order_goodTail]
  have htarget : i.val + 1 + 1 = i.tailShift.val + 1 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 1 + 1 = i.tailShift.val - 1 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourceIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, hsourceIndex, ← hdefect]

/-- Mixed secondary-candidate transport.  The source endpoint is positive
from the third tail boundary onward, while the target endpoint is already in
the range normalized by Lemma 9.2. -/
theorem representationSecondaryDefect_tail_eq_shift_of_targetLater_sourceAll
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 2 < i.val) (hinterior : i.val + 1 < n + 1) :
    a.tail.representationSecondaryDefect b.tail i
        ⟨by omega, hinterior⟩ =
      a.representationSecondaryDefect b i.tailShift
        ⟨by
          change 1 < i.val + 1
          omega,
         by
          change i.val + 1 + 1 < n + 2
          omega⟩ := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 2) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq
    halphaB (i.val - 2) (by omega) (by omega)
  have hdefect := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    b hhead 1 (i.val + 2) (i.val - 2) (by omega) (by omega)
      hcapA hcapB
  unfold representationSecondaryDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  have htarget : i.val + 2 + 1 = i.tailShift.val + 2 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val - 2 + 1 = i.tailShift.val - 2 := by
    simp only [RepresentationIndex.tailShift_val]
    omega
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have htargetNextIndex :
      (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex :
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex,
    hsourceIndex, ← hdefect]

/-- Mixed transport for Lemma 2.7(ii)'s current-form secondary candidate.
At the second tail boundary the target cap is already in Lemma 9.2's later
range, while Corollary 8.11 supplies the source cap at the remaining early
prefix. -/
theorem representationSecondaryCurrentDefect_tail_eq_shift_of_targetLater_sourceAll
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1) :
    a.tail.representationSecondaryCurrentDefect b.tail i hi =
      a.representationSecondaryCurrentDefect b i.tailShift
        ⟨by
          change 1 < i.val + 1
          omega,
         by
          change i.val + 1 + 1 < n + 2
          omega⟩ := by
  have hilarge := i.lt_large
  have hcapA := a.prefixAlphaCap_shift_eq_tail_of_laterAlphaValue_eq
    halphaA (i.val + 2) (by omega) (by omega)
  have hcapB := b.prefixAlphaCap_shift_eq_tail_of_alphaValue_eq
    halphaB i.val (by omega) (by omega)
  have hdefect := a.truncatedPrefixDefect_shift_eq_tail_of_caps_eq
    b hhead (-1) (i.val + 2) i.val (by omega) (by omega)
      hcapA hcapB
  unfold representationSecondaryCurrentDefect
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  have htarget : i.val + 2 + 1 = i.tailShift.val + 2 := by
    simp only [RepresentationIndex.tailShift_val]
  have hsource : i.val + 1 = i.tailShift.val := by
    simp only [RepresentationIndex.tailShift_val]
  rw [htarget, hsource] at hdefect
  have htargetIndex : (⟨i.val, by omega⟩ : Fin (n + 1)).succ =
      (⟨i.tailShift.val, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have htargetNextIndex :
      (⟨i.val + 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
  have hsourcePreviousIndex :
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  have hsourceIndex :
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)).succ =
        (⟨i.tailShift.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [RepresentationIndex.tailShift_val, Fin.val_succ]
    omega
  rw [htargetIndex, htargetNextIndex, hsourcePreviousIndex,
    hsourceIndex, ← hdefect]

/-- At the second comparison boundary, current essentiality is precisely the
strict cross inequality needed by Lemma 2.7(i). -/
theorem order_head_lt_third_of_currentEssential_second
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (h : a.IsCurrentEssential b
      (secondRepresentationIndex N (N + 1))) :
    b.order (0 : Fin (N + 3)) < a.order (2 : Fin (N + 3)) := by
  unfold IsCurrentEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at h
  have hcross := h.1 (by
    simp only [currentEssentialIndex, secondRepresentationIndex]
    omega) (by
    simp only [currentEssentialIndex, secondRepresentationIndex]
    omega)
  simp only [orderSequence_at, currentEssentialIndex,
    secondRepresentationIndex] at hcross
  have hzero : (⟨2 - 1 - 1, by omega⟩ : Fin (N + 3)) =
      (0 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have htwo : (⟨2 - 1 + 1, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    change 2 - 1 + 1 = 2 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hzero, htwo] at hcross
  exact hcross

/-- At the second comparison boundary, next essentiality gives the strict
cross inequality used by Lemma 2.7(ii). -/
theorem order_second_lt_fourth_of_nextEssential_second
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hN : 0 < N)
    (h : a.IsNextEssential b
      (secondRepresentationIndex N (N + 1))) :
    b.order (1 : Fin (N + 3)) < a.order (3 : Fin (N + 3)) := by
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at h
  have hcross := h.1 (by
    simp only [nextEssentialIndex, secondRepresentationIndex]
    omega) (by
    simp only [nextEssentialIndex, secondRepresentationIndex]
    omega)
  simp only [orderSequence_at, nextEssentialIndex,
    secondRepresentationIndex] at hcross
  have hone : (⟨2 - 1, by omega⟩ : Fin (N + 3)) =
      (1 : Fin (N + 3)) := by
    apply Fin.ext
    change 2 - 1 = 1 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hthree : (⟨2 + 1, by omega⟩ : Fin (N + 3)) =
      (3 : Fin (N + 3)) := by
    apply Fin.ext
    change 2 + 1 = 3 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hone, hthree] at hcross
  exact hcross

set_option maxHeartbeats 800000 in
-- The dependent candidate indices and two asymmetric cap hypotheses make
-- elaboration of the combined minimum identity substantially more expensive.
/-- In Corollary 8.11's branch, comparison alphas are transported exactly at
every tail boundary after the first two. -/
theorem representationAlpha_tail_eq_shift_of_targetLater_sourceAll
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin n, 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin n,
      b.alphaValue k.succ = b.tail.alphaValue k)
    (i : RepresentationIndex (n + 1) (n + 1)) (hi : 2 < i.val) :
    a.tail.representationAlpha b.tail i =
      a.representationAlpha b i.tailShift := by
  rw [a.tail.representationAlpha_eq_min_halfGap_prime b.tail i,
    a.representationAlpha_eq_min_halfGap_prime b i.tailShift,
    a.representationHalfGap_tail_eq_shift b i]
  by_cases hinterior : i.val + 1 < n + 1
  · have htailInterior : 1 < i.val ∧ i.val + 1 < n + 1 :=
      ⟨by omega, hinterior⟩
    have horiginalInterior :
        1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2 := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_min_primary_secondary
        b.tail i htailInterior,
      a.representationAlphaPrime_eq_min_primary_secondary
        b i.tailShift horiginalInterior,
      a.representationPrimaryDefect_tail_eq_shift_of_targetLater_sourceAll
        b hhead halphaA halphaB i (by omega)]
    congr 2
    exact
      a.representationSecondaryDefect_tail_eq_shift_of_targetLater_sourceAll
        b hhead halphaA halphaB i hi hinterior
  · have htailEndpoint :
        ¬(1 < i.val ∧ i.val + 1 < n + 1) := by omega
    have horiginalEndpoint :
        ¬(1 < i.tailShift.val ∧ i.tailShift.val + 1 < n + 2) := by
      simp only [RepresentationIndex.tailShift_val]
      omega
    rw [a.tail.representationAlphaPrime_eq_primary_of_not_interior
        b.tail i htailEndpoint,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b i.tailShift horiginalEndpoint,
      a.representationPrimaryDefect_tail_eq_shift_of_targetLater_sourceAll
        b hhead halphaA halphaB i (by omega)]

/-- The capped-defect identity at the start of Case 1's low-defect
subcase:
`d[-a_(1,3)b_1] = min {d*[-a_(2,3)], α_3, β_1}`.

Deleting equal heads preserves the raw defect.  The extra cap occurring in
the tail defect can be discarded because the general head-deletion
inequality gives `α_3 ≤ α_3*`. -/
theorem firstThirdDefect_eq_min_tail_alpha_three_beta_one
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hhead : a.value 0 = b.value 0) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      min (a.tail.truncatedPrefixDefect b.tail (-1) 2 0)
        (min (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
          (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)) := by
  have halpha :
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
        (a.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    simpa using a.alphaValue_shift_le_tail (1 : Fin (N + 2))
  unfold truncatedPrefixDefect
  rw [a.defectOrder_shiftedPrefixes_eq_tail b hhead (-1) 2 0
      (by omega) (by omega),
    a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega),
    b.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega),
    a.tail.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega),
    b.tail.prefixAlphaCap_zero]
  have htwo : (⟨3 - 1, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    change 2 = 2 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hzero : (⟨1 - 1, by omega⟩ : Fin (N + 3)) =
      (0 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hone : (⟨2 - 1, by omega⟩ : Fin (N + 2)) =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    change 1 = 1 % (N + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [htwo, hzero, hone]
  simp only [min_top_right]
  apply le_antisymm
  · apply le_min
    · apply le_min
      · exact min_le_left _ _
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans halpha
    · exact min_le_right _ _
  · apply le_min
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_right _ _

set_option maxHeartbeats 800000 in
/-- If deleting the head strictly raises the third alpha, the lost first
left-defect candidate attains that alpha.  Endpoint monotonicity then gives
the paper's identity `α₃ = R₄ - R₂ + α₁`. -/
theorem thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hstrict :
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
        (a.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ)) :
    a.alphaValue (2 : Fin (N + 3)) =
      ((a.order (3 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
        a.alphaValue (0 : Fin (N + 3)) := by
  have htwoSucc : (1 : Fin (N + 2)).succ =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    change 1 % (N + 2) + 1 = 2 % (N + 3)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hshift : a.alpha (1 : Fin (N + 2)).succ <
      a.tail.alpha (1 : Fin (N + 2)) := by
    rw [htwoSucc, ← a.coe_alphaValue, ← a.tail.coe_alphaValue]
    exact hstrict
  have hlostLt :=
    a.firstLeftDefect_lt_tailAlpha_of_alpha_shift_lt
      (1 : Fin (N + 2)) hshift
  have hlost :
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) =
        a.leftDefectCandidate (2 : Fin (N + 3))
          (0 : Fin (N + 3)) := by
    rw [a.coe_alphaValue]
    simpa only [htwoSucc] using
      a.alpha_shift_eq_firstLeftDefect_of_lt_tailAlpha
        (1 : Fin (N + 2)) hlostLt
  have hadjacentFinite : a.adjacentDefect (0 : Fin (N + 3)) ≠ ⊤ := by
    intro htop
    rw [leftDefectCandidate, htop] at hlost
    simp only [add_top] at hlost
    exact WithTop.coe_ne_top hlost
  let delta : ℚ :=
    (a.adjacentDefect (0 : Fin (N + 3))).untop hadjacentFinite
  have hdelta : (delta : WithTop ℚ) =
      a.adjacentDefect (0 : Fin (N + 3)) :=
    WithTop.coe_untop _ _
  have hlostQ : a.alphaValue (2 : Fin (N + 3)) =
      ((a.order (3 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta := by
    rw [leftDefectCandidate, ← hdelta, ← WithTop.coe_add] at hlost
    exact WithTop.coe_eq_coe.mp hlost
  have hfirstUpperTop :=
    a.alpha_le_leftDefectCandidate
      (i := (0 : Fin (N + 3))) (j := (0 : Fin (N + 3))) le_rfl
  have hfirstUpper : a.alphaValue (0 : Fin (N + 3)) ≤
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta := by
    rw [← a.coe_alphaValue, leftDefectCandidate, ← hdelta,
      ← WithTop.coe_add] at hfirstUpperTop
    exact_mod_cast hfirstUpperTop
  have hendpoint02Le :=
    a.alphaRightEndpoint_antitone
      (show (0 : Fin (N + 3)) ≤ (2 : Fin (N + 3)) by
        change 0 % (N + 3) ≤ 2 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
  have honeSucc : (0 : Fin (N + 3)).succ =
      (1 : Fin (N + 4)) := by
    apply Fin.ext
    change 0 % (N + 3) + 1 = 1 % (N + 4)
    simp
  have hthreeSucc : (2 : Fin (N + 3)).succ =
      (3 : Fin (N + 4)) := by
    apply Fin.ext
    change 2 % (N + 3) + 1 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold alphaRightEndpoint at hendpoint02Le
  rw [honeSucc, hthreeSucc] at hendpoint02Le
  have hfirstLower :
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta ≤
        a.alphaValue (0 : Fin (N + 3)) := by
    push_cast at hendpoint02Le hlostQ ⊢
    linarith
  have hfirstQ : a.alphaValue (0 : Fin (N + 3)) =
      ((a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) : Int) : ℚ) + delta :=
    le_antisymm hfirstUpper hfirstLower
  push_cast at hlostQ hfirstQ ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- The remaining strict low-defect branch of Case 1 is impossible.  This is
the contradiction in the last two displays of Case 1: the Lemma 9.1
alternatives reduce to `R₂ = S₂`, condition 2.1(ii) fixes `A₂`, and the
right-endpoint equalities force `R₂ = R₄` despite `R₂ < R₄`. -/
theorem false_of_firstThirdDefect_lt_tail_of_caseOneLow
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hhead : a.value 0 = b.value 0)
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hearly : a.Lemma92EarlyAlternative →
      a.alphaValue (2 : Fin (N + 3)) =
        a.tail.alphaValue (1 : Fin (N + 2)))
    (hlemma91 : a.Lemma91Alternative b)
    (hlow :
      a.truncatedPrefixDefect b (-1) 3 1 <
        ((((b.order (1 : Fin (N + 4)) -
          a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ))
    (hcase :
      a.truncatedPrefixDefect b (-1) 3 1 <
          (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∨
        (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
          (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (hstrictDefect :
      a.truncatedPrefixDefect b (-1) 3 1 <
        a.tail.truncatedPrefixDefect b.tail (-1) 2 0) : False := by
  let d := a.truncatedPrefixDefect b (-1) 3 1
  let dstar := a.tail.truncatedPrefixDefect b.tail (-1) 2 0
  let alphaThree : WithTop ℚ :=
    (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)
  let betaOne : WithTop ℚ :=
    (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  have hmin : d = min dstar (min alphaThree betaOne) := by
    exact a.firstThirdDefect_eq_min_tail_alpha_three_beta_one b hhead
  have hdCaps : d = min alphaThree betaOne := by
    rcases min_choice dstar (min alphaThree betaOne) with htail | hcaps
    · have heq : d = dstar := hmin.trans htail
      exact ((ne_of_lt hstrictDefect) heq).elim
    · exact hmin.trans hcaps
  have hdAlpha : d = alphaThree := by
    rcases hcase with hbetaStrict | halphaBeta
    · change d < betaOne at hbetaStrict
      rcases min_choice alphaThree betaOne with halpha | hbeta
      · exact hdCaps.trans halpha
      · have hdBeta : d = betaOne := hdCaps.trans hbeta
        exact ((lt_irrefl betaOne) (hdBeta ▸ hbetaStrict)).elim
    · change alphaThree ≤ betaOne at halphaBeta
      exact hdCaps.trans (min_eq_left halphaBeta)
  have htailCap :=
    a.tail.truncatedPrefixDefect_le_leftCap b.tail (-1) 2 0
  rw [a.tail.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega)]
      at htailCap
  have hone : (⟨2 - 1, by omega⟩ : Fin (N + 2)) =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    change 1 = 1 % (N + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hone] at htailCap
  have hstrictAlpha :
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
        (a.tail.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    change alphaThree < _
    rw [← hdAlpha]
    exact hstrictDefect.trans_le htailCap
  have hnotEarly : ¬a.Lemma92EarlyAlternative := by
    intro hcaseEarly
    have heq := hearly hcaseEarly
    have heqTop := congrArg (fun x : ℚ => (x : WithTop ℚ)) heq
    exact (ne_of_lt hstrictAlpha) heqTop
  have hnotFirstThird :
      ¬a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)) := by
    intro h
    exact hnotEarly (Or.inl h)
  have hnotSecondFourth :
      ¬a.order (1 : Fin (N + 4)) = a.order (3 : Fin (N + 4)) := by
    intro h
    exact hnotEarly (Or.inr (Or.inl h))
  have hnotFirstGap :
      ¬a.orderGap (0 : Fin (N + 3)) =
        2 * (ramificationIndex K : Int) := by
    intro h
    exact hnotEarly (Or.inr (Or.inr h))
  have hfirstThirdLe := a.order_zero_le_two
  have hfirstThirdEq : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)) :=
    le_antisymm hfirstThirdLe (le_of_not_gt hnotFirstThird)
  have hsecondFourthLe : a.order (1 : Fin (N + 4)) ≤
      a.order (3 : Fin (N + 4)) := by
    have htail := a.tail.order_zero_le_two
    have hzeroSucc : (⟨0, by omega⟩ : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      change 0 + 1 = 1 % (N + 4)
      simp
    have htwoSucc : (⟨2, by omega⟩ : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [a.order_goodTail, a.order_goodTail,
      hzeroSucc, htwoSucc] at htail
    exact htail
  have hsecondFourthLt : a.order (1 : Fin (N + 4)) <
      a.order (3 : Fin (N + 4)) :=
    lt_of_le_of_ne hsecondFourthLe hnotSecondFourth
  have hthirdFormula :=
    a.thirdAlpha_eq_fourth_sub_second_add_first_of_lt_tail hstrictAlpha
  have hthirdGtFirst : a.alphaValue (0 : Fin (N + 3)) <
      a.alphaValue (2 : Fin (N + 3)) := by
    have hordersQ : (a.order (1 : Fin (N + 4)) : ℚ) <
        (a.order (3 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hsecondFourthLt
    push_cast at hthirdFormula
    linarith
  have hsecondOrder : a.order (1 : Fin (N + 4)) =
      b.order (1 : Fin (N + 4)) := by
    unfold Lemma91Alternative at hlemma91
    rcases hlemma91 with hfirstThird | hsecond | hgap | hsecondFourth | hdefect
    · exact (hnotFirstThird hfirstThird).elim
    · exact hsecond
    · exact (hnotFirstGap hgap).elim
    · rcases hsecondFourth with ⟨hfour, hsecondFourth⟩
      have hthree : (⟨3, hfour⟩ : Fin (N + 4)) =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        change 3 = 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hthree] at hsecondFourth
      exact (hnotSecondFourth hsecondFourth).elim
    · have halphaEq : a.alphaValue (2 : Fin (N + 3)) =
          a.alphaValue (0 : Fin (N + 3)) := by
        apply WithTop.coe_injective
        exact hdAlpha.symm.trans hdefect.1
      exact ((ne_of_gt hthirdGtFirst) halphaEq).elim
  let second : RepresentationIndex (N + 4) (N + 4) :=
    secondRepresentationIndex (N + 1) (N + 2)
  have hsecondAlphaLe : a.representationAlpha b second ≤
      (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) := by
    have hcondition := conditions.defectCondition second
    rw [a.coe_representationAlphaValue b second] at hcondition
    have hcap := a.truncatedPrefixDefect_le_leftCap b 1 2 2
    rw [a.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega)] at hcap
    have hindex : (⟨2 - 1, by omega⟩ : Fin (N + 3)) =
        (1 : Fin (N + 3)) := by
      apply Fin.ext
      change 1 = 1 % (N + 3)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hindex] at hcap
    exact hcondition.trans hcap
  have hlowQ : a.alphaValue (2 : Fin (N + 3)) <
      ((b.order (1 : Fin (N + 4)) -
        a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    change d < _ at hlow
    rw [hdAlpha] at hlow
    change (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) < _ at hlow
    exact WithTop.coe_lt_coe.mp hlow
  have hprimaryLtHalf : a.secondRepresentationPrimaryFormula b <
      a.secondRepresentationHalfGapFormula b := by
    unfold secondRepresentationPrimaryFormula
      secondRepresentationHalfGapFormula
    change
      ((((a.order (2 : Fin (N + 4)) -
        b.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) + d) < _
    rw [hdAlpha, ← WithTop.coe_add]
    apply WithTop.coe_lt_coe.mpr
    push_cast at hlowQ ⊢
    linarith
  have hsecondAlphaEqPrimary : a.representationAlpha b second =
      a.secondRepresentationPrimaryFormula b := by
    have hformula := a.beli2019Lemma812_ii b hfirst
    change a.representationAlpha b second = _
    rw [hformula, min_eq_right hprimaryLtHalf.le]
  have hprimaryLeSecondAlpha :
      ((a.order (2 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
          a.alphaValue (2 : Fin (N + 3)) ≤
        a.alphaValue (1 : Fin (N + 3)) := by
    rw [hsecondAlphaEqPrimary] at hsecondAlphaLe
    unfold secondRepresentationPrimaryFormula at hsecondAlphaLe
    change
      ((((a.order (2 : Fin (N + 4)) -
        b.order (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) + d) ≤
          (a.alphaValue (1 : Fin (N + 3)) : WithTop ℚ) at hsecondAlphaLe
    rw [hdAlpha, ← WithTop.coe_add, ← hsecondOrder] at hsecondAlphaLe
    exact WithTop.coe_le_coe.mp hsecondAlphaLe
  have hsecondAlphaLePrimary : a.alphaValue (1 : Fin (N + 3)) ≤
      ((a.order (2 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
          a.alphaValue (2 : Fin (N + 3)) := by
    have hendpoint := a.alphaLeftEndpoint_monotone
      (show (1 : Fin (N + 3)) ≤ (2 : Fin (N + 3)) by
        change 1 % (N + 3) ≤ 2 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
    unfold alphaLeftEndpoint at hendpoint
    have honeCast : (1 : Fin (N + 3)).castSucc =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      change 1 % (N + 3) = 1 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have htwoCast : (2 : Fin (N + 3)).castSucc =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [honeCast, htwoCast] at hendpoint
    push_cast at hendpoint ⊢
    linarith
  have hsecondAlphaEq : a.alphaValue (1 : Fin (N + 3)) =
      ((a.order (2 : Fin (N + 4)) -
        a.order (1 : Fin (N + 4)) : Int) : ℚ) +
          a.alphaValue (2 : Fin (N + 3)) :=
    le_antisymm hsecondAlphaLePrimary hprimaryLeSecondAlpha
  have hrightOuter : a.alphaRightEndpoint (0 : Fin (N + 3)) =
      a.alphaRightEndpoint (2 : Fin (N + 3)) := by
    unfold alphaRightEndpoint
    have honeSucc : (0 : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      change 0 % (N + 3) + 1 = 1 % (N + 4)
      simp
    have hthreeSucc : (2 : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [honeSucc, hthreeSucc]
    push_cast at hthirdFormula ⊢
    linarith
  have hrightMiddleOuter :
      a.alphaRightEndpoint (1 : Fin (N + 3)) =
        a.alphaRightEndpoint (2 : Fin (N + 3)) := by
    have hmiddleLeFirst := a.alphaRightEndpoint_antitone
      (show (0 : Fin (N + 3)) ≤ (1 : Fin (N + 3)) by
        change 0 % (N + 3) ≤ 1 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
    have hthirdLeMiddle := a.alphaRightEndpoint_antitone
      (show (1 : Fin (N + 3)) ≤ (2 : Fin (N + 3)) by
        change 1 % (N + 3) ≤ 2 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega)
    apply le_antisymm
    · exact hmiddleLeFirst.trans_eq hrightOuter
    · exact hthirdLeMiddle
  have hsecondFourthEq : a.order (1 : Fin (N + 4)) =
      a.order (3 : Fin (N + 4)) := by
    unfold alphaRightEndpoint at hrightMiddleOuter
    have htwoSucc : (1 : Fin (N + 3)).succ =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 1 % (N + 3) + 1 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hthreeSucc : (2 : Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 % (N + 3) + 1 = 3 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [htwoSucc, hthreeSucc] at hrightMiddleOuter
    push_cast at hsecondAlphaEq hrightMiddleOuter
    exact_mod_cast (by linarith :
      (a.order (1 : Fin (N + 4)) : ℚ) =
        (a.order (3 : Fin (N + 4)) : ℚ))
  exact (ne_of_lt hsecondFourthLt) hsecondFourthEq

/-- The three alternatives displayed at the start of Case 1 in the proof of
Lemma 9.3: `β₁ > d`, `β₁ ≥ α₃`, or the large-defect lower bound. -/
noncomputable def Beli2019Lemma93CaseOneCondition
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) : Prop :=
  a.truncatedPrefixDefect b (-1) 3 1 <
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∨
  (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∨
  ((((b.order (1 : Fin (N + 4)) -
      a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
    a.truncatedPrefixDefect b (-1) 3 1

/-- Lemma 9.1's five-way alternative is independent of both chosen good
BONGs.  The source-only version is used by Corollary 8.11; this pairwise
version is what Case 1 needs after Lemma 9.2 has changed the target as well. -/
theorem lemma91Alternative_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a c : GoodBONG q L (N + 4))
    (b d : GoodBONG r M (N + 4)) :
    a.Lemma91Alternative b ↔ c.Lemma91Alternative d := by
  have hordersA : a.SameOrders c := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.order_invariant c
  have hordersB : b.SameOrders d := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant d
  have halphasA : a.SameAlphas c := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.alpha_invariant c
  have halphasB : b.SameAlphas d := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant d
  have hgap := a.orderGap_invariant
    (classificationV := classificationV) c (0 : Fin (N + 3))
  have hdefect := a.truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    c b d (-1) 3 1
  constructor
  · intro h
    unfold Lemma91Alternative at h ⊢
    rcases h with hfirst | hsecond | hgapA | hfourth | hdef
    · left
      rw [← hordersA (0 : Fin (N + 4)),
        ← hordersA (⟨2, by omega⟩ : Fin (N + 4))]
      exact hfirst
    · right; left
      rw [← hordersA (1 : Fin (N + 4)),
        ← hordersB (1 : Fin (N + 4))]
      exact hsecond
    · right; right; left
      rw [← hgap]
      exact hgapA
    · right; right; right; left
      rcases hfourth with ⟨hfour, hfourth⟩
      refine ⟨hfour, ?_⟩
      rw [← hordersA (1 : Fin (N + 4)), ← hordersA ⟨3, hfour⟩]
      exact hfourth
    · right; right; right; right
      constructor
      · rw [← hdefect, ← halphasA (0 : Fin (N + 3))]
        exact hdef.1
      · rw [← halphasA (0 : Fin (N + 3)),
          ← halphasB (0 : Fin (N + 3))]
        exact hdef.2
  · intro h
    unfold Lemma91Alternative at h ⊢
    rcases h with hfirst | hsecond | hgapC | hfourth | hdef
    · left
      rw [hordersA (0 : Fin (N + 4)),
        hordersA (⟨2, by omega⟩ : Fin (N + 4))]
      exact hfirst
    · right; left
      rw [hordersA (1 : Fin (N + 4)),
        hordersB (1 : Fin (N + 4))]
      exact hsecond
    · right; right; left
      rw [hgap]
      exact hgapC
    · right; right; right; left
      rcases hfourth with ⟨hfour, hfourth⟩
      refine ⟨hfour, ?_⟩
      rw [hordersA (1 : Fin (N + 4)), hordersA ⟨3, hfour⟩]
      exact hfourth
    · right; right; right; right
      constructor
      · rw [hdefect, halphasA (0 : Fin (N + 3))]
        exact hdef.1
      · rw [halphasA (0 : Fin (N + 3)),
          halphasB (0 : Fin (N + 3))]
        exact hdef.2

/-- The three Case 1 inequalities are lattice invariants, so the paper may
test them after the Corollary 8.11 and Lemma 9.2 changes of BONG. -/
theorem beli2019Lemma93CaseOneCondition_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a c : GoodBONG q L (N + 4))
    (b d : GoodBONG r M (N + 4)) :
    a.Beli2019Lemma93CaseOneCondition b ↔
      c.Beli2019Lemma93CaseOneCondition d := by
  have hordersA : a.SameOrders c := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.order_invariant c
  have hordersB : b.SameOrders d := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.order_invariant d
  have halphasA : a.SameAlphas c := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.alpha_invariant c
  have halphasB : b.SameAlphas d := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact b.alpha_invariant d
  have hdefect := a.truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    c b d (-1) 3 1
  unfold Beli2019Lemma93CaseOneCondition
  rw [hdefect, halphasA (2 : Fin (N + 3)),
    halphasB (0 : Fin (N + 3)), hordersB (1 : Fin (N + 4)),
    hordersA (2 : Fin (N + 4))]

/-- Equality of the two first-third capped defects is exactly equality of
the primary candidates for tail `A₁` and original `A₂`. -/
theorem representationPrimaryDefect_tail_first_eq_originalSecond_of_defect_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hdefect :
      a.truncatedPrefixDefect b (-1) 3 1 =
        a.tail.truncatedPrefixDefect b.tail (-1) 2 0) :
    a.tail.representationPrimaryDefect b.tail
        (firstRepresentationIndex N (N + 1)) =
      a.representationPrimaryDefect b
        (secondRepresentationIndex N (N + 1)) := by
  change
    (((a.tail.order (⟨1, by omega⟩ : Fin (N + 2)) -
      b.tail.order (⟨0, by omega⟩ : Fin (N + 2)) : Int) : ℚ) :
        WithTop ℚ) +
      a.tail.truncatedPrefixDefect b.tail (-1) 2 0 =
    (((a.order (⟨2, by omega⟩ : Fin (N + 3)) -
      b.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) :
        WithTop ℚ) +
      a.truncatedPrefixDefect b (-1) 3 1
  rw [a.order_goodTail, b.order_goodTail]
  have htarget : (⟨1, by omega⟩ : Fin (N + 2)).succ =
      (⟨2, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hsource : (⟨0, by omega⟩ : Fin (N + 2)).succ =
      (⟨1, by omega⟩ : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [htarget, hsource, hdefect]

/-- At the next boundary, the same defect equality transports the
previous-form secondary candidate used by Lemma 2.7(i). -/
theorem representationSecondaryPreviousDefect_tail_second_eq_shift_of_defect_eq
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hN : 0 < N)
    (hdefect :
      a.truncatedPrefixDefect b (-1) 3 1 =
        a.tail.truncatedPrefixDefect b.tail (-1) 2 0) :
    a.tail.representationSecondaryPreviousDefect b.tail
        (secondRepresentationIndex N (N + 1))
        ⟨by simp only [secondRepresentationIndex]; omega,
         by simp only [secondRepresentationIndex]; omega⟩ =
      a.representationSecondaryPreviousDefect b
        (secondRepresentationIndex N (N + 1)).tailShift
        ⟨by
          simp only [RepresentationIndex.tailShift_val,
            secondRepresentationIndex]
          omega,
         by
          simp only [RepresentationIndex.tailShift_val,
            secondRepresentationIndex]
          omega⟩ := by
  change
    (((a.tail.order (⟨2, by omega⟩ : Fin (N + 3)) +
      a.tail.order (⟨3, by omega⟩ : Fin (N + 3)) -
      b.tail.order (⟨0, by omega⟩ : Fin (N + 3)) -
      b.tail.order (⟨1, by omega⟩ : Fin (N + 3)) : Int) : ℚ) :
        WithTop ℚ) +
      a.tail.truncatedPrefixDefect b.tail (-1) 2 0 =
    (((a.order (⟨3, by omega⟩ : Fin (N + 4)) +
      a.order (⟨4, by omega⟩ : Fin (N + 4)) -
      b.order (⟨1, by omega⟩ : Fin (N + 4)) -
      b.order (⟨2, by omega⟩ : Fin (N + 4)) : Int) : ℚ) :
        WithTop ℚ) +
      a.truncatedPrefixDefect b (-1) 3 1
  rw [a.order_goodTail, a.order_goodTail,
    b.order_goodTail, b.order_goodTail]
  have hthree : (⟨2, by omega⟩ : Fin (N + 3)).succ =
      (⟨3, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have hfour : (⟨3, by omega⟩ : Fin (N + 3)).succ =
      (⟨4, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have hone : (⟨0, by omega⟩ : Fin (N + 3)).succ =
      (⟨1, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  have htwo : (⟨1, by omega⟩ : Fin (N + 3)).succ =
      (⟨2, by omega⟩ : Fin (N + 4)) := by
    apply Fin.ext
    rfl
  rw [hthree, hfour, hone, htwo, hdefect]

/-- The defect-equality branch therefore gives the complete equality
`A₁* = A₂`, using Lemma 8.12(ii) at the original boundary. -/
theorem representationAlpha_tail_first_eq_originalSecond_of_defect_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hfirst : a.order (0 : Fin (N + 3)) =
      b.order (0 : Fin (N + 3)))
    (hdefect :
      a.truncatedPrefixDefect b (-1) 3 1 =
        a.tail.truncatedPrefixDefect b.tail (-1) 2 0) :
    a.tail.representationAlpha b.tail
        (firstRepresentationIndex N (N + 1)) =
      a.representationAlpha b
        (secondRepresentationIndex N (N + 1)) := by
  apply a.representationAlpha_tail_first_eq_originalSecond_of_primary_eq
    b hfirst
  exact
    a.representationPrimaryDefect_tail_first_eq_originalSecond_of_defect_eq
      b hdefect

/-- The third disjunct in the paper's Case 1 makes the primary candidate at
`A₂` no smaller than the half-gap candidate.  Hence the first tail
comparison is bounded by the original `A₂`. -/
theorem representationAlpha_tail_first_le_originalSecond_of_largeDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M (N + 3))
    (hfirst : a.order (0 : Fin (N + 3)) =
      b.order (0 : Fin (N + 3)))
    (hdefect :
      ((((b.order (1 : Fin (N + 3)) -
          a.order (2 : Fin (N + 3)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b (-1) 3 1) :
    a.tail.representationAlpha b.tail
        (firstRepresentationIndex N (N + 1)) ≤
      a.representationAlpha b
        (secondRepresentationIndex N (N + 1)) := by
  let first := firstRepresentationIndex N (N + 1)
  have hshift : first.tailShift =
      secondRepresentationIndex N (N + 1) := by
    rfl
  have hhalf :
      a.tail.representationAlpha b.tail first ≤
        a.secondRepresentationHalfGapFormula b := by
    calc
      a.tail.representationAlpha b.tail first ≤
          a.tail.representationHalfGap b.tail first :=
        a.tail.representationAlpha_le_halfGap b.tail first
      _ = a.representationHalfGap b first.tailShift :=
        a.representationHalfGap_tail_eq_shift b first
      _ = a.secondRepresentationHalfGapFormula b := by
        rw [hshift]
        exact a.representationHalfGap_second_eq_formula b
  have hhalfPrimary :
      a.secondRepresentationHalfGapFormula b ≤
        a.secondRepresentationPrimaryFormula b := by
    unfold secondRepresentationHalfGapFormula
      secondRepresentationPrimaryFormula
    let delta : ℚ :=
      ((a.order (2 : Fin (N + 3)) -
        b.order (1 : Fin (N + 3)) : Int) : ℚ)
    let threshold : ℚ :=
      ((b.order (1 : Fin (N + 3)) -
        a.order (2 : Fin (N + 3)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)
    have hdefect' : (threshold : WithTop ℚ) ≤
        a.truncatedPrefixDefect b (-1) 3 1 := by
      exact hdefect
    have hadd := add_le_add_right hdefect' (delta : WithTop ℚ)
    change ((delta / 2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
      (delta : WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1
    calc
      ((delta / 2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) =
          (delta : WithTop ℚ) + (threshold : WithTop ℚ) := by
        rw [← WithTop.coe_add]
        congr 1
        dsimp only [delta, threshold]
        push_cast
        ring
      _ ≤ (delta : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) 3 1 := hadd
  apply representationAlpha_tail_first_le_originalSecond_of_le_primary
    a b hfirst
  rw [a.representationPrimaryDefect_second_eq_formula b]
  exact hhalf.trans hhalfPrimary

/-- In the interior `A₃` branch with `S₂ ≤ R₄`, the large first
defect also bounds the Lemma 2.7(i) previous-form candidate.  This is the
inequality chain displayed in the middle of Case 1. -/
theorem representationAlpha_tail_second_le_shiftedPrevious_of_largeDefect
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hN : 0 < N)
    (halphaA : ∀ k : Fin (N + 2), 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (hcross : b.order (1 : Fin (N + 4)) ≤
      a.order (3 : Fin (N + 4)))
    (hdefect :
      ((((b.order (1 : Fin (N + 4)) -
          a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b (-1) 3 1) :
    let i := secondRepresentationIndex N (N + 1)
    let j := i.tailShift
    a.tail.representationAlpha b.tail i ≤
      a.representationSecondaryPreviousDefect b j
        ⟨by
          simp only [j, i, RepresentationIndex.tailShift_val,
            secondRepresentationIndex]
          omega,
         by
          simp only [j, i, RepresentationIndex.tailShift_val,
            secondRepresentationIndex]
          omega⟩ := by
  dsimp only
  let i : RepresentationIndex (N + 3) (N + 3) :=
    secondRepresentationIndex N (N + 1)
  let j : RepresentationIndex (N + 4) (N + 4) := i.tailShift
  have hupper :=
    (a.tail.representationAlpha_le_prime b.tail i).trans
      (a.tail.representationAlphaPrime_le_primaryLeftCap b.tail i)
  rw [a.tail.prefixAlphaCap_of_internal
    (by simp only [i, secondRepresentationIndex]; omega)
    (by simp only [i, secondRepresentationIndex]; omega)] at hupper
  have htarget : a.alphaValue (3 : Fin (N + 3)) =
      a.tail.alphaValue (2 : Fin (N + 2)) := by
    let k : Fin (N + 2) := ⟨2, by omega⟩
    have h := halphaA k (by simp only [k]; omega)
    have hsucc : k.succ = (3 : Fin (N + 3)) := by
      apply Fin.ext
      change 2 + 1 = 3 % (N + 3)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hk : k = (2 : Fin (N + 2)) := by
      apply Fin.ext
      change 2 = 2 % (N + 2)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsucc, hk] at h
    exact h
  have halphaHalf := a.alpha_le_halfGapCandidate (3 : Fin (N + 3))
  rw [← a.coe_alphaValue] at halphaHalf
  let upper : ℚ :=
    ((a.order (3 : Fin (N + 4)) + a.order (4 : Fin (N + 4)) : Int) : ℚ) /
        2 - (b.order (2 : Fin (N + 4)) : ℚ) +
      (ramificationIndex K : ℚ)
  let primaryShift : ℚ :=
    ((a.order (3 : Fin (N + 4)) -
      b.order (2 : Fin (N + 4)) : Int) : ℚ)
  have htargetOrderIndex :
      (⟨i.val, by simp only [i, secondRepresentationIndex]; omega⟩ :
          Fin (N + 3)).succ =
        (3 : Fin (N + 4)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    change i.val + 1 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [i, secondRepresentationIndex]
  have hsourceOrderIndex :
      (⟨i.val - 1, by simp only [i, secondRepresentationIndex]; omega⟩ :
          Fin (N + 3)).succ =
        (2 : Fin (N + 4)) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    change i.val - 1 + 1 = 2 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [i, secondRepresentationIndex]
  have halphaIndex :
      (⟨i.val + 1 - 1,
          by simp only [i, secondRepresentationIndex]; omega⟩ : Fin (N + 2)) =
        (2 : Fin (N + 2)) := by
    apply Fin.ext
    change i.val + 1 - 1 = 2 % (N + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [i, secondRepresentationIndex]
  have hupper' : a.tail.representationAlpha b.tail i ≤
      (upper : WithTop ℚ) := by
    calc
      a.tail.representationAlpha b.tail i ≤
          (primaryShift : WithTop ℚ) +
            (a.tail.alphaValue (2 : Fin (N + 2)) : WithTop ℚ) := by
        rw [a.order_goodTail, b.order_goodTail, htargetOrderIndex,
          hsourceOrderIndex, halphaIndex] at hupper
        simpa only [primaryShift] using hupper
      _ = (primaryShift : WithTop ℚ) +
            (a.alphaValue (3 : Fin (N + 3)) : WithTop ℚ) := by
        rw [htarget]
      _ ≤ (primaryShift : WithTop ℚ) +
            a.halfGapCandidate (3 : Fin (N + 3)) :=
        add_le_add_right halphaHalf _
      _ = (upper : WithTop ℚ) := by
        unfold halfGapCandidate
        have hsucc : (3 : Fin (N + 3)).succ =
            (4 : Fin (N + 4)) := by
          apply Fin.ext
          change 3 % (N + 3) + 1 = 4 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hcast : (3 : Fin (N + 3)).castSucc =
            (3 : Fin (N + 4)) := by
          apply Fin.ext
          change 3 % (N + 3) = 3 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hsucc, hcast]
        rw [← WithTop.coe_add]
        congr 1
        dsimp only [upper, primaryShift]
        push_cast
        ring
  have hgood : a.order (2 : Fin (N + 4)) ≤
      a.order (4 : Fin (N + 4)) := by
    let k : Fin (N + 4) := ⟨2, by omega⟩
    have hk : k.val + 2 < N + 4 := by
      simp only [k]
      omega
    have h := a.good k hk
    have hkLeft : k = (2 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 = 2 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    have hkRight : (⟨k.val + 2, hk⟩ : Fin (N + 4)) =
        (4 : Fin (N + 4)) := by
      apply Fin.ext
      change 2 + 2 = 4 % (N + 4)
      rw [Nat.mod_eq_of_lt (by omega)]
    change a.toBONG.order (2 : Fin (N + 4)) ≤
      a.toBONG.order (4 : Fin (N + 4))
    calc
      a.toBONG.order (2 : Fin (N + 4)) = a.toBONG.order k :=
        congrArg a.toBONG.order hkLeft.symm
      _ ≤ a.toBONG.order ⟨k.val + 2, hk⟩ := h
      _ = a.toBONG.order (4 : Fin (N + 4)) :=
        congrArg a.toBONG.order hkRight
  let shift : ℚ :=
    ((a.order (3 : Fin (N + 4)) + a.order (4 : Fin (N + 4)) -
      b.order (1 : Fin (N + 4)) - b.order (2 : Fin (N + 4)) : Int) : ℚ)
  let threshold : ℚ :=
    ((b.order (1 : Fin (N + 4)) - a.order (2 : Fin (N + 4)) : Int) : ℚ) /
        2 + (ramificationIndex K : ℚ)
  have hdefect' : (threshold : WithTop ℚ) ≤
      a.truncatedPrefixDefect b (-1) 3 1 := by
    exact hdefect
  have hlowerQ : upper ≤ shift + threshold := by
    have hcrossQ : (b.order (1 : Fin (N + 4)) : ℚ) ≤
        (a.order (3 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hcross
    have hgoodQ : (a.order (2 : Fin (N + 4)) : ℚ) ≤
        (a.order (4 : Fin (N + 4)) : ℚ) := by
      exact_mod_cast hgood
    dsimp only [upper, shift, threshold]
    push_cast
    linarith
  have hlower : (upper : WithTop ℚ) ≤
      (shift : WithTop ℚ) + a.truncatedPrefixDefect b (-1) 3 1 := by
    calc
      (upper : WithTop ℚ) ≤ ((shift + threshold : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.mpr hlowerQ
      _ = (shift : WithTop ℚ) + (threshold : WithTop ℚ) := by
        rw [WithTop.coe_add]
      _ ≤ (shift : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) 3 1 :=
        add_le_add_right hdefect' _
  apply hupper'.trans
  have hthree : (⟨3, by omega⟩ : Fin (N + 4)) =
      (3 : Fin (N + 4)) := by
    apply Fin.ext
    change 3 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hfour : (⟨4, by omega⟩ : Fin (N + 4)) =
      (4 : Fin (N + 4)) := by
    apply Fin.ext
    change 4 = 4 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have htwo : (⟨2, by omega⟩ : Fin (N + 4)) =
      (2 : Fin (N + 4)) := by
    apply Fin.ext
    change 2 = 2 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  simpa [j, i, representationSecondaryPreviousDefect,
    RepresentationIndex.tailShift_val, secondRepresentationIndex,
    shift, hthree, hfour, htwo] using hlower

/-- The complete `A₃` estimate in Case 1's large-defect subcase.  Current
essentiality uses Lemma 2.7(i) and the preceding arithmetic bound; next
essentiality uses Lemma 2.7(ii), whose current-form candidate is transported
exactly.  At the terminal rank only the half-gap and primary candidates
remain. -/
theorem representationAlpha_tail_second_le_shift_of_largeDefect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin (N + 2), 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin (N + 2),
      b.alphaValue k.succ = b.tail.alphaValue k)
    (himportant :
      a.tail.IsCurrentEssential b.tail
          (secondRepresentationIndex N (N + 1)) ∨
        a.tail.IsNextEssential b.tail
          (secondRepresentationIndex N (N + 1)))
    (hdefect :
      ((((b.order (1 : Fin (N + 4)) -
          a.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b (-1) 3 1) :
    let i := secondRepresentationIndex N (N + 1)
    a.tail.representationAlpha b.tail i ≤
      a.representationAlpha b i.tailShift := by
  dsimp only
  let i : RepresentationIndex (N + 3) (N + 3) :=
    secondRepresentationIndex N (N + 1)
  let j : RepresentationIndex (N + 4) (N + 4) := i.tailShift
  change a.tail.representationAlpha b.tail i ≤
    a.representationAlpha b j
  have hhalf : a.tail.representationAlpha b.tail i ≤
      a.representationHalfGap b j := by
    exact (a.tail.representationAlpha_le_halfGap b.tail i).trans_eq
      (a.representationHalfGap_tail_eq_shift b i)
  have hprimaryEq : a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b j := by
    exact a.representationPrimaryDefect_tail_eq_shift_of_targetLater_sourceAll
      b hhead halphaA halphaB i (by
        simp only [i, secondRepresentationIndex]
        omega)
  have hprimary : a.tail.representationAlpha b.tail i ≤
      a.representationPrimaryDefect b j :=
    (a.tail.representationAlpha_le_primary b.tail i).trans_eq hprimaryEq
  by_cases hN : 0 < N
  · rcases himportant with hcurrent | hnext
    · letI : Beli2006AlphaLaws.{u, v} K := alphaV
      have hstrictTail :=
        order_head_lt_third_of_currentEssential_second
          a.tail b.tail hcurrent
      have hzeroSucc : (0 : Fin (N + 3)).succ =
          (1 : Fin (N + 4)) := by
        apply Fin.ext
        change 0 % (N + 3) + 1 = 1 % (N + 4)
        simp
      have htwoSucc : (2 : Fin (N + 3)).succ =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        change 2 % (N + 3) + 1 = 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [b.order_goodTail, a.order_goodTail,
        hzeroSucc, htwoSucc] at hstrictTail
      have hcross : b.order (1 : Fin (N + 4)) ≤
          a.order (3 : Fin (N + 4)) := hstrictTail.le
      have hprevious :=
        representationAlpha_tail_second_le_shiftedPrevious_of_largeDefect
          a b hN halphaA hcross hdefect
      have hjInterior : 1 < j.val ∧ j.val + 1 < N + 4 := by
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
        omega
      have hjSource : (⟨j.val - 2, by omega⟩ : Fin (N + 4)) =
          (1 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val - 2 = 1 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjTarget : (⟨j.val, j.lt_large⟩ : Fin (N + 4)) =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val = 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjCross :
          b.order ⟨j.val - 2, by omega⟩ ≤
            a.order ⟨j.val, j.lt_large⟩ := by
        rw [hjSource, hjTarget]
        exact hcross
      rw [a.representationAlpha_eq_min_halfGap_prime b j,
        a.representationAlphaPrime_eq_min_primary_previous
          b j hjInterior hjCross]
      exact le_min hhalf (le_min hprimary hprevious)
    · letI : Beli2006AlphaLaws.{u, w} K := alphaW
      have hstrictTail :=
        order_second_lt_fourth_of_nextEssential_second
          a.tail b.tail hN hnext
      have hiInterior : 1 < i.val ∧ i.val + 1 < N + 3 := by
        simp only [i, secondRepresentationIndex]
        omega
      have hiSource : (⟨i.val - 1, by omega⟩ : Fin (N + 3)) =
          (1 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val - 1 = 1 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [i, secondRepresentationIndex]
      have hiTarget : (⟨i.val + 1, hiInterior.2⟩ : Fin (N + 3)) =
          (3 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val + 1 = 3 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [i, secondRepresentationIndex]
      have hiCross :
          b.tail.order ⟨i.val - 1, by omega⟩ ≤
            a.tail.order ⟨i.val + 1, hiInterior.2⟩ := by
        rw [hiSource, hiTarget]
        exact hstrictTail.le
      have hcurrentTail : a.tail.representationAlpha b.tail i ≤
          a.tail.representationSecondaryCurrentDefect b.tail i hiInterior := by
        calc
          a.tail.representationAlpha b.tail i ≤
              a.tail.representationAlphaPrime b.tail i :=
            a.tail.representationAlpha_le_prime b.tail i
          _ = min (a.tail.representationPrimaryDefect b.tail i)
                (a.tail.representationSecondaryCurrentDefect
                  b.tail i hiInterior) :=
            a.tail.representationAlphaPrime_eq_min_primary_current
              b.tail i hiInterior hiCross
          _ ≤ a.tail.representationSecondaryCurrentDefect
                b.tail i hiInterior := min_le_right _ _
      have hcurrentEq :
          a.tail.representationSecondaryCurrentDefect b.tail i hiInterior =
            a.representationSecondaryCurrentDefect b j
              ⟨by
                change 1 < i.val + 1
                omega,
               by
                change i.val + 1 + 1 < N + 4
                omega⟩ := by
        exact
          a.representationSecondaryCurrentDefect_tail_eq_shift_of_targetLater_sourceAll
            b hhead halphaA halphaB i hiInterior
      have hcurrentBound : a.tail.representationAlpha b.tail i ≤
          a.representationSecondaryCurrentDefect b j
            ⟨by
              change 1 < i.val + 1
              omega,
             by
              change i.val + 1 + 1 < N + 4
              omega⟩ := hcurrentTail.trans_eq hcurrentEq
      have hjInterior : 1 < j.val ∧ j.val + 1 < N + 4 := by
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
        omega
      have hstrictOriginal : b.order (2 : Fin (N + 4)) <
          a.order (4 : Fin (N + 4)) := by
        have honeSucc : (1 : Fin (N + 3)).succ =
            (2 : Fin (N + 4)) := by
          apply Fin.ext
          change 1 % (N + 3) + 1 = 2 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hthreeSucc : (3 : Fin (N + 3)).succ =
            (4 : Fin (N + 4)) := by
          apply Fin.ext
          change 3 % (N + 3) + 1 = 4 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [b.order_goodTail, a.order_goodTail,
          honeSucc, hthreeSucc] at hstrictTail
        exact hstrictTail
      have hjSource : (⟨j.val - 1, by omega⟩ : Fin (N + 4)) =
          (2 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val - 1 = 2 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjTarget : (⟨j.val + 1, hjInterior.2⟩ : Fin (N + 4)) =
          (4 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val + 1 = 4 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjCross :
          b.order ⟨j.val - 1, by omega⟩ ≤
            a.order ⟨j.val + 1, hjInterior.2⟩ := by
        rw [hjSource, hjTarget]
        exact hstrictOriginal.le
      rw [a.representationAlpha_eq_min_halfGap_prime b j,
        a.representationAlphaPrime_eq_min_primary_current
          b j hjInterior hjCross]
      exact le_min hhalf (le_min hprimary hcurrentBound)
  · have hjEndpoint : ¬(1 < j.val ∧ j.val + 1 < N + 4) := by
      simp only [j, i, RepresentationIndex.tailShift_val,
        secondRepresentationIndex]
      omega
    rw [a.representationAlpha_eq_min_halfGap_prime b j,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b j hjEndpoint]
    exact le_min hhalf hprimary

/-- The complete `A₃` estimate when the first-third defect agrees with its
tail counterpart.  In the current-essential branch Lemma 2.7(i)'s
previous-form candidate is transported by the defect equality; in the
next-essential branch Lemma 2.7(ii)'s current-form candidate is transported
by the normalized alpha caps. -/
theorem representationAlpha_tail_second_le_shift_of_defect_eq
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ k : Fin (N + 2), 2 ≤ k.1 →
      a.alphaValue k.succ = a.tail.alphaValue k)
    (halphaB : ∀ k : Fin (N + 2),
      b.alphaValue k.succ = b.tail.alphaValue k)
    (himportant :
      a.tail.IsCurrentEssential b.tail
          (secondRepresentationIndex N (N + 1)) ∨
        a.tail.IsNextEssential b.tail
          (secondRepresentationIndex N (N + 1)))
    (hdefect :
      a.truncatedPrefixDefect b (-1) 3 1 =
        a.tail.truncatedPrefixDefect b.tail (-1) 2 0) :
    let i := secondRepresentationIndex N (N + 1)
    a.tail.representationAlpha b.tail i ≤
      a.representationAlpha b i.tailShift := by
  dsimp only
  let i : RepresentationIndex (N + 3) (N + 3) :=
    secondRepresentationIndex N (N + 1)
  let j : RepresentationIndex (N + 4) (N + 4) := i.tailShift
  change a.tail.representationAlpha b.tail i ≤
    a.representationAlpha b j
  have hhalf : a.tail.representationAlpha b.tail i ≤
      a.representationHalfGap b j := by
    exact (a.tail.representationAlpha_le_halfGap b.tail i).trans_eq
      (a.representationHalfGap_tail_eq_shift b i)
  have hprimaryEq : a.tail.representationPrimaryDefect b.tail i =
      a.representationPrimaryDefect b j := by
    exact a.representationPrimaryDefect_tail_eq_shift_of_targetLater_sourceAll
      b hhead halphaA halphaB i (by
        simp only [i, secondRepresentationIndex]
        omega)
  have hprimary : a.tail.representationAlpha b.tail i ≤
      a.representationPrimaryDefect b j :=
    (a.tail.representationAlpha_le_primary b.tail i).trans_eq hprimaryEq
  by_cases hN : 0 < N
  · rcases himportant with hcurrent | hnext
    · letI : Beli2006AlphaLaws.{u, v} K := alphaV
      have hstrictTail :=
        order_head_lt_third_of_currentEssential_second
          a.tail b.tail hcurrent
      have hiInterior : 1 < i.val ∧ i.val + 1 < N + 3 := by
        simp only [i, secondRepresentationIndex]
        omega
      have hiSource : (⟨i.val - 2, by omega⟩ : Fin (N + 3)) =
          (0 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val - 2 = 0
        simp only [i, secondRepresentationIndex]
      have hiTarget : (⟨i.val, i.lt_large⟩ : Fin (N + 3)) =
          (2 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val = 2 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [i, secondRepresentationIndex]
      have hiCross :
          b.tail.order ⟨i.val - 2, by omega⟩ ≤
            a.tail.order ⟨i.val, i.lt_large⟩ := by
        rw [hiSource, hiTarget]
        exact hstrictTail.le
      have hpreviousTail : a.tail.representationAlpha b.tail i ≤
          a.tail.representationSecondaryPreviousDefect
            b.tail i hiInterior := by
        calc
          a.tail.representationAlpha b.tail i ≤
              a.tail.representationAlphaPrime b.tail i :=
            a.tail.representationAlpha_le_prime b.tail i
          _ = min (a.tail.representationPrimaryDefect b.tail i)
                (a.tail.representationSecondaryPreviousDefect
                  b.tail i hiInterior) :=
            a.tail.representationAlphaPrime_eq_min_primary_previous
              b.tail i hiInterior hiCross
          _ ≤ a.tail.representationSecondaryPreviousDefect
                b.tail i hiInterior := min_le_right _ _
      have hjInterior : 1 < j.val ∧ j.val + 1 < N + 4 := by
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
        omega
      have hpreviousEq :
          a.tail.representationSecondaryPreviousDefect b.tail i hiInterior =
            a.representationSecondaryPreviousDefect b j hjInterior := by
        simpa only [i, j] using
          a.representationSecondaryPreviousDefect_tail_second_eq_shift_of_defect_eq
            b hN hdefect
      have hprevious : a.tail.representationAlpha b.tail i ≤
          a.representationSecondaryPreviousDefect b j hjInterior :=
        hpreviousTail.trans_eq hpreviousEq
      have hstrictOriginal : b.order (1 : Fin (N + 4)) <
          a.order (3 : Fin (N + 4)) := by
        have hzeroSucc : (0 : Fin (N + 3)).succ =
            (1 : Fin (N + 4)) := by
          apply Fin.ext
          change 0 % (N + 3) + 1 = 1 % (N + 4)
          simp
        have htwoSucc : (2 : Fin (N + 3)).succ =
            (3 : Fin (N + 4)) := by
          apply Fin.ext
          change 2 % (N + 3) + 1 = 3 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [b.order_goodTail, a.order_goodTail,
          hzeroSucc, htwoSucc] at hstrictTail
        exact hstrictTail
      have hjSource : (⟨j.val - 2, by omega⟩ : Fin (N + 4)) =
          (1 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val - 2 = 1 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjTarget : (⟨j.val, j.lt_large⟩ : Fin (N + 4)) =
          (3 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val = 3 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjCross :
          b.order ⟨j.val - 2, by omega⟩ ≤
            a.order ⟨j.val, j.lt_large⟩ := by
        rw [hjSource, hjTarget]
        exact hstrictOriginal.le
      rw [a.representationAlpha_eq_min_halfGap_prime b j,
        a.representationAlphaPrime_eq_min_primary_previous
          b j hjInterior hjCross]
      exact le_min hhalf (le_min hprimary hprevious)
    · letI : Beli2006AlphaLaws.{u, w} K := alphaW
      have hstrictTail :=
        order_second_lt_fourth_of_nextEssential_second
          a.tail b.tail hN hnext
      have hiInterior : 1 < i.val ∧ i.val + 1 < N + 3 := by
        simp only [i, secondRepresentationIndex]
        omega
      have hiSource : (⟨i.val - 1, by omega⟩ : Fin (N + 3)) =
          (1 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val - 1 = 1 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [i, secondRepresentationIndex]
      have hiTarget : (⟨i.val + 1, hiInterior.2⟩ : Fin (N + 3)) =
          (3 : Fin (N + 3)) := by
        apply Fin.ext
        change i.val + 1 = 3 % (N + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [i, secondRepresentationIndex]
      have hiCross :
          b.tail.order ⟨i.val - 1, by omega⟩ ≤
            a.tail.order ⟨i.val + 1, hiInterior.2⟩ := by
        rw [hiSource, hiTarget]
        exact hstrictTail.le
      have hcurrentTail : a.tail.representationAlpha b.tail i ≤
          a.tail.representationSecondaryCurrentDefect b.tail i hiInterior := by
        calc
          a.tail.representationAlpha b.tail i ≤
              a.tail.representationAlphaPrime b.tail i :=
            a.tail.representationAlpha_le_prime b.tail i
          _ = min (a.tail.representationPrimaryDefect b.tail i)
                (a.tail.representationSecondaryCurrentDefect
                  b.tail i hiInterior) :=
            a.tail.representationAlphaPrime_eq_min_primary_current
              b.tail i hiInterior hiCross
          _ ≤ a.tail.representationSecondaryCurrentDefect
                b.tail i hiInterior := min_le_right _ _
      have hcurrentEq :
          a.tail.representationSecondaryCurrentDefect b.tail i hiInterior =
            a.representationSecondaryCurrentDefect b j
              ⟨by
                change 1 < i.val + 1
                omega,
               by
                change i.val + 1 + 1 < N + 4
                omega⟩ := by
        exact
          a.representationSecondaryCurrentDefect_tail_eq_shift_of_targetLater_sourceAll
            b hhead halphaA halphaB i hiInterior
      have hcurrentBound : a.tail.representationAlpha b.tail i ≤
          a.representationSecondaryCurrentDefect b j
            ⟨by
              change 1 < i.val + 1
              omega,
             by
              change i.val + 1 + 1 < N + 4
              omega⟩ := hcurrentTail.trans_eq hcurrentEq
      have hjInterior : 1 < j.val ∧ j.val + 1 < N + 4 := by
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
        omega
      have hstrictOriginal : b.order (2 : Fin (N + 4)) <
          a.order (4 : Fin (N + 4)) := by
        have honeSucc : (1 : Fin (N + 3)).succ =
            (2 : Fin (N + 4)) := by
          apply Fin.ext
          change 1 % (N + 3) + 1 = 2 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hthreeSucc : (3 : Fin (N + 3)).succ =
            (4 : Fin (N + 4)) := by
          apply Fin.ext
          change 3 % (N + 3) + 1 = 4 % (N + 4)
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [b.order_goodTail, a.order_goodTail,
          honeSucc, hthreeSucc] at hstrictTail
        exact hstrictTail
      have hjSource : (⟨j.val - 1, by omega⟩ : Fin (N + 4)) =
          (2 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val - 1 = 2 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjTarget : (⟨j.val + 1, hjInterior.2⟩ : Fin (N + 4)) =
          (4 : Fin (N + 4)) := by
        apply Fin.ext
        change j.val + 1 = 4 % (N + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [j, i, RepresentationIndex.tailShift_val,
          secondRepresentationIndex]
      have hjCross :
          b.order ⟨j.val - 1, by omega⟩ ≤
            a.order ⟨j.val + 1, hjInterior.2⟩ := by
        rw [hjSource, hjTarget]
        exact hstrictOriginal.le
      rw [a.representationAlpha_eq_min_halfGap_prime b j,
        a.representationAlphaPrime_eq_min_primary_current
          b j hjInterior hjCross]
      exact le_min hhalf (le_min hprimary hcurrentBound)
  · have hjEndpoint : ¬(1 < j.val ∧ j.val + 1 < N + 4) := by
      simp only [j, i, RepresentationIndex.tailShift_val,
        secondRepresentationIndex]
      omega
    rw [a.representationAlpha_eq_min_halfGap_prime b j,
      a.representationAlphaPrime_eq_primary_of_not_interior
        b j hjEndpoint]
    exact le_min hhalf hprimary

/-- Only the first two tail boundaries remain after the Case 1 source
normalization. -/
structure Beli2019Lemma93CaseOneLowTwoReverseCertificate
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (D : Beli2019Lemma93CaseOneNormalizedPair a b) : Prop where
  reverseAtImportant
    (i : RepresentationIndex (N + 3) (N + 3))
    (himportant :
      D.normalized.targetTransform.transformed.tail.IsCurrentEssential
          D.normalized.sourceTransform.transformed.tail i ∨
        D.normalized.targetTransform.transformed.tail.IsNextEssential
          D.normalized.sourceTransform.transformed.tail i)
    (hlow : i.val ≤ 2) :
    D.normalized.targetTransform.transformed.tail.representationAlpha
        D.normalized.sourceTransform.transformed.tail i ≤
      D.normalized.targetTransform.transformed.representationAlpha
        D.normalized.sourceTransform.transformed i.tailShift

/-- Case 1's third displayed disjunct supplies both remaining low-index
inequalities: the preceding `A₂` theorem handles tail value one and the
complete `A₃` theorem handles tail value two. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.lowTwoReverse_of_largeDefect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      ((((D.normalized.sourceTransform.transformed.order
              (1 : Fin (N + 4)) -
            D.normalized.targetTransform.transformed.order
              (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1) :
    Beli2019Lemma93CaseOneLowTwoReverseCertificate a b D where
  reverseAtImportant i himportant hlow := by
    have hiPos := i.pos
    by_cases hone : i.val = 1
    · letI : Beli2006AlphaLaws.{u, v} K := alphaV
      have hi : i = firstRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simpa only [firstRepresentationIndex] using hone
      have hshift :
          (firstRepresentationIndex (N + 1) (N + 2)).tailShift =
            secondRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simp only [RepresentationIndex.tailShift_val,
          firstRepresentationIndex, secondRepresentationIndex]
      have hfirstOrder :
          D.normalized.targetTransform.transformed.order
              (0 : Fin (N + 4)) =
            D.normalized.sourceTransform.transformed.order
              (0 : Fin (N + 4)) := by
        unfold GoodBONG.order
        rw [D.normalized.targetTransform.transformed.toBONG.order_eq_ordUnit,
          D.normalized.sourceTransform.transformed.toBONG.order_eq_ordUnit]
        exact congrArg (ordUnit K) (by
          apply Units.ext
          exact D.normalized.headValue_eq)
      rw [hi, hshift]
      exact representationAlpha_tail_first_le_originalSecond_of_largeDefect
        D.normalized.targetTransform.transformed
        D.normalized.sourceTransform.transformed hfirstOrder hdefect
    · have hitwo : i.val = 2 := by omega
      have hi : i = secondRepresentationIndex N (N + 1) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simpa only [secondRepresentationIndex] using hitwo
      rw [hi] at himportant ⊢
      exact representationAlpha_tail_second_le_shift_of_largeDefect
        (alphaV := alphaV) (alphaW := alphaW)
        D.normalized.targetTransform.transformed
        D.normalized.sourceTransform.transformed
        D.normalized.headValue_eq
        (fun k hk ↦
          D.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
        D.sourceAlpha_shift_eq_tail himportant hdefect

/-- If the first-third defect is unchanged by deleting the equal heads, the
same two low boundaries are discharged by exact candidate transport. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.lowTwoReverse_of_defect_eq
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1 =
        D.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed.tail (-1) 2 0) :
    Beli2019Lemma93CaseOneLowTwoReverseCertificate a b D where
  reverseAtImportant i himportant hlow := by
    have hiPos := i.pos
    by_cases hone : i.val = 1
    · letI : Beli2006AlphaLaws.{u, v} K := alphaV
      have hi : i = firstRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simpa only [firstRepresentationIndex] using hone
      have hshift :
          (firstRepresentationIndex (N + 1) (N + 2)).tailShift =
            secondRepresentationIndex (N + 1) (N + 2) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simp only [RepresentationIndex.tailShift_val,
          firstRepresentationIndex, secondRepresentationIndex]
      have hfirstOrder :
          D.normalized.targetTransform.transformed.order
              (0 : Fin (N + 4)) =
            D.normalized.sourceTransform.transformed.order
              (0 : Fin (N + 4)) := by
        unfold GoodBONG.order
        rw [D.normalized.targetTransform.transformed.toBONG.order_eq_ordUnit,
          D.normalized.sourceTransform.transformed.toBONG.order_eq_ordUnit]
        exact congrArg (ordUnit K) (by
          apply Units.ext
          exact D.normalized.headValue_eq)
      rw [hi, hshift]
      exact
        (representationAlpha_tail_first_eq_originalSecond_of_defect_eq
          D.normalized.targetTransform.transformed
          D.normalized.sourceTransform.transformed hfirstOrder hdefect).le
    · have hitwo : i.val = 2 := by omega
      have hi : i = secondRepresentationIndex N (N + 1) := by
        apply representationIndex_eq_of_val_eq_caseOne
        simpa only [secondRepresentationIndex] using hitwo
      rw [hi] at himportant ⊢
      exact representationAlpha_tail_second_le_shift_of_defect_eq
        (alphaV := alphaV) (alphaW := alphaW)
        D.normalized.targetTransform.transformed
        D.normalized.sourceTransform.transformed
        D.normalized.headValue_eq
        (fun k hk ↦
          D.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk)
        D.sourceAlpha_shift_eq_tail himportant hdefect

/-- Promote the two genuinely exceptional Case 1 boundaries to the uniform
low certificate consumed by the Lemma 9.3 assembly. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.toLowReverseCertificate
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (C : Beli2019Lemma93CaseOneLowTwoReverseCertificate a b D) :
    Beli2019Lemma93LowReverseCertificate a b D.normalized where
  reverseAtImportant i himportant hlow := by
    by_cases htwo : i.val ≤ 2
    · exact C.reverseAtImportant i himportant htwo
    · have htarget : ∀ k : Fin (N + 2), 2 ≤ k.1 →
          D.normalized.targetTransform.transformed.alphaValue k.succ =
            D.normalized.targetTransform.transformed.tail.alphaValue k := by
        intro k hk
        exact D.normalized.targetTransform.transformed_laterAlpha_eq_tail k hk
      exact
        (representationAlpha_tail_eq_shift_of_targetLater_sourceAll
          D.normalized.targetTransform.transformed
          D.normalized.sourceTransform.transformed D.normalized.headValue_eq
          htarget D.sourceAlpha_shift_eq_tail i (by omega)).le

/-- The large-defect disjunct, now packaged in the uniform reverse
certificate expected by the ordinary Lemma 9.3 assembly. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.lowReverse_of_largeDefect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      ((((D.normalized.sourceTransform.transformed.order
              (1 : Fin (N + 4)) -
            D.normalized.targetTransform.transformed.order
              (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1) :
    Beli2019Lemma93LowReverseCertificate a b D.normalized :=
  D.toLowReverseCertificate
    (D.lowTwoReverse_of_largeDefect
      (alphaV := alphaV) (alphaW := alphaW) hdefect)

/-- The defect-equality subbranch, packaged in the uniform reverse
certificate expected by the ordinary Lemma 9.3 assembly. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.lowReverse_of_defect_eq
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1 =
        D.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed.tail (-1) 2 0) :
    Beli2019Lemma93LowReverseCertificate a b D.normalized :=
  D.toLowReverseCertificate
    (D.lowTwoReverse_of_defect_eq
      (alphaV := alphaV) (alphaW := alphaW) hdefect)

/-- Complete the three-way arithmetic split of Case 1.  In the low-defect
part, the head-deletion minimum formula leaves either exact defect transport
or the strict branch excluded by `false_of_firstThirdDefect_lt_tail_of_caseOneLow`.
Thus all three displayed alternatives in the paper produce the uniform
reverse certificate required by Lemma 9.3. -/
theorem Beli2019Lemma93CaseOneNormalizedPair.lowReverse_of_caseOne
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseOneCondition b) :
    Beli2019Lemma93LowReverseCertificate a b D.normalized := by
  let a' := D.normalized.targetTransform.transformed
  let b' := D.normalized.sourceTransform.transformed
  have hhead : a'.value 0 = b'.value 0 := D.normalized.headValue_eq
  have hfirst : a'.order (0 : Fin (N + 4)) =
      b'.order (0 : Fin (N + 4)) := by
    unfold GoodBONG.order
    rw [a'.toBONG.order_eq_ordUnit, b'.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (by
      apply Units.ext
      exact hhead)
  have hlemma91' : a'.Lemma91Alternative b' :=
    (a.lemma91Alternative_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a' b b').mp hlemma91
  have hcase' : a'.Beli2019Lemma93CaseOneCondition b' :=
    (a.beli2019Lemma93CaseOneCondition_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a' b b').mp hcase
  have hearly : a'.Lemma92EarlyAlternative →
      a'.alphaValue (2 : Fin (N + 3)) =
        a'.tail.alphaValue (1 : Fin (N + 2)) := by
    intro hearly'
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    have hbefore :
        D.normalized.targetBeforeLemma92.Lemma92EarlyAlternative :=
      (D.normalized.targetBeforeLemma92.lemma92EarlyAlternative_iff a').mpr
        hearly'
    exact D.normalized.targetTransform.transformed_earlyAlpha_eq_tail hbefore
  unfold Beli2019Lemma93CaseOneCondition at hcase'
  by_cases hlarge :
      ((((b'.order (1 : Fin (N + 4)) -
          a'.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        a'.truncatedPrefixDefect b' (-1) 3 1
  · exact D.lowReverse_of_largeDefect
      (alphaV := alphaV) (alphaW := alphaW)
      (classificationV := classificationV) hlarge
  · have hlow : a'.truncatedPrefixDefect b' (-1) 3 1 <
        ((((b'.order (1 : Fin (N + 4)) -
          a'.order (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) :=
      lt_of_not_ge hlarge
    have hcaseLow :
        a'.truncatedPrefixDefect b' (-1) 3 1 <
            (b'.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ∨
          (a'.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
            (b'.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
      rcases hcase' with hbeta | halphaBeta | hlarge'
      · exact Or.inl hbeta
      · exact Or.inr halphaBeta
      · exact (hlarge hlarge').elim
    by_cases hdefect :
        a'.truncatedPrefixDefect b' (-1) 3 1 =
          a'.tail.truncatedPrefixDefect b'.tail (-1) 2 0
    · exact D.lowReverse_of_defect_eq
        (alphaV := alphaV) (alphaW := alphaW)
        (classificationV := classificationV) hdefect
    · have hdecomp :=
        a'.firstThirdDefect_eq_min_tail_alpha_three_beta_one b' hhead
      have hdefectLe : a'.truncatedPrefixDefect b' (-1) 3 1 ≤
          a'.tail.truncatedPrefixDefect b'.tail (-1) 2 0 := by
        rw [hdecomp]
        exact min_le_left _ _
      have hstrictDefect : a'.truncatedPrefixDefect b' (-1) 3 1 <
          a'.tail.truncatedPrefixDefect b'.tail (-1) 2 0 :=
        lt_of_le_of_ne hdefectLe hdefect
      letI : Beli2006AlphaLaws.{u, v} K := alphaV
      exact (a'.false_of_firstThirdDefect_lt_tail_of_caseOneLow b'
        hhead hfirst D.normalized.selectedConditions hearly hlemma91'
        hlow hcaseLow hstrictDefect).elim

/-- End-to-end output of Case 1's large-defect disjunct: the selected BONGs
and the proved reverse inequalities form the exact descent input used by
Lemma 9.3. -/
noncomputable def Beli2019Lemma93CaseOneNormalizedPair.toLemma93Input_of_largeDefect
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      ((((D.normalized.sourceTransform.transformed.order
              (1 : Fin (N + 4)) -
            D.normalized.targetTransform.transformed.order
              (2 : Fin (N + 4)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) ≤
        D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions) :=
  D.normalized.toLemma93Input
    (classificationV := classificationV)
    (classificationW := classificationW) a b ambient conditions
    (D.lowReverse_of_largeDefect
      (alphaV := alphaV) (alphaW := alphaW)
      (classificationV := classificationV) hdefect)

/-- End-to-end output of Case 1's defect-equality subbranch. -/
noncomputable def Beli2019Lemma93CaseOneNormalizedPair.toLemma93Input_of_defect_eq
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hdefect :
      D.normalized.targetTransform.transformed.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed (-1) 3 1 =
        D.normalized.targetTransform.transformed.tail.truncatedPrefixDefect
          D.normalized.sourceTransform.transformed.tail (-1) 2 0) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions) :=
  D.normalized.toLemma93Input
    (classificationV := classificationV)
    (classificationW := classificationW) a b ambient conditions
    (D.lowReverse_of_defect_eq
      (alphaV := alphaV) (alphaW := alphaW)
      (classificationV := classificationV) hdefect)

/-- End-to-end Case 1 output for all three displayed disjuncts in the paper. -/
noncomputable def Beli2019Lemma93CaseOneNormalizedPair.toLemma93Input_of_caseOne
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (D : Beli2019Lemma93CaseOneNormalizedPair a b)
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseOneCondition b) :
    Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions) :=
  D.normalized.toLemma93Input
    (classificationV := classificationV)
    (classificationW := classificationW) a b ambient conditions
    (D.lowReverse_of_caseOne
      (alphaV := alphaV) (alphaW := alphaW)
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      hlemma91 hcase)

/-- Full Case 1 of Lemma 9.3, from the original pair of good BONGs to the
concrete head-reduction input.  This composes Corollary 8.11, Lemmas 9.1 and
9.2, the complete three-way Case 1 arithmetic split, and the ordinary-branch
assembly. -/
theorem exists_beli2019Lemma93Input_caseOne
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b)
    (hcase : a.Beli2019Lemma93CaseOneCondition b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions)) := by
  rcases a.exists_beli2019Lemma93NormalizedPair_caseOne
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      b hfirst ambient conditions hlemma91 with ⟨D⟩
  exact ⟨D.toLemma93Input_of_caseOne
    (alphaV := targetLaws) (alphaW := sourceLaws)
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a b ambient conditions hlemma91 hcase⟩

end BONG.GoodBONG

end Bong
