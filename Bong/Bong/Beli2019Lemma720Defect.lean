/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma720Order
import Bong.Bong.Beli2019Lemma716AtS
import Bong.Bong.Beli2019Lemma716DefectEasy


/-!
# Beli (2019), Section 7 after Lemma 7.19: defect condition

This file proves condition 2.1(ii) for all three replacement normal forms.
It formalizes the nonessential interior ranges, the first and penultimate
boundaries, the stopping boundary, and transport along the common suffix.
The stopping-boundary proof keeps both alpha caps explicit and uses capped
quadratic-defect domination through the original prefix.
-/
namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]

private theorem representationIndex_eq_of_val_eq720
    {m k : Nat} {i j : RepresentationIndex m k} (h : i.val = j.val) :
    i = j := by
  cases i
  cases j
  simp_all

theorem Lemma718TypeINormalForm.notEssential_prefix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (j : Fin (n + 3)) (hjPos : 0 < j.val) (hjNextS : j.val + 1 < s) :
    ¬b.IsEssentialFor c j := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  have hjNext : j.val + 1 < n + 3 := by
    have := D.stopping.le_rank
    omega
  apply b.not_isEssentialFor_of_next_le_previous c j hjPos hjNext
  let previous : Fin (n + 3) := ⟨j.val - 1, by omega⟩
  let next : Fin (n + 3) := ⟨j.val + 1, hjNext⟩
  change b.order next ≤ c.order previous
  rcases Nat.even_or_odd j.val with hjEven | hjOdd
  · rcases hjEven with ⟨d, hd⟩
    have hpreviousOdd : Odd previous.val := by
      exact ⟨d - 1, by dsimp only [previous]; omega⟩
    have hnextOdd : Odd next.val := by
      exact ⟨d, by dsimp only [next]; omega⟩
    have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
      hnorm previous hpreviousOdd
    have htarget := D.targetOrder_odd a b R s next (by
      dsimp only [next]
      exact hjNextS) hnextOdd
    omega
  · rcases hjOdd with ⟨d, hd⟩
    have hpreviousEven : Even previous.val := by
      exact ⟨d, by dsimp only [previous]; omega⟩
    have hnextEven : Even next.val := by
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previous hpreviousEven
    have htarget := D.targetOrder_even a b R s next (by
      dsimp only [next]
      exact hjNextS) hnextEven
    omega

theorem Lemma718TypeIINormalForm.notEssential_prefix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (j : Fin (n + 3)) (hjPos : 0 < j.val) (hjNextS : j.val + 1 < s) :
    ¬b.IsEssentialFor c j := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  have hjNext : j.val + 1 < n + 3 := by
    have := D.stopping.le_rank
    omega
  apply b.not_isEssentialFor_of_next_le_previous c j hjPos hjNext
  let previous : Fin (n + 3) := ⟨j.val - 1, by omega⟩
  let next : Fin (n + 3) := ⟨j.val + 1, hjNext⟩
  change b.order next ≤ c.order previous
  have hnextTwo : ¬next.val < 2 := by
    dsimp only [next]
    omega
  rcases Nat.even_or_odd j.val with hjEven | hjOdd
  · rcases hjEven with ⟨d, hd⟩
    have hpreviousOdd : Odd previous.val := by
      exact ⟨d - 1, by dsimp only [previous]; omega⟩
    have hnextOdd : Odd next.val := by
      exact ⟨d, by dsimp only [next]; omega⟩
    have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
      hnorm previous hpreviousOdd
    have htarget := D.targetOrder_odd a b R s next (by
      dsimp only [next]
      exact hjNextS) hnextOdd
    rw [if_neg hnextTwo] at htarget
    omega
  · rcases hjOdd with ⟨d, hd⟩
    have hpreviousEven : Even previous.val := by
      exact ⟨d, by dsimp only [previous]; omega⟩
    have hnextEven : Even next.val := by
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previous hpreviousEven
    have htarget := D.targetOrder_even a b R s next (by
      dsimp only [next]
      exact hjNextS) hnextEven
    rw [if_neg hnextTwo] at htarget
    omega

theorem Lemma718TypeIIINormalForm.targetOrder_even_le_stopping
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (i : Fin (n + 3)) (his : i.val ≤ s) (hiEven : Even i.val) :
    b.order i = R := by
  by_cases hlt : i.val < s
  · exact D.targetOrder_even a b R s i hlt hiEven
  · have hiEq : i.val = s := by omega
    rcases D.typeIII with ⟨hsRank, hsource⟩
    have htail := D.tailOrder a b R s i (by omega)
    have hindex : i = (⟨s, hsRank⟩ : Fin (n + 3)) := Fin.ext hiEq
    rw [hindex] at htail ⊢
    exact htail.symm.trans hsource

theorem Lemma718TypeIIINormalForm.notEssential_prefix
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (j : Fin (n + 3)) (hjPos : 0 < j.val) (hjS : j.val < s) :
    ¬b.IsEssentialFor c j := by
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  rcases Nat.even_or_odd j.val with hjEven | hjOdd
  · intro hessential
    rcases hjEven with ⟨d, hd⟩
    rcases D.stopping.even with ⟨t, ht⟩
    rcases D.typeIII with ⟨hsRank, _⟩
    have hjNextTwo : j.val + 2 < n + 3 := by
      omega
    have hstrict := hessential.2 (by omega) hjNextTwo
    simp only [orderSequence_at] at hstrict
    let previousTwo : Fin (n + 3) := ⟨j.val - 2, by omega⟩
    let previousOne : Fin (n + 3) := ⟨j.val - 1, by omega⟩
    let nextOne : Fin (n + 3) := ⟨j.val + 1, by omega⟩
    let nextTwo : Fin (n + 3) := ⟨j.val + 2, hjNextTwo⟩
    have hpreviousTwoEven : Even previousTwo.val := by
      exact ⟨d - 1, by dsimp only [previousTwo]; omega⟩
    have hpreviousOneOdd : Odd previousOne.val := by
      exact ⟨d - 1, by dsimp only [previousOne]; omega⟩
    have hnextOneOdd : Odd nextOne.val := by
      exact ⟨d, by dsimp only [nextOne]; omega⟩
    have hnextTwoEven : Even nextTwo.val := by
      exact ⟨d + 1, by dsimp only [nextTwo]; omega⟩
    have hpreviousTwo := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previousTwo hpreviousTwoEven
    have hpreviousOne := a.lemma716_comparison_odd_order_ge c R hfirst
      hnorm previousOne hpreviousOneOdd
    have hnextOne := D.targetOrder_odd a b R s nextOne (by
      dsimp only [nextOne]
      omega) hnextOneOdd
    have hnextTwo := D.targetOrder_even_le_stopping a b R s nextTwo (by
      dsimp only [nextTwo]
      omega) hnextTwoEven
    have hstrict' : c.order previousTwo + c.order previousOne <
        b.order nextOne + b.order nextTwo := by
      simpa only [previousTwo, previousOne, nextOne, nextTwo] using hstrict
    omega
  · rcases hjOdd with ⟨d, hd⟩
    rcases D.typeIII with ⟨hsRank, _⟩
    have hjNext : j.val + 1 < n + 3 := by
      omega
    apply b.not_isEssentialFor_of_next_le_previous c j hjPos hjNext
    let previous : Fin (n + 3) := ⟨j.val - 1, by omega⟩
    let next : Fin (n + 3) := ⟨j.val + 1, hjNext⟩
    change b.order next ≤ c.order previous
    have hpreviousEven : Even previous.val := by
      exact ⟨d, by dsimp only [previous]; omega⟩
    have hnextEven : Even next.val := by
      exact ⟨d + 1, by dsimp only [next]; omega⟩
    have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previous hpreviousEven
    have htarget := D.targetOrder_even_le_stopping a b R s next (by
      dsimp only [next]
      rcases D.stopping.even with ⟨t, ht⟩
      omega) hnextEven
    omega

theorem Lemma718TypeINormalForm.firstRepresentationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectAt c
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := 1, pos := by omega, lt_large := by omega,
      le_small := by omega }
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  have htarget := D.targetOrder_odd a b R s (1 : Fin (n + 3)) (by
    change 1 < s
    have := D.stopping.two_le
    omega) (by
      change Odd (1 : Nat)
      exact ⟨0, by omega⟩)
  have hcomparison := a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order (1 : Fin (n + 3)) +
      2 * (ramificationIndex K : Int) ≤ c.order (0 : Fin (n + 3))
  omega

theorem Lemma718TypeIINormalForm.firstRepresentationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectAt c
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := 1, pos := by omega, lt_large := by omega,
      le_small := by omega }
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  have htarget := D.targetOrder_odd a b R s (1 : Fin (n + 3)) (by
    change 1 < s
    have := D.stopping.two_le
    omega) (by
      change Odd (1 : Nat)
      exact ⟨0, by omega⟩)
  have hcomparison := a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order (1 : Fin (n + 3)) +
      2 * (ramificationIndex K : Int) ≤ c.order (0 : Fin (n + 3))
  omega

theorem Lemma718TypeIIINormalForm.firstRepresentationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectAt c
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := 1, pos := by omega, lt_large := by omega,
      le_small := by omega }
  let current : Fin (n + 3) := ⟨1, by omega⟩
  let previous : Fin (n + 3) := ⟨0, by omega⟩
  let beta : Fin (n + 2) := ⟨1, by omega⟩
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      have := D.stopping.two_le
      omega) (by simp)
  have hcurrent : b.order current =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    exact D.targetOrder_odd a b R s current (by
      dsimp only [current]
      have := D.stopping.two_le
      omega) (by exact ⟨0, by dsimp only [current]; omega⟩)
  have hnext : b.order (2 : Fin (n + 3)) = R := by
    exact D.targetOrder_even_le_stopping a b R s (2 : Fin (n + 3)) (by
      change 2 ≤ s
      exact D.stopping.two_le) (by
        change Even (2 : Nat)
        exact ⟨1, by omega⟩)
  have hgap : b.orderGap beta =
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap
    change b.order (2 : Fin (n + 3)) - b.order current = _
    rw [hnext, hcurrent]
    ring
  have hattains : b.alphaValue beta = b.halfGapValue beta :=
    b.beli2009Corollary29_i beta (Or.inr (Or.inr (Or.inr hgap)))
  have hhalf : b.halfGapValue beta =
      2 * (ramificationIndex K : ℚ) - 1 := by
    unfold halfGapValue
    rw [hgap]
    push_cast
    ring
  have hbeta : b.alphaValue beta =
      2 * (ramificationIndex K : ℚ) - 1 := by
    rw [hattains, hhalf]
  have hcomparison := a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  have harith :
      (((b.order current - c.order previous : Int) : ℚ) +
        b.alphaValue beta) ≤ 0 := by
    rw [hcurrent, hbeta]
    have hcomparisonQ : ((R + 1 : Int) : ℚ) ≤
        (c.order previous : ℚ) := by
      exact_mod_cast hcomparison
    push_cast at hcomparisonQ ⊢
    linarith
  unfold RepresentationDefectAt
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ ≤ ((((b.order current - c.order previous : Int) : ℚ) :
          WithTop ℚ) + (b.alphaValue beta : WithTop ℚ)) := by
      unfold representationPrimaryDefect
      have hcap := b.truncatedPrefixDefect_le_leftCap c (-1)
        (i.val + 1) (i.val - 1)
      rw [b.prefixAlphaCap_of_internal (by dsimp only [i]; omega)
        (by dsimp only [i]; omega)] at hcap
      simpa only [i, current, previous, beta] using
        add_le_add_right hcap
          ((((b.order current - c.order previous : Int) : ℚ) :
            WithTop ℚ))
    _ ≤ ((0 : ℚ) : WithTop ℚ) := by exact_mod_cast harith
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

/-- The common middle-prefix argument for condition (ii) at `i = s`. -/
theorem representationDefectAt_at_stopping_of_prefixIsometric
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (hsPos : 0 < s) (hsInterior : s < n + 3)
    (hac : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (hattains : b.alphaValue ⟨s - 1, by omega⟩ =
      b.halfGapValue ⟨s - 1, by omega⟩) :
    b.RepresentationDefectAt c
      { val := s, pos := hsPos, lt_large := hsInterior,
        le_small := hsInterior.le } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s, pos := hsPos, lt_large := hsInterior,
      le_small := hsInterior.le }
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  have hAlpha : a.representationAlpha c i = b.representationAlpha c i :=
    a.lemma716_tail_representationAlpha_eq b c s horders halphas
      (fun k hsk hk ↦ hprefix k (by omega) hk) i le_rfl
  have hsource : a.RepresentationDefectAt c i :=
    ((a.representationDefectCondition_iff_forall_at c).mp hac) i
  have hbValue :=
    b.representationAlphaValue_le_sourceAlpha_of_attainsHalfGap
      c horderBC i (by simpa only [i, boundary] using hattains)
  have hbTop : b.representationAlpha c i ≤
      (b.alphaValue boundary : WithTop ℚ) := by
    rw [← b.coe_representationAlphaValue c i]
    exact WithTop.coe_le_coe.mpr hbValue
  have hbCap : b.representationAlpha c i ≤ b.prefixAlphaCap s := by
    rw [b.prefixAlphaCap_of_internal hsPos hsInterior]
    simpa only [boundary] using hbTop
  have haCap : b.representationAlpha c i ≤ a.prefixAlphaCap s := by
    unfold RepresentationDefectAt at hsource
    calc
      b.representationAlpha c i = a.representationAlpha c i := hAlpha.symm
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hsource
      _ ≤ a.prefixAlphaCap s := by
        simpa only [i] using
          a.truncatedPrefixDefect_le_leftCap c 1 i.val i.val
  have hraw : b.representationAlpha c i ≤ defectOrder (K := K)
      (1 * b.prefixProduct s * a.prefixProduct s) := by
    have heq := a.defectOrder_mixedPrefix_eq_of_prefix_isometric
      b a 1 s s hsInterior.le (hprefix s le_rfl hsInterior.le)
    have hsquare : IsSquare
        (1 * a.prefixProduct s * a.prefixProduct s) := by
      refine ⟨a.prefixProduct s, ?_⟩
      simp only [one_mul]
    rw [← heq, defectOrder_eq_top_of_isSquare hsquare]
    exact le_top
  have hmiddle : b.representationAlpha c i ≤
      b.truncatedPrefixDefect a 1 s s := by
    unfold truncatedPrefixDefect
    exact le_min hraw (le_min hbCap haCap)
  simpa only [i] using
    representationDefectAt_of_middlePrefix a b c i hAlpha hsource
      (by simpa only [i] using hmiddle)

theorem Lemma718TypeINormalForm.stoppingBoundaryAttainsHalfGap
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hsInterior : s < n + 3) :
    b.alphaValue ⟨s - 1, by omega⟩ =
      b.halfGapValue ⟨s - 1, by omega⟩ := by
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  let right : Fin (n + 3) := ⟨s, hsInterior⟩
  rcases D.stopping.even with ⟨d, hd⟩
  have hleftOdd : Odd left.val := by
    change Odd (s - 1)
    exact ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
  have hleft := D.targetOrder_odd a b R s left (by
    dsimp only [left]
    have := D.stopping.two_le
    omega) hleftOdd
  have hsourceRight : R + 1 ≤ a.order right := by
    rcases D.typeI.1 with hfull | ⟨hs, habove⟩
    · omega
    · have hindex : right = (⟨s, hs⟩ : Fin (n + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      omega
  have hrightEq := D.tailOrder a b R s right le_rfl
  have hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap boundary := by
    unfold orderGap
    have hcast : boundary.castSucc = left := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = right := by
      apply Fin.ext
      simp only [boundary, right, Fin.val_succ]
      have := D.stopping.two_le
      omega
    rw [hcast, hsucc]
    omega
  simpa only [boundary] using b.beli2009Lemma27_ii boundary hgap

theorem Lemma718TypeIINormalForm.stoppingBoundaryAttainsHalfGap
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hsInterior : s < n + 3) :
    b.alphaValue ⟨s - 1, by omega⟩ =
      b.halfGapValue ⟨s - 1, by omega⟩ := by
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  let right : Fin (n + 3) := ⟨s, hsInterior⟩
  rcases D.stopping.even with ⟨d, hd⟩
  have hleftOdd : Odd left.val := by
    change Odd (s - 1)
    exact ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
  have hleft := D.targetOrder_odd a b R s left (by
    dsimp only [left]
    have := D.stopping.two_le
    omega) hleftOdd
  have hsourceRight : R + 1 ≤ a.order right := by
    rcases D.typeII.1 with hfull | ⟨hs, habove⟩
    · omega
    · have hindex : right = (⟨s, hs⟩ : Fin (n + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      omega
  have hrightEq := D.tailOrder a b R s right le_rfl
  have hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap boundary := by
    unfold orderGap
    have hcast : boundary.castSucc = left := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = right := by
      apply Fin.ext
      simp only [boundary, right, Fin.val_succ]
      have := D.stopping.two_le
      omega
    rw [hcast, hsucc]
    split at hleft <;> omega
  simpa only [boundary] using b.beli2009Lemma27_ii boundary hgap

theorem Lemma718TypeIIINormalForm.stoppingBoundaryAttainsHalfGap
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s) :
    b.alphaValue ⟨s - 1, by
      rcases D.typeIII with ⟨hs, _⟩
      omega⟩ =
      b.halfGapValue ⟨s - 1, by
        rcases D.typeIII with ⟨hs, _⟩
        omega⟩ := by
  rcases D.typeIII with ⟨hsInterior, _⟩
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let left : Fin (n + 3) := ⟨s - 1, by omega⟩
  let right : Fin (n + 3) := ⟨s, hsInterior⟩
  rcases D.stopping.even with ⟨d, hd⟩
  have hleftOdd : Odd left.val := by
    change Odd (s - 1)
    exact ⟨d - 1, by
      have := D.stopping.two_le
      omega⟩
  have hleft := D.targetOrder_odd a b R s left (by
    dsimp only [left]
    have := D.stopping.two_le
    omega) hleftOdd
  have hright := D.targetOrder_even_le_stopping a b R s right le_rfl
    (by exact ⟨d, by dsimp only [right]; omega⟩)
  have hgap : b.orderGap boundary =
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap
    have hcast : boundary.castSucc = left := by
      apply Fin.ext
      rfl
    have hsucc : boundary.succ = right := by
      apply Fin.ext
      simp only [boundary, right, Fin.val_succ]
      have := D.stopping.two_le
      omega
    rw [hcast, hsucc]
    rw [hright, hleft]
    ring
  have hattains := b.beli2009Corollary29_i boundary
    (Or.inr (Or.inr (Or.inr hgap)))
  simpa only [boundary] using hattains

theorem Lemma718TypeINormalForm.penultimateRepresentationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hsThree : 3 ≤ s) :
    b.RepresentationDefectAt c
      { val := s - 1, pos := by omega,
        lt_large := by have := D.stopping.le_rank; omega,
        le_small := by have := D.stopping.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1, pos := by omega,
      lt_large := by have := D.stopping.le_rank; omega,
      le_small := by have := D.stopping.le_rank; omega }
  let current : Fin (n + 3) := ⟨s - 1, by
    have := D.stopping.le_rank
    omega⟩
  let previous : Fin (n + 3) := ⟨s - 2, by
    have := D.stopping.le_rank
    omega⟩
  rcases D.stopping.even with ⟨d, hd⟩
  have hcurrentOdd : Odd current.val := by
    change Odd (s - 1)
    exact ⟨d - 1, by omega⟩
  have hpreviousEven : Even previous.val := by
    change Even (s - 2)
    exact ⟨d - 1, by omega⟩
  have hcurrent := D.targetOrder_odd a b R s current (by
    dsimp only [current]
    omega) hcurrentOdd
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      omega) (by simp)
  have hprevious := a.lemma716_comparison_even_order_ge c R hfirst hnorm
    previous hpreviousEven
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order current + 2 * (ramificationIndex K : Int) ≤
    c.order previous
  omega

theorem Lemma718TypeIINormalForm.penultimateRepresentationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hsThree : 3 ≤ s) :
    b.RepresentationDefectAt c
      { val := s - 1, pos := by omega,
        lt_large := by have := D.stopping.le_rank; omega,
        le_small := by have := D.stopping.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 1, pos := by omega,
      lt_large := by have := D.stopping.le_rank; omega,
      le_small := by have := D.stopping.le_rank; omega }
  let current : Fin (n + 3) := ⟨s - 1, by
    have := D.stopping.le_rank
    omega⟩
  let previous : Fin (n + 3) := ⟨s - 2, by
    have := D.stopping.le_rank
    omega⟩
  rcases D.stopping.even with ⟨d, hd⟩
  have hcurrentOdd : Odd current.val := by
    change Odd (s - 1)
    exact ⟨d - 1, by omega⟩
  have hpreviousEven : Even previous.val := by
    change Even (s - 2)
    exact ⟨d - 1, by omega⟩
  have hcurrent := D.targetOrder_odd a b R s current (by
    dsimp only [current]
    omega) hcurrentOdd
  have hnotInitial : ¬current.val < 2 := by
    dsimp only [current]
    omega
  rw [if_neg hnotInitial] at hcurrent
  have hfirst : a.order 0 = R :=
    D.sourceOrder_even a b R s ⟨0, by omega⟩ (by
      change 0 < s
      omega) (by simp)
  have hprevious := a.lemma716_comparison_even_order_ge c R hfirst hnorm
    previous hpreviousEven
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order current + 2 * (ramificationIndex K : Int) ≤
    c.order previous
  omega

theorem Lemma718TypeINormalForm.representationDefectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectCondition c := by
  let normal : Beli2019Lemma718NormalForm a b R s :=
    Beli2019Lemma718NormalForm.typeI D
  let h719 := beli2019Lemma719_of_normalForm a b R s normal
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have horders : ∀ j, s ≤ j.val → a.order j = b.order j :=
    fun j hsj ↦ D.tailOrder a b R s j hsj
  have halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j :=
    fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj
  have hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk) :=
    fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k hsk hk
  rw [b.representationDefectCondition_iff_forall_at c]
  intro i
  by_cases hiFirst : i.val = 1
  · let first : RepresentationIndex (n + 3) (n + 3) :=
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega }
    have hi : i = first := representationIndex_eq_of_val_eq720 hiFirst
    rw [hi]
    exact D.firstRepresentationDefectAt a b c R s hnorm
  by_cases hiTail : s + 1 ≤ i.val
  · exact a.lemma716_tail_representationDefectAt b c s
      hac.defectCondition horders halphas
      (fun k hsk hk ↦ hprefix k (by omega) hk) i hiTail
  by_cases hiStop : i.val = s
  · have hsInterior : s < n + 3 := by
      have hiLt := i.lt_large
      omega
    let stop : RepresentationIndex (n + 3) (n + 3) :=
      { val := s, pos := by have := D.stopping.two_le; omega,
        lt_large := hsInterior, le_small := hsInterior.le }
    have hi : i = stop := representationIndex_eq_of_val_eq720 hiStop
    rw [hi]
    exact representationDefectAt_at_stopping_of_prefixIsometric
      a b c s (by have := D.stopping.two_le; omega) hsInterior
      hac.defectCondition horderBC horders halphas hprefix
      (D.stoppingBoundaryAttainsHalfGap a b R s hsInterior)
  by_cases hiPrevious : i.val = s - 1
  · have hsThree : 3 ≤ s := by
      have hiPos := i.pos
      have hsTwo := D.stopping.two_le
      omega
    let previous : RepresentationIndex (n + 3) (n + 3) :=
      { val := s - 1, pos := by omega,
        lt_large := by have := D.stopping.le_rank; omega,
        le_small := by have := D.stopping.le_rank; omega }
    have hi : i = previous :=
      representationIndex_eq_of_val_eq720 hiPrevious
    rw [hi]
    exact D.penultimateRepresentationDefectAt a b c R s hnorm hsThree
  have hiTwo : 1 < i.val := by
    have hiPos := i.pos
    omega
  have hiNextS : i.val + 1 < s := by
    omega
  apply b.representationDefectAt_of_not_essential c i
  · apply D.notEssential_prefix a b c R s hnorm (currentEssentialIndex i)
    · change 0 < i.val - 1
      omega
    · change (i.val - 1) + 1 < s
      omega
  · apply D.notEssential_prefix a b c R s hnorm (nextEssentialIndex i)
    · change 0 < i.val
      exact i.pos
    · change i.val + 1 < s
      exact hiNextS

theorem Lemma718TypeIINormalForm.representationDefectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectCondition c := by
  let normal : Beli2019Lemma718NormalForm a b R s :=
    Beli2019Lemma718NormalForm.typeII D
  let h719 := beli2019Lemma719_of_normalForm a b R s normal
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have horders : ∀ j, s ≤ j.val → a.order j = b.order j :=
    fun j hsj ↦ D.tailOrder a b R s j hsj
  have halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j :=
    fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj
  have hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk) :=
    fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k hsk hk
  rw [b.representationDefectCondition_iff_forall_at c]
  intro i
  by_cases hiFirst : i.val = 1
  · let first : RepresentationIndex (n + 3) (n + 3) :=
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega }
    have hi : i = first := representationIndex_eq_of_val_eq720 hiFirst
    rw [hi]
    exact D.firstRepresentationDefectAt a b c R s hnorm
  by_cases hiTail : s + 1 ≤ i.val
  · exact a.lemma716_tail_representationDefectAt b c s
      hac.defectCondition horders halphas
      (fun k hsk hk ↦ hprefix k (by omega) hk) i hiTail
  by_cases hiStop : i.val = s
  · have hsInterior : s < n + 3 := by
      have hiLt := i.lt_large
      omega
    let stop : RepresentationIndex (n + 3) (n + 3) :=
      { val := s, pos := by have := D.stopping.two_le; omega,
        lt_large := hsInterior, le_small := hsInterior.le }
    have hi : i = stop := representationIndex_eq_of_val_eq720 hiStop
    rw [hi]
    exact representationDefectAt_at_stopping_of_prefixIsometric
      a b c s (by have := D.stopping.two_le; omega) hsInterior
      hac.defectCondition horderBC horders halphas hprefix
      (D.stoppingBoundaryAttainsHalfGap a b R s hsInterior)
  by_cases hiPrevious : i.val = s - 1
  · have hsThree : 3 ≤ s := by
      have hiPos := i.pos
      have hsTwo := D.stopping.two_le
      omega
    let previous : RepresentationIndex (n + 3) (n + 3) :=
      { val := s - 1, pos := by omega,
        lt_large := by have := D.stopping.le_rank; omega,
        le_small := by have := D.stopping.le_rank; omega }
    have hi : i = previous :=
      representationIndex_eq_of_val_eq720 hiPrevious
    rw [hi]
    exact D.penultimateRepresentationDefectAt a b c R s hnorm hsThree
  have hiTwo : 1 < i.val := by
    have hiPos := i.pos
    omega
  have hiNextS : i.val + 1 < s := by omega
  apply b.representationDefectAt_of_not_essential c i
  · apply D.notEssential_prefix a b c R s hnorm (currentEssentialIndex i)
    · change 0 < i.val - 1
      omega
    · change (i.val - 1) + 1 < s
      omega
  · apply D.notEssential_prefix a b c R s hnorm (nextEssentialIndex i)
    · change 0 < i.val
      exact i.pos
    · change i.val + 1 < s
      exact hiNextS

theorem Lemma718TypeIIINormalForm.representationDefectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma718TypeIIINormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectCondition c := by
  let normal : Beli2019Lemma718NormalForm a b R s :=
    Beli2019Lemma718NormalForm.typeIII D
  let h719 := beli2019Lemma719_of_normalForm a b R s normal
  have horderBC := D.representationOrderCondition a b c R s
    hac.orderCondition hnorm
  have horders : ∀ j, s ≤ j.val → a.order j = b.order j :=
    fun j hsj ↦ D.tailOrder a b R s j hsj
  have halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j :=
    fun j hsj ↦ h719.alphaValue_eq_of_s_le a b R s j hsj
  have hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk) :=
    fun k hsk hk ↦ h719.prefixIsometric_of_s_le a b R s k hsk hk
  rw [b.representationDefectCondition_iff_forall_at c]
  intro i
  by_cases hiFirst : i.val = 1
  · let first : RepresentationIndex (n + 3) (n + 3) :=
      { val := 1, pos := by omega, lt_large := by omega,
        le_small := by omega }
    have hi : i = first := representationIndex_eq_of_val_eq720 hiFirst
    rw [hi]
    exact D.firstRepresentationDefectAt a b c R s hnorm
  by_cases hiTail : s + 1 ≤ i.val
  · exact a.lemma716_tail_representationDefectAt b c s
      hac.defectCondition horders halphas
      (fun k hsk hk ↦ hprefix k (by omega) hk) i hiTail
  by_cases hiStop : i.val = s
  · rcases D.typeIII with ⟨hsInterior, _⟩
    let stop : RepresentationIndex (n + 3) (n + 3) :=
      { val := s, pos := by have := D.stopping.two_le; omega,
        lt_large := hsInterior, le_small := hsInterior.le }
    have hi : i = stop := representationIndex_eq_of_val_eq720 hiStop
    rw [hi]
    exact representationDefectAt_at_stopping_of_prefixIsometric
      a b c s (by have := D.stopping.two_le; omega) hsInterior
      hac.defectCondition horderBC horders halphas hprefix
      (by simpa using D.stoppingBoundaryAttainsHalfGap a b R s)
  have hiTwo : 1 < i.val := by
    have hiPos := i.pos
    omega
  have hiS : i.val < s := by omega
  apply b.representationDefectAt_of_not_essential c i
  · apply D.notEssential_prefix a b c R s hnorm (currentEssentialIndex i)
    · change 0 < i.val - 1
      omega
    · change i.val - 1 < s
      omega
  · apply D.notEssential_prefix a b c R s hnorm (nextEssentialIndex i)
    · change 0 < i.val
      exact i.pos
    · change i.val < s
      exact hiS

/-- Condition 2.1(ii) survives all three replacements in Lemma 7.18. -/
theorem Beli2019Lemma718NormalForm.representationDefectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Beli2019Lemma718NormalForm a b R s)
    (hac : RepresentationConditions a c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationDefectCondition c := by
  cases D with
  | typeI data =>
      exact data.representationDefectCondition a b c R s hac hnorm
  | typeII data =>
      exact data.representationDefectCondition a b c R s hac hnorm
  | typeIII data =>
      exact data.representationDefectCondition a b c R s hac hnorm

end BONG.GoodBONG

end Bong
