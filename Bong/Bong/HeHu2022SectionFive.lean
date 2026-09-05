/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022Theorem41
import Bong.Bong.HeHu2022Lemma211

/-!
# He--Hu 2022, Section 5: odd-rank conditions

This file starts the source-numbered formalization of Section 5 of Zilong He
and Yong Hu, *On n-universal quadratic forms over dyadic local fields*,
Sci. China Math. 67 (2024), 1481--1506.  Paper indices are one based; the
`Fin` indices below are zero based.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {r : QuadraticSpace K W} {M : Lattice K W}

namespace BONG.GoodBONG

/-- The integer `G_n` in He--Hu, equation (5.1).  The source writes it as
`2(e-floor((R_(n+2)-R_(n+1))/2))-1`; the displayed parity split is used here
so that the two source branches remain visible. -/
noncomputable def heHuOddThreshold {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (_hm : n + 2 ≤ m) : Int :=
  let gap := a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩
  if Even gap then
    2 * (ramificationIndex K : Int) -
      a.order ⟨n + 1, by omega⟩ + a.order ⟨n, by omega⟩ - 1
  else
    2 * (ramificationIndex K : Int) -
      a.order ⟨n + 1, by omega⟩ + a.order ⟨n, by omega⟩

/-- He--Hu, Theorem 5.1, condition `I1^O(n)`. -/
def HeHuI1O {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (_hn : 3 ≤ n) (hm : n + 2 ≤ m) : Prop :=
  (∀ i : Fin n, Odd (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ = 0) ∧
    (∀ i : Fin n, Even (i.1 + 1) →
      a.order ⟨i.1, by omega⟩ =
        -(2 * (ramificationIndex K : Int))) ∧
    (a.alphaValue ⟨n - 1, by omega⟩ = 0 ∨
      a.alphaValue ⟨n - 1, by omega⟩ = 1)

/-- He--Hu, Theorem 5.1, condition `I2^O(n)`, including both of its
published implications. -/
noncomputable def HeHuI2O {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (_hn : 3 ≤ n) (hm : n + 2 ≤ m) : Prop :=
  (a.alphaValue ⟨n - 1, by omega⟩ = 0 →
      a.order ⟨n + 1, by omega⟩ = 0 ∨
        a.order ⟨n + 1, by omega⟩ = 1) ∧
    (a.alphaValue ⟨n - 1, by omega⟩ = 1 →
      (a.order ⟨n, by omega⟩ = 1 ∨
        1 < a.order ⟨n + 1, by omega⟩) →
      a.alphaValue ⟨n + 1, by omega⟩ ≤
        (a.heHuOddThreshold n hm : ℚ))

/-- He--Hu, Theorem 5.1, condition `I3^O(n)`. -/
def HeHuI3O {m : Nat} (a : GoodBONG q L (m + 1))
    (n : Nat) (_hn : 3 ≤ n) (_hm : n + 2 ≤ m) : Prop :=
  a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ ≤
    2 * (ramificationIndex K : Int)

/-- The three odd-rank invariant conditions in He--Hu, Theorem 5.1. -/
structure HeHuOddSectionConditions {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat)
    (hn : 3 ≤ n) (hm : n + 2 ≤ m) : Prop where
  i1 : a.HeHuI1O n hn hm
  i2 : a.HeHuI2O n hn hm
  i3 : a.HeHuI3O n hn hm

/-- `I1^O(n)` contains `I1^E(n-1)`, as used at the start of the proof of
Theorem 5.1. -/
theorem HeHuI1O.toI1E {m n : Nat} {a : GoodBONG q L (m + 1)}
    {hn : 3 ≤ n} {hm : n + 2 ≤ m}
    (h : a.HeHuI1O n hn hm) :
    a.HeHuI1E (n - 1) (by omega) := by
  constructor
  · intro i hi
    exact h.1 ⟨i.1, by omega⟩ hi
  · intro i hi
    exact h.2.1 ⟨i.1, by omega⟩ hi

/-- Conversely, `I1^E(n-1)` plus `alpha_n in {0,1}` is precisely
`I1^O(n)`. -/
theorem heHuI1O_iff_i1E_and_alpha {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) :
    a.HeHuI1O n hn hm ↔
      a.HeHuI1E (n - 1) (by omega) ∧
        (a.alphaValue ⟨n - 1, by omega⟩ = 0 ∨
          a.alphaValue ⟨n - 1, by omega⟩ = 1) := by
  constructor
  · intro h
    exact ⟨h.toI1E, h.2.2⟩
  · rintro ⟨hE, hAlpha⟩
    refine ⟨?_, ?_, hAlpha⟩
    · intro i hi
      exact hE.1 ⟨i.1, by omega⟩ hi
    · intro i hi
      rcases hi with ⟨r, hr⟩
      rcases hnOdd with ⟨s, hs⟩
      exact hE.2 ⟨i.1, by omega⟩ ⟨r, hr⟩

/-- If the boundary gap is at least `2e`, equation (5.1) makes `G_n`
strictly negative.  This is the numerical contradiction used in Lemma 5.4. -/
theorem heHuOddThreshold_lt_zero_of_two_e_le_gap {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hm : n + 2 ≤ m)
    (hgap : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩) :
    a.heHuOddThreshold n hm < 0 := by
  let gap := a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩
  by_cases hEven : Even gap
  · simp only [heHuOddThreshold, gap, hEven, if_pos]
    omega
  · have htwoE : Even (2 * (ramificationIndex K : Int)) :=
      ⟨ramificationIndex K, by ring⟩
    have hne : 2 * (ramificationIndex K : Int) ≠ gap := by
      intro heq
      apply hEven
      rw [← heq]
      exact htwoE
    have hstrict : 2 * (ramificationIndex K : Int) < gap :=
      lt_of_le_of_ne hgap hne
    simp only [heHuOddThreshold, gap, hEven]
    omega

/-- The paper-order `R_n` is zero under `I1^E(n-1)` when `n` is odd. -/
theorem HeHuI1E.oddBoundaryOrder {m n : Nat}
    {a : GoodBONG q L (m + 1)} (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (h : a.HeHuI1E (n - 1) (by omega)) :
    a.order ⟨n - 1, by omega⟩ = 0 := by
  have hindex : n - 1 + 1 = n := by omega
  exact h.oddOrder ⟨n - 1, by omega⟩ (by rw [hindex]; exact hnOdd)

/-- He--Hu, Lemma 5.4(i). -/
theorem heHu2022Lemma54i {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hI1 : a.HeHuI1E (n - 1) (by omega))
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 0) :
    a.order ⟨n, by omega⟩ = -(2 * (ramificationIndex K : Int)) := by
  let boundary : Fin m := ⟨n - 1, by omega⟩
  have hRn := hI1.oddBoundaryOrder hn hnOdd hm
  have hgap := (a.heHu2022Proposition26 boundary).alphaZero.mp hAlpha
  have hsucc : boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    simp only [Fin.val_succ, boundary]
    omega
  have hcast : boundary.castSucc = (⟨n - 1, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  unfold orderGap at hgap
  rw [hsucc, hcast] at hgap
  rw [hRn] at hgap
  omega

/-- The first assertion of He--Hu, Lemma 5.4(ii). -/
theorem heHu2022Lemma54ii_gap {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hI1 : a.HeHuI1E (n - 1) (by omega))
    (hI2 : a.HeHuI2O n hn hm)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1) :
    a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ ≤
      2 * (ramificationIndex K : Int) - 1 := by
  let boundary : Fin m := ⟨n - 1, by omega⟩
  have hRn := hI1.oddBoundaryOrder hn hnOdd hm
  have hboundaryGap : a.orderGap boundary = a.order ⟨n, by omega⟩ := by
    have hsucc : boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, boundary]
      omega
    have hcast : boundary.castSucc = (⟨n - 1, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    unfold orderGap
    rw [hsucc, hcast]
    rw [hRn]
    omega
  have hshape := (a.heHu2022Proposition26 boundary).alphaOne hAlpha |>.1
  rw [hboundaryGap] at hshape
  by_contra hnot
  have hgap : 2 * (ramificationIndex K : Int) ≤
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by
    omega
  have htrigger : a.order ⟨n, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 1, by omega⟩ := by
    rcases hshape with hOne | hEvenRange
    · exact Or.inl hOne
    · exact Or.inr (by omega)
  have hAlphaBound := hI2.2 hAlpha htrigger
  have hGneg := a.heHuOddThreshold_lt_zero_of_two_e_le_gap hm hgap
  have hGnegQ : (a.heHuOddThreshold n hm : ℚ) < 0 := by
    exact_mod_cast hGneg
  have hAlphaNonnegative := a.zero_le_alphaValue ⟨n + 1, by omega⟩
  exact (not_lt_of_ge hAlphaNonnegative) (hAlphaBound.trans_lt hGnegQ)

/-- The exceptional final assertion of He--Hu, Lemma 5.4(ii). -/
theorem heHu2022Lemma54ii_nextAlpha {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n - 1) (by omega))
    (hI2 : a.HeHuI2O n hn hm)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1)
    (hRn1 : a.order ⟨n, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int)) :
    a.alphaValue ⟨n, by omega⟩ =
      2 * (ramificationIndex K : ℚ) - 1 := by
  have hgapUpper := a.heHu2022Lemma54ii_gap hn hnOdd hm hI1 hI2 hAlpha
  have hn1Even : Even (n + 1) := by
    rcases hnOdd with ⟨r, hr⟩
    exact ⟨r + 1, by omega⟩
  have hRn2Nonnegative : 0 ≤ a.order ⟨n + 1, by omega⟩ :=
    (a.heHu2022Proposition27i hIntegral).oddIndexed
      ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩ (le_refl _)
      hn1Even hn1Even |>.1
  let next : Fin m := ⟨n, by omega⟩
  have hnextGap : a.orderGap next =
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by
    have hsucc : next.succ = (⟨n + 1, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    have hcast : next.castSucc = (⟨n, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    unfold orderGap
    rw [hsucc, hcast]
  have hgapLower : 2 * (ramificationIndex K : Int) - 2 ≤
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by
    rw [hRn1]
    omega
  have hgapCases :
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ =
          2 * (ramificationIndex K : Int) - 2 ∨
        a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ =
          2 * (ramificationIndex K : Int) - 1 := by
    omega
  rcases hgapCases with hgap | hgap
  · have hhalf := (a.heHu2022Proposition26 next).halfGap
      (Or.inr (Or.inr (Or.inr (hnextGap.trans hgap))))
    calc
      a.alphaValue ⟨n, by omega⟩ = a.halfGapValue next := hhalf
      _ = 2 * (ramificationIndex K : ℚ) - 1 := by
        unfold halfGapValue
        rw [hnextGap, hgap]
        push_cast
        ring
  · have hle : a.orderGap next ≤ 2 * (ramificationIndex K : Int) := by
      rw [hnextGap, hgap]
      omega
    have hodd : Odd (a.orderGap next) := by
      rw [hnextGap, hgap]
      refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
      ring
    have heq := ((a.heHu2022Proposition26 next).lowerBound hle).2.mpr
      (Or.inr hodd)
    calc
      a.alphaValue ⟨n, by omega⟩ = (a.orderGap next : ℚ) := heq
      _ = ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) := by
        rw [hnextGap, hgap]
      _ = 2 * (ramificationIndex K : ℚ) - 1 := by
        push_cast
        ring

/-- The capped-defect equality in He--Hu, Lemma 5.4(ii). -/
theorem heHu2022Lemma54ii_defect {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n - 1) (by omega))
    (hI2 : a.HeHuI2O n hn hm)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1) :
    a.heHuAdjacentCappedDefect ⟨n - 1, by omega⟩ =
      ((((1 : ℚ) - (a.order ⟨n, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) := by
  let boundary : Fin m := ⟨n - 1, by omega⟩
  have hRn := hI1.oddBoundaryOrder hn hnOdd hm
  have hboundaryGap : a.orderGap boundary = a.order ⟨n, by omega⟩ := by
    have hsucc : boundary.succ = (⟨n, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, boundary]
      omega
    have hcast : boundary.castSucc = (⟨n - 1, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    unfold orderGap
    rw [hsucc, hcast, hRn]
    omega
  have hOne := (a.heHu2022Proposition26 boundary).alphaOne hAlpha
  by_cases hExceptional : a.order ⟨n, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int)
  · have hnext := a.heHu2022Lemma54ii_nextAlpha hn hnOdd hm hIntegral
      hI1 hI2 hAlpha hExceptional
    have hupper : a.heHuAdjacentCappedDefect boundary ≤
        (a.alphaValue ⟨n, by omega⟩ : WithTop ℚ) := by
      unfold heHuAdjacentCappedDefect
      have hcap := a.truncatedPrefixDefect_le_rightCap
        a (-1) boundary.val (boundary.val + 2)
      have harg : boundary.val + 2 = n + 1 := by
        simp only [boundary]
        omega
      rw [harg] at hcap
      rw [a.prefixAlphaCap_of_internal (i := n + 1)
        (by omega) (by omega)] at hcap
      have hindex :
          (⟨n + 1 - 1, by omega⟩ : Fin m) =
            (⟨n, by omega⟩ : Fin m) := by
        apply Fin.ext
        exact Nat.add_sub_cancel n 1
      rw [hindex] at hcap
      rw [harg]
      exact hcap
    have htarget :
        ((((1 : ℚ) - (a.order ⟨n, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) =
          ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
      have hq :
          (1 : ℚ) - (a.order ⟨n, by omega⟩ : ℚ) =
            2 * (ramificationIndex K : ℚ) - 1 := by
        rw [hExceptional]
        push_cast
        ring
      exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hq
    apply le_antisymm
    · rw [hnext] at hupper
      simpa only [htarget] using hupper
    · have hlower := hOne.2.1
      rw [hboundaryGap] at hlower
      exact hlower
  · have hgapNe : a.orderGap boundary ≠
        2 - 2 * (ramificationIndex K : Int) := by
      rw [hboundaryGap]
      exact hExceptional
    have heq := hOne.2.2 hgapNe
    rw [hboundaryGap] at heq
    exact heq

/-- He--Hu, Lemma 5.4, with both clauses and all assertions in clause (ii). -/
theorem heHu2022Lemma54 {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n - 1) (by omega))
    (hI2 : a.HeHuI2O n hn hm) :
    (a.alphaValue ⟨n - 1, by omega⟩ = 0 →
      a.order ⟨n, by omega⟩ = -(2 * (ramificationIndex K : Int))) ∧
    (a.alphaValue ⟨n - 1, by omega⟩ = 1 →
      a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ ≤
          2 * (ramificationIndex K : Int) - 1 ∧
        a.heHuAdjacentCappedDefect ⟨n - 1, by omega⟩ =
          ((((1 : ℚ) - (a.order ⟨n, by omega⟩ : ℚ)) : ℚ) : WithTop ℚ) ∧
        (a.order ⟨n, by omega⟩ =
            2 - 2 * (ramificationIndex K : Int) →
          a.alphaValue ⟨n, by omega⟩ =
            2 * (ramificationIndex K : ℚ) - 1)) := by
  constructor
  · exact a.heHu2022Lemma54i hn hnOdd hm hI1
  · intro hAlpha
    exact ⟨a.heHu2022Lemma54ii_gap hn hnOdd hm hI1 hI2 hAlpha,
      a.heHu2022Lemma54ii_defect hn hnOdd hm hIntegral hI1 hI2 hAlpha,
      a.heHu2022Lemma54ii_nextAlpha hn hnOdd hm hIntegral hI1 hI2 hAlpha⟩

/-- He--Hu, Lemma 5.6(i): condition (i) of Theorem 2.8 holds for every
integral rank-`n` target. -/
theorem heHu2022Lemma56i {m n : Nat}
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hBIntegral : Lattice.IsIntegral r M) :
    a.RepresentationOrderCondition b (by omega) := by
  intro i
  left
  let C := b.heHu2022Proposition27i hBIntegral
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hiPaperOdd : Odd (i.val + 1) := by
      rcases hiEven with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    have hsource := hI1.oddOrder ⟨i.val, by omega⟩ hiPaperOdd
    have htarget := C.oddIndexed i i (le_refl _) hiEven hiEven |>.1
    rw [hsource]
    exact htarget
  · have hiPaperEven : Even (i.val + 1) := by
      rcases hiOdd with ⟨t, ht⟩
      exact ⟨t + 1, by omega⟩
    have hiBound : i.val < n + 1 := by
      rcases hiOdd with ⟨t, ht⟩
      rcases hnOdd with ⟨s, hs⟩
      omega
    have hsource := hI1.evenOrder ⟨i.val, hiBound⟩ hiPaperEven
    have htarget := C.evenIndexed i i (le_refl _) hiOdd hiOdd |>.1
    rw [hsource]
    exact htarget

/-- A nonterminal odd representation index has nonpositive half-gap under
`I1^E(n-1)`.  This is the uniform form of the first-boundary estimate in
the proof of He--Hu, Lemma 5.6(ii). -/
private theorem heHuLemma56_oddIndexDefect {m n : Nat}
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hBIntegral : Lattice.IsIntegral r M)
    (i : RepresentationIndex (m + 3) (n + 2))
    (hiOdd : Odd i.val) (hiLast : i.val ≠ n + 2) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  have hiBound : i.val < n + 1 := by
    have hiSmall := i.le_small
    rcases hiOdd with ⟨u, hu⟩
    rcases hnOdd with ⟨v, hv⟩
    omega
  have hsource : a.order ⟨i.val, i.lt_large⟩ =
      -(2 * (ramificationIndex K : Int)) := by
    apply hI1.evenOrder ⟨i.val, hiBound⟩
    exact hiOdd.add_one
  have htarget : 0 ≤ b.order ⟨i.val - 1, by omega⟩ := by
    let targetOrders := b.heHu2022Proposition27i hBIntegral
    have hindexEven : Even (i.val - 1) := by
      rcases hiOdd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      omega
    exact (targetOrders.oddIndexed ⟨i.val - 1, by omega⟩
      ⟨i.val - 1, by omega⟩ le_rfl hindexEven hindexEven).1
  have hhalf : a.representationHalfGap b i ≤ 0 := by
    unfold representationHalfGap
    apply WithTop.coe_le_coe.mpr
    have horder : a.order ⟨i.val, i.lt_large⟩ +
        2 * (ramificationIndex K : Int) ≤
          b.order ⟨i.val - 1, by omega⟩ := by
      rw [hsource]
      simpa only [neg_add_cancel] using htarget
    have horderQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
            2 * (ramificationIndex K : ℚ) ≤
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) := by
      exact_mod_cast horder
    push_cast at horderQ ⊢
    linarith
  calc
    (a.representationAlphaValue b i : WithTop ℚ) =
        a.representationAlpha b i := a.coe_representationAlphaValue b i
    _ ≤ a.representationHalfGap b i :=
      a.representationAlpha_le_halfGap b i
    _ ≤ 0 := hhalf
    _ ≤ a.truncatedPrefixDefect b 1 i.val i.val :=
      a.truncatedPrefixDefect_nonneg b 1 i.val i.val

/-- He--Hu, Lemma 5.6(ii): condition (ii) of Theorem 2.8 holds for every
integral rank-`n` target.  The source rank is written as `m+3`, matching the
paper's standing assumption that its quadratic space is `n`-universal. -/
theorem heHu2022Lemma56ii {m n : Nat}
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hI2 : a.HeHuI2E (n + 1) (by omega)) :
    a.RepresentationDefectCondition b := by
  intro i
  by_cases hiLast : i.val = n + 2
  · have hiEq : i =
        ({ val := n + 2
           pos := by omega
           lt_large := by omega
           le_small := by omega } : RepresentationIndex (m + 3) (n + 2)) := by
      apply RepresentationIndex.ext
      exact hiLast
    rw [hiEq]
    let boundary : Fin (m + 2) := ⟨n + 1, by omega⟩
    have hRn : a.order boundary.castSucc = 0 := by
      have h := hI1.oddBoundaryOrder hn hnOdd (by omega)
      change a.order ⟨n + 1, by omega⟩ = 0
      have hindex : (⟨n + 1, by omega⟩ : Fin (m + 3)) =
          ⟨n + 2 - 1, by omega⟩ := by
        apply Fin.ext
        change n + 1 = n + 2 - 1
        omega
      rw [hindex]
      exact h
    have hnBeforeEven : Even (n + 1) := by
      rcases hnOdd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      omega
    by_cases hnext : a.order ⟨n + 2, by omega⟩ =
        -(2 * (ramificationIndex K : Int))
    · have htarget : 0 ≤ b.order ⟨n + 1, by omega⟩ := by
        let targetOrders := b.heHu2022Proposition27i hBIntegral
        exact (targetOrders.oddIndexed ⟨n + 1, by omega⟩
          ⟨n + 1, by omega⟩ le_rfl hnBeforeEven hnBeforeEven).1
      have hhalf : a.representationHalfGap b
          ({ val := n + 2
             pos := by omega
             lt_large := by omega
             le_small := by omega } : RepresentationIndex (m + 3) (n + 2)) ≤ 0 := by
        unfold representationHalfGap
        apply WithTop.coe_le_coe.mpr
        have horder : a.order ⟨n + 2, by omega⟩ +
            2 * (ramificationIndex K : Int) ≤
              b.order ⟨n + 1, by omega⟩ := by
          rw [hnext]
          simpa only [neg_add_cancel] using htarget
        have horderQ : (a.order ⟨n + 2, by omega⟩ : ℚ) +
              2 * (ramificationIndex K : ℚ) ≤
            (b.order ⟨n + 1, by omega⟩ : ℚ) := by
          exact_mod_cast horder
        push_cast at horderQ ⊢
        linarith
      calc
        (a.representationAlphaValue b
            ({ val := n + 2
               pos := by omega
               lt_large := by omega
               le_small := by omega } : RepresentationIndex (m + 3) (n + 2)) :
              WithTop ℚ) =
            a.representationAlpha b _ :=
              a.coe_representationAlphaValue b _
        _ ≤ a.representationHalfGap b _ :=
          a.representationAlpha_le_halfGap b _
        _ ≤ 0 := hhalf
        _ ≤ a.truncatedPrefixDefect b 1 (n + 2) (n + 2) :=
          a.truncatedPrefixDefect_nonneg b 1 (n + 2) (n + 2)
    · rcases hnOdd with ⟨k, hk⟩
      have hkPos : 1 ≤ k := by omega
      let t := k - 1
      have hnForm : n = 2 * t + 1 := by
        simp only [t]
        omega
      have hBefore : a.order ⟨n, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
        apply hI1.evenOrder ⟨n, by omega⟩
        exact hnBeforeEven
      have hAlphaLocal :
          a.alphaValue ⟨n + 1, by omega⟩ = 1 ∧
            a.heHuAdjacentCappedDefect ⟨n + 1, by omega⟩ =
              ((((1 : ℚ) - (a.order ⟨n + 2, by omega⟩ : ℚ)) : ℚ) :
                WithTop ℚ) := by
        rcases hI2 with hzero | hone
        · have hforced := a.heHu2022Lemma54i hn ⟨k, hk⟩ (by omega)
            hI1 hzero
          exact False.elim (hnext hforced)
        · exact hone
      subst n
      have htwo : 2 * t + 1 + 1 = 2 * t + 2 := by omega
      have hthree : 2 * t + 1 + 2 = 2 * t + 3 := by omega
      have hfour : 2 * t + 2 + 2 = 2 * t + 4 := by omega
      have hAlphaExact : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1 := by
        simpa only [htwo] using hAlphaLocal.1
      have hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0 := by
        have hindex : (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) =
            boundary.castSucc := by
          apply Fin.ext
          change 2 * t + 2 = 2 * t + 1 + 1
          omega
        rw [hindex]
        exact hRn
      have hLocal :
          a.truncatedPrefixDefect a (-1) (2 * t + 2) (2 * t + 4) =
            (((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) := by
        have hlocalRaw := hAlphaLocal.2
        unfold heHuAdjacentCappedDefect at hlocalRaw
        simp only [htwo, hthree, hfour] at hlocalRaw
        have hcast :
            ((((1 : ℚ) - (a.order ⟨2 * t + 3, by omega⟩ : ℚ)) : ℚ) :
                WithTop ℚ) =
              (((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
                WithTop ℚ) := by
          norm_cast
        exact hlocalRaw.trans hcast
      have hTerminal := a.heHu2022Lemma211LongSource t b (by omega)
        hAIntegral hBIntegral
        (by simpa only using hBefore)
        hRAt
        hAlphaExact
        hLocal
      have hPrimary : a.representationPrimaryDefect b
          ({ val := 2 * t + 3
             pos := by omega
             lt_large := by omega
             le_small := by omega } : RepresentationIndex (m + 3) (2 * t + 3)) ≤
            a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
        have hpred : 2 * t + 3 - 1 = 2 * t + 2 := by omega
        have hsucc : 2 * t + 3 + 1 = 2 * t + 4 := by omega
        unfold representationPrimaryDefect
        simpa only [hpred, hsucc] using hTerminal
      calc
        (a.representationAlphaValue b
            ({ val := 2 * t + 3
               pos := by omega
               lt_large := by omega
               le_small := by omega } : RepresentationIndex (m + 3) (2 * t + 3)) :
              WithTop ℚ) = a.representationAlpha b _ :=
          a.coe_representationAlphaValue b _
        _ ≤ a.representationPrimaryDefect b _ :=
          a.representationAlpha_le_primary b _
        _ ≤ a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := hPrimary
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiBeforeLast : i.val < n + 2 := by
        have hiSmall := i.le_small
        omega
      have hprev : a.order ⟨i.val - 1, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) := by
        apply hI1.evenOrder ⟨i.val - 1, by omega⟩
        simpa only [Nat.sub_add_cancel i.pos] using hiEven
      have hcurrent : a.order ⟨i.val, i.lt_large⟩ = 0 := by
        apply hI1.oddOrder ⟨i.val, by
          have hiSmall := i.le_small
          rcases hnOdd with ⟨u, hu⟩
          rcases hiEven with ⟨v, hv⟩
          omega⟩
        exact hiEven.add_one
      have hlemma := a.heHu2022Lemma29 b hAIntegral hBIntegral i
        hiEven hprev hcurrent
      simpa only [← a.coe_representationAlphaValue b i] using hlemma
    · exact a.heHuLemma56_oddIndexDefect b hn hnOdd hm hI1
        hBIntegral i hiOdd hiLast

/-- He--Hu, Lemma 5.6, assembled in the paper's quantified form.  The
ambient-space `n`-universality hypothesis is retained even though the two
numerical conclusions only use integrality and the displayed BONG
conditions. -/
theorem heHu2022Lemma56 {m n : Nat}
    (a : GoodBONG q L (m + 3))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (_hAmbient : Lattice.AmbientlyNUniversal.{u, v, w} q (n + 2))
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hI2 : a.HeHuI2E (n + 1) (by omega)) :
    (∀ {W : Type w} [AddCommGroup W] [Module K W]
        {r : QuadraticSpace K W} {M : Lattice K W}
        (b : GoodBONG r M (n + 2)), Lattice.IsIntegral r M →
          a.RepresentationOrderCondition b (by omega)) ∧
      (∀ {W : Type w} [AddCommGroup W] [Module K W]
        {r : QuadraticSpace K W} {M : Lattice K W}
        (b : GoodBONG r M (n + 2)), Lattice.IsIntegral r M →
          a.RepresentationDefectCondition b) := by
  constructor
  · intro W _ _ r M b hB
    exact a.heHu2022Lemma56i b hn hnOdd hm hI1 hB
  · intro W _ _ r M b hB
    exact a.heHu2022Lemma56ii b hn hnOdd hm hAIntegral hB hI1 hI2

/-- The first consequence in Remark 5.2: when `n` is odd,
`R_(n+1)=1` forces `R_(n+2)>=1`. -/
theorem heHu2022Remark52_order_ge_one {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hIntegral : Lattice.IsIntegral q L)
    (hRn1 : a.order ⟨n, by omega⟩ = 1) :
    1 ≤ a.order ⟨n + 1, by omega⟩ := by
  have hn1Even : Even (n + 1) := by
    rcases hnOdd with ⟨r, hr⟩
    exact ⟨r + 1, by omega⟩
  have hnonnegative : 0 ≤ a.order ⟨n + 1, by omega⟩ :=
    (a.heHu2022Proposition27i hIntegral).oddIndexed
      ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩ (le_refl _)
      hn1Even hn1Even |>.1
  by_contra hnot
  have hzero : a.order ⟨n + 1, by omega⟩ = 0 := by omega
  let gap : Fin m := ⟨n, by omega⟩
  have hgap : a.orderGap gap = -1 := by
    unfold orderGap gap
    simp only [Fin.castSucc_mk, Fin.succ_mk]
    rw [hzero, hRn1]
    omega
  have hgapOdd : Odd (a.orderGap gap) := by rw [hgap]; norm_num [Odd]
  have hpositive := (a.heHu2022Corollary23i gap).1 hgapOdd
  rw [hgap] at hpositive
  omega

/-- He--Hu, Remark 5.2. -/
theorem heHu2022Remark52 {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 ≤ n) (hnOdd : Odd n)
    (hm : n + 2 ≤ m) (hIntegral : Lattice.IsIntegral q L) :
    (a.order ⟨n, by omega⟩ = 1 ∨
        1 < a.order ⟨n + 1, by omega⟩) ↔
      ((a.order ⟨n, by omega⟩ = 1 ∧
          a.order ⟨n + 1, by omega⟩ = 1) ∨
        1 < a.order ⟨n + 1, by omega⟩) := by
  constructor
  · rintro (hRn1 | hRn2)
    · have hge := a.heHu2022Remark52_order_ge_one hn hnOdd hm hIntegral hRn1
      rcases lt_or_eq_of_le hge with hgt | heq
      · exact Or.inr hgt
      · exact Or.inl ⟨hRn1, heq.symm⟩
    · exact Or.inr hRn2
  · rintro (h | h)
    · exact Or.inl h.1
    · exact Or.inr h

end BONG.GoodBONG

end Bong
