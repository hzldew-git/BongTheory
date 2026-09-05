/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaP1Proof
import Bong.Bong.Segment

/-!
# Beli (2009/2010), Lemmas 2.1--2.3

This file formalizes localization of the finite candidate set defining
`α_i`, the two monotonicity assertions of Lemma 2.2, and every conclusion of
Corollary 2.3.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Zero-based data `start ≤ pivot < stop` for the segment
`a_start, ..., a_stop` in Lemma 2.1. -/
structure AlphaLocalizationIndex (n : Nat) where
  start : Nat
  pivot : Nat
  stop : Nat
  start_le_pivot : start ≤ pivot
  pivot_lt_stop : pivot < stop
  stop_lt : stop < n + 1

namespace AlphaLocalizationIndex

/-- Number of order entries in the localized segment. -/
abbrev length (s : AlphaLocalizationIndex n) : Nat :=
  s.stop - s.start + 1

theorem bound (s : AlphaLocalizationIndex n) : s.start + s.length ≤ n + 1 := by
  unfold length
  have hstart : s.start ≤ s.stop :=
    s.start_le_pivot.trans s.pivot_lt_stop.le
  have hstop := s.stop_lt
  omega

/-- The global alpha index. -/
def pivotFin (s : AlphaLocalizationIndex n) : Fin n :=
  ⟨s.pivot, by
    have hpivot := s.pivot_lt_stop
    have hstop := s.stop_lt
    omega⟩

/-- The corresponding alpha index inside the localized segment. -/
def localPivot (s : AlphaLocalizationIndex n) : Fin (s.stop - s.start) :=
  ⟨s.pivot - s.start, by
    have hstart := s.start_le_pivot
    have hpivot := s.pivot_lt_stop
    omega⟩

end AlphaLocalizationIndex

namespace BONG.GoodBONG

/-- The candidates in Definition 1 whose adjacent indices lie in the block
`start, ..., stop - 1`, together with the half-gap candidate. -/
noncomputable def localizationBlockCandidates
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n) :
    Finset (WithTop ℚ) :=
  insert (b.halfGapCandidate s.pivotFin)
    (((Finset.univ.filter fun j : Fin n =>
          s.start ≤ j.1 ∧ j ≤ s.pivotFin).image
        (b.leftDefectCandidate s.pivotFin)) ∪
      ((Finset.univ.filter fun j : Fin n =>
          s.pivotFin ≤ j ∧ j.1 < s.stop).image
        (b.rightDefectCandidate s.pivotFin)))

/-- The candidate set after replacing the block from Lemma 2.1 by the alpha
of the corresponding consecutive segment. -/
noncomputable def localizedReplacementCandidates
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    Finset (WithTop ℚ) :=
  insert ((w.toGoodBONG b.good).alpha s.localPivot)
    (b.alphaCandidates s.pivotFin \ b.localizationBlockCandidates s)

theorem localizedReplacementCandidates_nonempty
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    (b.localizedReplacementCandidates s w).Nonempty :=
  ⟨(w.toGoodBONG b.good).alpha s.localPivot,
    Finset.mem_insert_self _ _⟩

end BONG.GoodBONG

/-- The finite-minimum replacement calculation in Beli (2009/2010),
Lemma 2.1.  It has no default instance. -/
class Beli2009AlphaLocalizationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  localization
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG.GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha s.pivotFin =
      (b.localizedReplacementCandidates s w).min'
        (b.localizedReplacementCandidates_nonempty s w)

namespace BONG.GoodBONG

variable [Beli2009AlphaLocalizationLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 2.1: exact replacement of the localized block in
the finite set defining `α_i`. -/
theorem beli2009Lemma21
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha s.pivotFin =
      (b.localizedReplacementCandidates s w).min'
        (b.localizedReplacementCandidates_nonempty s w) :=
  Beli2009AlphaLocalizationLaws.localization b s w

/-- The particular inequality stated at the end of Lemma 2.1. -/
theorem beli2009Lemma21_le_segmentAlpha
    (b : GoodBONG q L (n + 1)) (s : AlphaLocalizationIndex n)
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound) :
    b.alpha s.pivotFin ≤ (w.toGoodBONG b.good).alpha s.localPivot := by
  rw [b.beli2009Lemma21 s w]
  apply Finset.min'_le
  exact Finset.mem_insert_self _ _

end BONG.GoodBONG

namespace BONG.GoodBONG

/-- The adjacent order sum `R_i + R_{i+1}`. -/
noncomputable def adjacentOrderSum
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Int :=
  b.order i.castSucc + b.order i.succ

/-- Goodness says that the adjacent order sums form a monotone sequence. -/
theorem adjacentOrderSum_monotone (b : GoodBONG q L (n + 2)) :
    Monotone b.adjacentOrderSum := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  let k : Fin (n + 2) := ⟨i.1, by omega⟩
  have hk : k.1 + 2 < n + 2 := by
    simp only [k]
    exact Nat.add_lt_add_right i.isLt 2
  have hgood := b.good k hk
  change b.order ⟨i.1, by omega⟩ + b.order ⟨i.1 + 1, by omega⟩ ≤
    b.order ⟨i.1 + 1, by omega⟩ + b.order ⟨i.1 + 2, by omega⟩
  change b.order ⟨i.1, by omega⟩ ≤ b.order ⟨i.1 + 2, by omega⟩ at hgood
  omega

/-- Beli (2009/2010), Lemma 2.2, first assertion. -/
theorem alphaLeftEndpoint_monotone (b : GoodBONG q L (n + 2)) :
    Monotone b.alphaLeftEndpoint := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  have hi : i.1 + 1 < n + 1 := by omega
  have h := b.satisfiesAlphaP1_proved i.castSucc hi
  have hindex :
      (⟨i.castSucc.1 + 1, hi⟩ : Fin (n + 1)) = i.succ := by
    apply Fin.ext
    rfl
  rw [hindex] at h
  exact h.1

/-- Beli (2009/2010), Lemma 2.2, second assertion. -/
theorem alphaRightEndpoint_antitone (b : GoodBONG q L (n + 2)) :
    Antitone b.alphaRightEndpoint := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  have hi : i.1 + 1 < n + 1 := by omega
  have h := b.satisfiesAlphaP1_proved i.castSucc hi
  have hindex :
      (⟨i.castSucc.1 + 1, hi⟩ : Fin (n + 1)) = i.succ := by
    apply Fin.ext
    rfl
  rw [hindex] at h
  exact h.2

/-! The paper applications often keep the ambient length in the form
`m+1`, without choosing a predecessor for `m`.  These fixed-rank variants
are propositionally identical to the three monotonicity statements above
and avoid transport through `m = (m-1)+1`. -/

/-- Fixed-rank form of monotonicity of adjacent order sums. -/
theorem adjacentOrderSum_monotone_fixedRank {m : Nat}
    (b : GoodBONG q L (m + 1)) : Monotone b.adjacentOrderSum := by
  cases m with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (adjacentOrderSum_monotone (n := m) b)

/-- Fixed-rank form of monotonicity of the left alpha endpoints. -/
theorem alphaLeftEndpoint_monotone_fixedRank {m : Nat}
    (b : GoodBONG q L (m + 1)) : Monotone b.alphaLeftEndpoint := by
  cases m with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (alphaLeftEndpoint_monotone (n := m) b)

/-- Fixed-rank form of antitonicity of the right alpha endpoints. -/
theorem alphaRightEndpoint_antitone_fixedRank {m : Nat}
    (b : GoodBONG q L (m + 1)) : Antitone b.alphaRightEndpoint := by
  cases m with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (alphaRightEndpoint_antitone (n := m) b)

/-- The equality case in Corollary 2.3(iii). -/
noncomputable def AttainsHalfGap
    (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  b.alphaValue i = b.halfGapValue i

theorem attainsHalfGap_iff_endpoint
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.AttainsHalfGap i ↔
      b.alphaLeftEndpoint i =
        (b.adjacentOrderSum i : ℚ) / 2 +
          (ramificationIndex K : ℚ) := by
  unfold AttainsHalfGap alphaLeftEndpoint halfGapValue orderGap
    adjacentOrderSum
  push_cast
  constructor <;> intro h <;> linarith

/-- All conclusions of Beli (2009/2010), Corollary 2.3. -/
structure ConstantAdjacentSumConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  leftEndpoint_eq : ∀ (k : Fin (n + 1)), i ≤ k → k ≤ j →
    b.alphaLeftEndpoint k = b.alphaLeftEndpoint i
  rightEndpoint_eq : ∀ (k : Fin (n + 1)), i ≤ k → k ≤ j →
    b.alphaRightEndpoint k = b.alphaRightEndpoint i
  order_eq_of_sameParity :
    ∀ (k l : Fin (n + 2)),
      i.1 ≤ k.1 → k.1 ≤ j.1 + 1 →
      i.1 ≤ l.1 → l.1 ≤ j.1 + 1 →
      k.1 % 2 = l.1 % 2 → b.order k = b.order l
  alpha_eq_of_sameParity :
    ∀ (k l : Fin (n + 1)),
      i ≤ k → k ≤ j → i ≤ l → l ≤ j →
      k.1 % 2 = l.1 % 2 → b.alphaValue k = b.alphaValue l
  attainsHalfGap_iff : ∀ (k : Fin (n + 1)), i ≤ k → k ≤ j →
    (b.AttainsHalfGap k ↔ b.AttainsHalfGap i)

/-- Beli (2009/2010), Corollary 2.3. -/
theorem beli2009Corollary23
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hij : i ≤ j) (hsum : b.adjacentOrderSum i = b.adjacentOrderSum j) :
    ConstantAdjacentSumConsequences b i j := by
  have hsumMono := b.adjacentOrderSum_monotone
  have hleftMono := b.alphaLeftEndpoint_monotone
  have hrightAnti := b.alphaRightEndpoint_antitone
  have hleftEnd : b.alphaLeftEndpoint i = b.alphaLeftEndpoint j := by
    have hleft := hleftMono hij
    have hright := hrightAnti hij
    have hsumQ := congrArg (fun z : Int => (z : ℚ)) hsum
    unfold adjacentOrderSum at hsum
    unfold adjacentOrderSum at hsumQ
    unfold alphaLeftEndpoint at hleft
    unfold alphaRightEndpoint at hright
    push_cast at hleft hright hsumQ
    apply le_antisymm hleft
    linarith [hsumQ]
  have hrightEnd : b.alphaRightEndpoint i = b.alphaRightEndpoint j := by
    have hsumQ := congrArg (fun z : Int => (z : ℚ)) hsum
    unfold adjacentOrderSum at hsumQ
    have hleftEndQ := hleftEnd
    unfold alphaLeftEndpoint at hleftEndQ
    unfold alphaRightEndpoint
    push_cast at hleftEndQ hsumQ ⊢
    linarith
  have hsumEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
      b.adjacentOrderSum k = b.adjacentOrderSum i := by
    apply le_antisymm
    · rw [hsum]
      exact hsumMono hkj
    · exact hsumMono hik
  have hleftEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
      b.alphaLeftEndpoint k = b.alphaLeftEndpoint i := by
    apply le_antisymm
    · rw [hleftEnd]
      exact hleftMono hkj
    · exact hleftMono hik
  have hrightEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
      b.alphaRightEndpoint k = b.alphaRightEndpoint i := by
    apply le_antisymm
    · exact hrightAnti hik
    · rw [hrightEnd]
      exact hrightAnti hkj
  have htwoStep (x : Nat) (hix : i.1 ≤ x) (hxj : x + 1 ≤ j.1) :
      b.order ⟨x, by omega⟩ = b.order ⟨x + 2, by omega⟩ := by
    let k₀ : Fin (n + 1) := ⟨x, by omega⟩
    let k₁ : Fin (n + 1) := ⟨x + 1, by omega⟩
    have hik₀ : i ≤ k₀ := by
      change i.1 ≤ k₀.1
      simpa only [k₀] using hix
    have hk₀j : k₀ ≤ j := by
      change k₀.1 ≤ j.1
      simp only [k₀]
      omega
    have hik₁ : i ≤ k₁ := by
      change i.1 ≤ k₁.1
      simp only [k₁]
      omega
    have hk₁j : k₁ ≤ j := by
      change k₁.1 ≤ j.1
      simp only [k₁]
      omega
    have h₀ := hsumEq k₀ hik₀ hk₀j
    have h₁ := hsumEq k₁ hik₁ hk₁j
    have heq : b.adjacentOrderSum k₀ = b.adjacentOrderSum k₁ :=
      h₀.trans h₁.symm
    unfold adjacentOrderSum at heq
    change b.order ⟨x, by omega⟩ + b.order ⟨x + 1, by omega⟩ =
      b.order ⟨x + 1, by omega⟩ + b.order ⟨x + 2, by omega⟩ at heq
    omega
  have hiterate (x d : Nat) (hix : i.1 ≤ x)
      (hxd : x + 2 * d ≤ j.1 + 1) :
      b.order ⟨x, by omega⟩ = b.order ⟨x + 2 * d, by omega⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
        have hstep := htwoStep (x + 2 * d) (by omega) (by omega)
        calc
          b.order ⟨x, by omega⟩ = b.order ⟨x + 2 * d, by omega⟩ :=
            ih (by omega)
          _ = b.order ⟨x + 2 * (d + 1), by omega⟩ := by
            simpa [Nat.mul_succ, Nat.add_assoc] using hstep
  have horderParity
      (k l : Fin (n + 2))
      (hik : i.1 ≤ k.1) (hkj : k.1 ≤ j.1 + 1)
      (hil : i.1 ≤ l.1) (hlj : l.1 ≤ j.1 + 1)
      (hparity : k.1 % 2 = l.1 % 2) : b.order k = b.order l := by
    by_cases hkl : k.1 ≤ l.1
    · have hdiv : k.1 / 2 ≤ l.1 / 2 := Nat.div_le_div_right hkl
      have hkdecomp := Nat.mod_add_div k.1 2
      have hldecomp := Nat.mod_add_div l.1 2
      obtain ⟨d, hd⟩ : ∃ d, l.1 = k.1 + 2 * d := by
        refine ⟨l.1 / 2 - k.1 / 2, ?_⟩
        omega
      have hrun := hiterate k.1 d hik (by omega)
      have hkindex : (⟨k.1, by omega⟩ : Fin (n + 2)) = k := by
        apply Fin.ext
        change k.1 = k.1
        rfl
      have hlindex : (⟨k.1 + 2 * d, by omega⟩ : Fin (n + 2)) = l := by
        apply Fin.ext
        change k.1 + 2 * d = l.1
        omega
      rw [hkindex, hlindex] at hrun
      exact hrun
    · have hlk : l.1 ≤ k.1 := by omega
      have hdiv : l.1 / 2 ≤ k.1 / 2 := Nat.div_le_div_right hlk
      have hkdecomp := Nat.mod_add_div k.1 2
      have hldecomp := Nat.mod_add_div l.1 2
      obtain ⟨d, hd⟩ : ∃ d, k.1 = l.1 + 2 * d := by
        refine ⟨k.1 / 2 - l.1 / 2, ?_⟩
        omega
      have hrun := hiterate l.1 d hil (by omega)
      have hlindex : (⟨l.1, by omega⟩ : Fin (n + 2)) = l := by
        apply Fin.ext
        change l.1 = l.1
        rfl
      have hkindex : (⟨l.1 + 2 * d, by omega⟩ : Fin (n + 2)) = k := by
        apply Fin.ext
        change l.1 + 2 * d = k.1
        omega
      rw [hlindex, hkindex] at hrun
      exact hrun.symm
  have halphaParity :
      ∀ (k l : Fin (n + 1)),
        i ≤ k → k ≤ j → i ≤ l → l ≤ j →
        k.1 % 2 = l.1 % 2 → b.alphaValue k = b.alphaValue l := by
    intro k l hik hkj hil hlj hparity
    have horders : b.order k.castSucc = b.order l.castSucc :=
      horderParity k.castSucc l.castSucc
        (by change i.1 ≤ k.1; exact hik)
        (by change k.1 ≤ j.1 + 1; omega)
        (by change i.1 ≤ l.1; exact hil)
        (by change l.1 ≤ j.1 + 1; omega)
        (by change k.1 % 2 = l.1 % 2; exact hparity)
    have hleftKL : b.alphaLeftEndpoint k = b.alphaLeftEndpoint l :=
      (hleftEq k hik hkj).trans (hleftEq l hil hlj).symm
    unfold alphaLeftEndpoint at hleftKL
    rw [horders] at hleftKL
    linarith
  have hhalfGap :
      ∀ (k : Fin (n + 1)), i ≤ k → k ≤ j →
        (b.AttainsHalfGap k ↔ b.AttainsHalfGap i) := by
    intro k hik hkj
    rw [b.attainsHalfGap_iff_endpoint k,
      b.attainsHalfGap_iff_endpoint i]
    rw [hleftEq k hik hkj, hsumEq k hik hkj]
  exact {
    leftEndpoint_eq := hleftEq
    rightEndpoint_eq := hrightEq
    order_eq_of_sameParity := horderParity
    alpha_eq_of_sameParity := halphaParity
    attainsHalfGap_iff := hhalfGap }

end BONG.GoodBONG

end Bong
