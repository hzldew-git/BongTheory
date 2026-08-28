/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma84

/-!
# Beli (2019), Lemma 8.5

This file introduces the paper's sets `A`, `B`, and `C` and proves the
finite-candidate and plateau facts used in the proof of Lemma 8.5.  In
particular, an index in `A` has a left or right defect candidate attaining
its alpha value, while membership in `A` and `B` is invariant along a block
with constant adjacent order sum.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

namespace BONG.GoodBONG

/-- The set `A` in Lemma 8.5: alpha is strictly below the half-gap
candidate. -/
def Beli2019Lemma85A (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  b.alphaValue i < b.halfGapValue i

/-- The set `B` in Lemma 8.5.  At `i`, both endpoint inequalities are
strict whenever the adjacent order sum changes in the indicated direction.
-/
def Beli2019Lemma85B (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  (∀ j : Fin n,
      b.adjacentOrderSum i < b.adjacentOrderSum j →
        b.alphaLeftEndpoint i < b.alphaLeftEndpoint j) ∧
    (∀ j : Fin n,
      b.adjacentOrderSum j < b.adjacentOrderSum i →
        b.alphaRightEndpoint i < b.alphaRightEndpoint j)

/-- The set `C` in Lemma 8.5: an index lies in both `A` and `B`, and its
central adjacent-defect candidate attains alpha. -/
def Beli2019Lemma85C (b : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  b.Beli2019Lemma85A i ∧ b.Beli2019Lemma85B i ∧
    (b.alphaValue i : WithTop ℚ) = b.leftDefectCandidate i i

theorem beli2019Lemma85A_iff_not_attainsHalfGap
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.Beli2019Lemma85A i ↔ ¬b.AttainsHalfGap i := by
  unfold Beli2019Lemma85A AttainsHalfGap
  constructor
  · exact fun hlt heq => (ne_of_lt hlt) heq
  · intro hne
    exact lt_of_le_of_ne (b.alphaValue_le_halfGapValue i) hne

/-- The minimum defining `α_i` cannot be the half-gap candidate at an index
of `A`; hence one of the explicit left or right defect candidates attains
the minimum. -/
theorem beli2019Lemma85_candidate_of_A
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hA : b.Beli2019Lemma85A i) :
    (∃ j : Fin n, j ≤ i ∧
        (b.alphaValue i : WithTop ℚ) = b.leftDefectCandidate i j) ∨
      (∃ j : Fin n, i ≤ j ∧
        (b.alphaValue i : WithTop ℚ) = b.rightDefectCandidate i j) := by
  have hmem : (b.alphaValue i : WithTop ℚ) ∈ b.alphaCandidates i := by
    rw [b.coe_alphaValue]
    exact Finset.min'_mem _ (b.alphaCandidates_nonempty i)
  unfold alphaCandidates at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with hhalf | hdefect
  · have hcoe :
        (b.alphaValue i : WithTop ℚ) =
          (b.halfGapValue i : WithTop ℚ) :=
      hhalf.trans (b.coe_halfGapValue i).symm
    have heq : b.alphaValue i = b.halfGapValue i := by
      exact_mod_cast hcoe
    exact ((ne_of_lt hA) heq).elim
  · rw [Finset.mem_union] at hdefect
    rcases hdefect with hleft | hright
    · rw [Finset.mem_image] at hleft
      rcases hleft with ⟨j, hj, hvalue⟩
      have hji : j ≤ i := (Finset.mem_filter.mp hj).2
      exact Or.inl ⟨j, hji, hvalue.symm⟩
    · rw [Finset.mem_image] at hright
      rcases hright with ⟨j, hj, hvalue⟩
      have hij : i ≤ j := (Finset.mem_filter.mp hj).2
      exact Or.inr ⟨j, hij, hvalue.symm⟩

/-- If a left candidate indexed by `j ≤ i` attains `α_i`, then the central
candidate at `j` attains `α_j` and the right endpoints at `j` and `i` agree.
This is the equality chain at the start of the proof of Lemma 8.5. -/
theorem beli2019Lemma85_leftCandidateConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hji : j ≤ i)
    (hvalue :
      (b.alphaValue i : WithTop ℚ) = b.leftDefectCandidate i j) :
    (b.alphaValue j : WithTop ℚ) = b.leftDefectCandidate j j ∧
      b.alphaRightEndpoint i = b.alphaRightEndpoint j := by
  let c : ℚ := (b.order i.succ - b.order j.succ : Int)
  have hjle :
      (b.alphaValue j : WithTop ℚ) ≤ b.leftDefectCandidate j j := by
    rw [b.coe_alphaValue]
    exact b.alpha_le_leftDefectCandidate le_rfl
  have hshift := b.left_shift_candidate_at i j j
  have hmono := b.alphaRightEndpoint_antitone hji
  have hupperQ : b.alphaValue i ≤ c + b.alphaValue j := by
    unfold alphaRightEndpoint at hmono
    dsimp [c]
    push_cast at hmono ⊢
    linarith
  have hupper :
      (b.alphaValue i : WithTop ℚ) ≤
        (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hupperQ
  have hlower :
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) ≤
        (b.alphaValue i : WithTop ℚ) := by
    calc
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) ≤
          (c : WithTop ℚ) + b.leftDefectCandidate j j :=
        by simpa [add_comm] using
          add_le_add_left hjle (c : WithTop ℚ)
      _ = b.leftDefectCandidate i j := by
        simpa only [c] using hshift
      _ = (b.alphaValue i : WithTop ℚ) := hvalue.symm
  have hsum :
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) =
        (b.alphaValue i : WithTop ℚ) :=
    le_antisymm hlower hupper
  have hcentral :
      (b.alphaValue j : WithTop ℚ) = b.leftDefectCandidate j j := by
    apply WithTop.add_left_cancel WithTop.coe_ne_top
    calc
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) =
          (b.alphaValue i : WithTop ℚ) := hsum
      _ = b.leftDefectCandidate i j := hvalue
      _ = (c : WithTop ℚ) + b.leftDefectCandidate j j := by
        simpa only [c] using hshift.symm
  have hsumQ : c + b.alphaValue j = b.alphaValue i := by
    apply WithTop.coe_injective
    simpa only [WithTop.coe_add] using hsum
  refine ⟨hcentral, ?_⟩
  unfold alphaRightEndpoint
  dsimp [c] at hsumQ
  push_cast at hsumQ ⊢
  linarith

/-- Right-candidate analogue of `beli2019Lemma85_leftCandidateConsequences`.
-/
theorem beli2019Lemma85_rightCandidateConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hvalue :
      (b.alphaValue i : WithTop ℚ) = b.rightDefectCandidate i j) :
    (b.alphaValue j : WithTop ℚ) = b.rightDefectCandidate j j ∧
      b.alphaLeftEndpoint i = b.alphaLeftEndpoint j := by
  let c : ℚ := (b.order j.castSucc - b.order i.castSucc : Int)
  have hjle :
      (b.alphaValue j : WithTop ℚ) ≤ b.rightDefectCandidate j j := by
    rw [b.coe_alphaValue]
    exact b.alpha_le_rightDefectCandidate le_rfl
  have hshift := b.right_shift_candidate_at i j j
  have hmono := b.alphaLeftEndpoint_monotone hij
  have hupperQ : b.alphaValue i ≤ c + b.alphaValue j := by
    unfold alphaLeftEndpoint at hmono
    dsimp [c]
    push_cast at hmono ⊢
    linarith
  have hupper :
      (b.alphaValue i : WithTop ℚ) ≤
        (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hupperQ
  have hlower :
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) ≤
        (b.alphaValue i : WithTop ℚ) := by
    calc
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) ≤
          (c : WithTop ℚ) + b.rightDefectCandidate j j :=
        by simpa [add_comm] using
          add_le_add_left hjle (c : WithTop ℚ)
      _ = b.rightDefectCandidate i j := by
        simpa only [c] using hshift
      _ = (b.alphaValue i : WithTop ℚ) := hvalue.symm
  have hsum :
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) =
        (b.alphaValue i : WithTop ℚ) :=
    le_antisymm hlower hupper
  have hcentral :
      (b.alphaValue j : WithTop ℚ) = b.rightDefectCandidate j j := by
    apply WithTop.add_left_cancel WithTop.coe_ne_top
    calc
      (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) =
          (b.alphaValue i : WithTop ℚ) := hsum
      _ = b.rightDefectCandidate i j := hvalue
      _ = (c : WithTop ℚ) + b.rightDefectCandidate j j := by
        simpa only [c] using hshift.symm
  have hsumQ : c + b.alphaValue j = b.alphaValue i := by
    apply WithTop.coe_injective
    simpa only [WithTop.coe_add] using hsum
  refine ⟨hcentral, ?_⟩
  unfold alphaLeftEndpoint
  dsimp [c] at hsumQ
  push_cast at hsumQ ⊢
  linarith

/-- Reconstruct a left candidate equality from the central equality at `j`
and equality of the right endpoints. -/
theorem beli2019Lemma85_leftCandidate_of_central
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hji : j ≤ i)
    (hcentral :
      (b.alphaValue j : WithTop ℚ) = b.leftDefectCandidate j j)
    (hendpoint : b.alphaRightEndpoint i = b.alphaRightEndpoint j) :
    (b.alphaValue i : WithTop ℚ) = b.leftDefectCandidate i j := by
  let c : ℚ := (b.order i.succ - b.order j.succ : Int)
  have hsumQ : b.alphaValue i = c + b.alphaValue j := by
    unfold alphaRightEndpoint at hendpoint
    dsimp [c]
    push_cast at hendpoint ⊢
    linarith
  have hshift := b.left_shift_candidate_at i j j
  calc
    (b.alphaValue i : WithTop ℚ) =
        ((c + b.alphaValue j : ℚ) : WithTop ℚ) :=
      congrArg (fun x : ℚ => (x : WithTop ℚ)) hsumQ
    _ = (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) := by
      simp only [WithTop.coe_add]
    _ = (c : WithTop ℚ) + b.leftDefectCandidate j j := by
      rw [hcentral]
    _ = b.leftDefectCandidate i j := by
      simpa only [c] using hshift

/-- Reconstruct a right candidate equality from the central equality at `j`
and equality of the left endpoints. -/
theorem beli2019Lemma85_rightCandidate_of_central
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hcentral :
      (b.alphaValue j : WithTop ℚ) = b.leftDefectCandidate j j)
    (hendpoint : b.alphaLeftEndpoint i = b.alphaLeftEndpoint j) :
    (b.alphaValue i : WithTop ℚ) = b.rightDefectCandidate i j := by
  let c : ℚ := (b.order j.castSucc - b.order i.castSucc : Int)
  have hsumQ : b.alphaValue i = c + b.alphaValue j := by
    unfold alphaLeftEndpoint at hendpoint
    dsimp [c]
    push_cast at hendpoint ⊢
    linarith
  have hshift := b.right_shift_candidate_at i j j
  have hcentralRight :
      (b.alphaValue j : WithTop ℚ) = b.rightDefectCandidate j j := by
    simpa only [leftDefectCandidate, rightDefectCandidate] using hcentral
  calc
    (b.alphaValue i : WithTop ℚ) =
        ((c + b.alphaValue j : ℚ) : WithTop ℚ) :=
      congrArg (fun x : ℚ => (x : WithTop ℚ)) hsumQ
    _ = (c : WithTop ℚ) + (b.alphaValue j : WithTop ℚ) := by
      simp only [WithTop.coe_add]
    _ = (c : WithTop ℚ) + b.rightDefectCandidate j j := by
      rw [hcentralRight]
    _ = b.rightDefectCandidate i j := by
      simpa only [c] using hshift

/-- The candidate selected from an index of `A` is itself in `A`, its
central defect candidate attains alpha, and it satisfies the corresponding
endpoint identity from Lemma 8.5.  This is the full conclusion of the lemma
apart from the later extremal refinement placing the selected index in `B`.
-/
theorem beli2019Lemma85_rawWitness
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hA : b.Beli2019Lemma85A i) :
    ∃ j : Fin (n + 1),
      b.Beli2019Lemma85A j ∧
        (b.alphaValue j : WithTop ℚ) = b.leftDefectCandidate j j ∧
        ((j ≤ i ∧
            b.alphaRightEndpoint i = b.alphaRightEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.leftDefectCandidate i j) ∨
          (i ≤ j ∧
            b.alphaLeftEndpoint i = b.alphaLeftEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.rightDefectCandidate i j)) := by
  rcases b.beli2019Lemma85_candidate_of_A i hA with
    ⟨j, hji, hvalue⟩ | ⟨j, hij, hvalue⟩
  · have H := b.beli2019Lemma85_leftCandidateConsequences i j hji hvalue
    have hAj : b.Beli2019Lemma85A j := by
      rw [b.beli2019Lemma85A_iff_not_attainsHalfGap j]
      intro hjHalf
      have hprop := b.beli2019Lemma84_iii
        j i j hji le_rfl hji H.2.symm hjHalf
      have hiHalf := hprop.2 i hji le_rfl
      exact (b.beli2019Lemma85A_iff_not_attainsHalfGap i).1 hA hiHalf
    exact ⟨j, hAj, H.1, Or.inl ⟨hji, H.2, hvalue⟩⟩
  · have H := b.beli2019Lemma85_rightCandidateConsequences i j hij hvalue
    have hAj : b.Beli2019Lemma85A j := by
      rw [b.beli2019Lemma85A_iff_not_attainsHalfGap j]
      intro hjHalf
      have hprop := b.beli2019Lemma84_ii
        i j j hij hij le_rfl H.2 hjHalf
      have hiHalf := hprop.2 i le_rfl hij
      exact (b.beli2019Lemma85A_iff_not_attainsHalfGap i).1 hA hiHalf
    have hcentral :
        (b.alphaValue j : WithTop ℚ) =
          b.leftDefectCandidate j j := by
      simpa only [leftDefectCandidate, rightDefectCandidate] using H.1
    exact ⟨j, hAj, hcentral, Or.inr ⟨hij, H.2, hvalue⟩⟩

/-- Membership in `A` is constant between two indices with the same
adjacent order sum. -/
theorem beli2019Lemma85A_iff_of_adjacentOrderSum_eq
    (b : GoodBONG q L (n + 2)) (i k : Fin (n + 1))
    (hik : i ≤ k)
    (hsum : b.adjacentOrderSum i = b.adjacentOrderSum k) :
    b.Beli2019Lemma85A i ↔ b.Beli2019Lemma85A k := by
  have C := b.beli2009Corollary23 i k hik hsum
  rw [b.beli2019Lemma85A_iff_not_attainsHalfGap i,
    b.beli2019Lemma85A_iff_not_attainsHalfGap k]
  exact not_congr (C.attainsHalfGap_iff k hik le_rfl).symm

/-- Membership in `B` is constant between two indices with the same
adjacent order sum. -/
theorem beli2019Lemma85B_iff_of_adjacentOrderSum_eq
    (b : GoodBONG q L (n + 2)) (i k : Fin (n + 1))
    (hik : i ≤ k)
    (hsum : b.adjacentOrderSum i = b.adjacentOrderSum k) :
    b.Beli2019Lemma85B i ↔ b.Beli2019Lemma85B k := by
  have C := b.beli2009Corollary23 i k hik hsum
  have hleft : b.alphaLeftEndpoint k = b.alphaLeftEndpoint i :=
    C.leftEndpoint_eq k hik le_rfl
  have hright : b.alphaRightEndpoint k = b.alphaRightEndpoint i :=
    C.rightEndpoint_eq k hik le_rfl
  constructor
  · rintro ⟨hiLeft, hiRight⟩
    constructor
    · intro j hkj
      rw [hleft]
      apply hiLeft
      rw [hsum]
      exact hkj
    · intro j hjk
      rw [hright]
      apply hiRight
      rw [hsum]
      exact hjk
  · rintro ⟨hkLeft, hkRight⟩
    constructor
    · intro j hij
      rw [← hleft]
      apply hkLeft
      rw [← hsum]
      exact hij
    · intro j hji
      rw [← hright]
      apply hkRight
      rw [← hsum]
      exact hji

/-- Failure of `B` is exactly one of the two endpoint plateaus used in the
second case of the paper's proof. -/
theorem beli2019Lemma85_not_B_cases
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hnotB : ¬b.Beli2019Lemma85B i) :
    (∃ k : Fin (n + 1),
        b.adjacentOrderSum k < b.adjacentOrderSum i ∧
          b.alphaRightEndpoint i = b.alphaRightEndpoint k) ∨
      (∃ k : Fin (n + 1),
        b.adjacentOrderSum i < b.adjacentOrderSum k ∧
          b.alphaLeftEndpoint i = b.alphaLeftEndpoint k) := by
  classical
  by_cases hleft :
      ∀ j : Fin (n + 1),
        b.adjacentOrderSum i < b.adjacentOrderSum j →
          b.alphaLeftEndpoint i < b.alphaLeftEndpoint j
  · have hright :
        ¬∀ j : Fin (n + 1),
          b.adjacentOrderSum j < b.adjacentOrderSum i →
            b.alphaRightEndpoint i < b.alphaRightEndpoint j := by
      intro h
      exact hnotB ⟨hleft, h⟩
    push Not at hright
    rcases hright with ⟨k, hsum, hnotLt⟩
    have hki : k ≤ i := by
      by_contra h
      have hik : i ≤ k := (lt_of_not_ge h).le
      exact (not_lt_of_ge (b.adjacentOrderSum_monotone hik)) hsum
    have hforward := b.alphaRightEndpoint_antitone hki
    have heq : b.alphaRightEndpoint i = b.alphaRightEndpoint k :=
      le_antisymm hforward hnotLt
    exact Or.inl ⟨k, hsum, heq⟩
  · push Not at hleft
    rcases hleft with ⟨k, hsum, hnotLt⟩
    have hik : i ≤ k := by
      by_contra h
      have hki : k ≤ i := (lt_of_not_ge h).le
      exact (not_lt_of_ge (b.adjacentOrderSum_monotone hki)) hsum
    have hforward := b.alphaLeftEndpoint_monotone hik
    have heq : b.alphaLeftEndpoint i = b.alphaLeftEndpoint k :=
      le_antisymm hforward hnotLt
    exact Or.inr ⟨k, hsum, heq⟩

/-- In the first non-`B` case, choose the least index on the right-endpoint
plateau through `i`.  The extremal index lies in `A ∩ B`, exactly as in the
first half of case 2 in the paper. -/
theorem beli2019Lemma85_exists_leftBoundary
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hA : b.Beli2019Lemma85A i)
    (hexists : ∃ k₀ : Fin (n + 1),
      b.adjacentOrderSum k₀ < b.adjacentOrderSum i ∧
        b.alphaRightEndpoint i = b.alphaRightEndpoint k₀) :
    ∃ k : Fin (n + 1),
      k ≤ i ∧ b.adjacentOrderSum k < b.adjacentOrderSum i ∧
        b.alphaRightEndpoint i = b.alphaRightEndpoint k ∧
        b.Beli2019Lemma85A k ∧ b.Beli2019Lemma85B k := by
  classical
  let plateau : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun k =>
      b.alphaRightEndpoint k = b.alphaRightEndpoint i
  have hplateau : plateau.Nonempty := by
    refine ⟨i, ?_⟩
    simp [plateau]
  let k : Fin (n + 1) := plateau.min' hplateau
  have hkMem : k ∈ plateau := plateau.min'_mem hplateau
  have hkEndpoint :
      b.alphaRightEndpoint k = b.alphaRightEndpoint i :=
    (Finset.mem_filter.mp hkMem).2
  have hiMem : i ∈ plateau := by simp [plateau]
  have hki : k ≤ i := plateau.min'_le _ hiMem
  rcases hexists with ⟨k₀, hk₀Sum, hk₀Endpoint⟩
  have hk₀Mem : k₀ ∈ plateau := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hk₀Endpoint.symm⟩
  have hkk₀ : k ≤ k₀ := plateau.min'_le _ hk₀Mem
  have hkSum :
      b.adjacentOrderSum k < b.adjacentOrderSum i :=
    (b.adjacentOrderSum_monotone hkk₀).trans_lt hk₀Sum
  have hkiStrict : k < i := by
    have hne : k ≠ i := by
      intro heq
      rw [heq] at hkSum
      exact (lt_irrefl _ hkSum)
    exact lt_of_le_of_ne hki hne
  have hrightStrict (l : Fin (n + 1)) (hlk : l < k) :
      b.alphaRightEndpoint k < b.alphaRightEndpoint l := by
    have hle := b.alphaRightEndpoint_antitone hlk.le
    apply lt_of_le_of_ne hle
    intro heq
    have hlMem : l ∈ plateau := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact heq.symm.trans hkEndpoint
    exact (not_le_of_gt hlk) (plateau.min'_le _ hlMem)
  have hkA : b.Beli2019Lemma85A k := by
    rw [b.beli2019Lemma85A_iff_not_attainsHalfGap k]
    intro hkHalf
    have H := b.beli2019Lemma84_iii
      k i k hki le_rfl hki hkEndpoint hkHalf
    have hiHalf := H.2 i hki le_rfl
    exact (b.beli2019Lemma85A_iff_not_attainsHalfGap i).1 hA hiHalf
  have hkB : b.Beli2019Lemma85B k := by
    constructor
    · intro l hklSum
      have hkl : k < l := by
        by_contra h
        have hlk : l ≤ k := le_of_not_gt h
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hlk)) hklSum
      have hleftLe := b.alphaLeftEndpoint_monotone hkl.le
      apply lt_of_le_of_ne hleftLe
      intro hleftEq
      let h : Fin (n + 1) := min l i
      have hkh : k < h := by
        change k < min l i
        rw [lt_min_iff]
        exact ⟨hkl, hkiStrict⟩
      have hhl : h ≤ l := by
        exact min_le_left _ _
      have hhi : h ≤ i := by
        exact min_le_right _ _
      have hleftH := b.beli2019Lemma84_i_left
        k l hkl.le hleftEq h hkh.le hhl
      have hrightH := b.beli2019Lemma84_i_right
        k i hki hkEndpoint h hkh.le hhi
      have hsumQ :
          (b.adjacentOrderSum h : ℚ) =
            (b.adjacentOrderSum k : ℚ) := by
        unfold alphaLeftEndpoint at hleftH
        unfold alphaRightEndpoint at hrightH
        unfold adjacentOrderSum
        push_cast at hleftH hrightH ⊢
        linarith
      have hsumEq :
          b.adjacentOrderSum h = b.adjacentOrderSum k := by
        exact_mod_cast hsumQ
      have hsumLt :
          b.adjacentOrderSum k < b.adjacentOrderSum h := by
        rcases le_total l i with hli | hil
        · simpa [h, min_eq_left hli] using hklSum
        · simpa [h, min_eq_right hil] using hkSum
      rw [hsumEq] at hsumLt
      exact (lt_irrefl _ hsumLt)
    · intro l hlkSum
      have hlk : l < k := by
        by_contra h
        have hkl : k ≤ l := le_of_not_gt h
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hkl)) hlkSum
      exact hrightStrict l hlk
  exact ⟨k, hki, hkSum, hkEndpoint.symm, hkA, hkB⟩

/-- Symmetric extremal construction: in the second non-`B` case, the
greatest index on the left-endpoint plateau through `i` belongs to `A ∩ B`.
-/
theorem beli2019Lemma85_exists_rightBoundary
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hA : b.Beli2019Lemma85A i)
    (hexists : ∃ k₀ : Fin (n + 1),
      b.adjacentOrderSum i < b.adjacentOrderSum k₀ ∧
        b.alphaLeftEndpoint i = b.alphaLeftEndpoint k₀) :
    ∃ k : Fin (n + 1),
      i ≤ k ∧ b.adjacentOrderSum i < b.adjacentOrderSum k ∧
        b.alphaLeftEndpoint i = b.alphaLeftEndpoint k ∧
        b.Beli2019Lemma85A k ∧ b.Beli2019Lemma85B k := by
  classical
  let plateau : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun k =>
      b.alphaLeftEndpoint k = b.alphaLeftEndpoint i
  have hplateau : plateau.Nonempty := by
    refine ⟨i, ?_⟩
    simp [plateau]
  let k : Fin (n + 1) := plateau.max' hplateau
  have hkMem : k ∈ plateau := plateau.max'_mem hplateau
  have hkEndpoint :
      b.alphaLeftEndpoint k = b.alphaLeftEndpoint i :=
    (Finset.mem_filter.mp hkMem).2
  have hiMem : i ∈ plateau := by simp [plateau]
  have hik : i ≤ k := plateau.le_max' _ hiMem
  rcases hexists with ⟨k₀, hk₀Sum, hk₀Endpoint⟩
  have hk₀Mem : k₀ ∈ plateau := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hk₀Endpoint.symm⟩
  have hk₀k : k₀ ≤ k := plateau.le_max' _ hk₀Mem
  have hkSum :
      b.adjacentOrderSum i < b.adjacentOrderSum k :=
    hk₀Sum.trans_le (b.adjacentOrderSum_monotone hk₀k)
  have hikStrict : i < k := by
    have hne : i ≠ k := by
      intro heq
      rw [← heq] at hkSum
      exact (lt_irrefl _ hkSum)
    exact lt_of_le_of_ne hik hne
  have hleftStrict (l : Fin (n + 1)) (hkl : k < l) :
      b.alphaLeftEndpoint k < b.alphaLeftEndpoint l := by
    have hle := b.alphaLeftEndpoint_monotone hkl.le
    apply lt_of_le_of_ne hle
    intro heq
    have hlMem : l ∈ plateau := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact heq.symm.trans hkEndpoint
    exact (not_le_of_gt hkl) (plateau.le_max' _ hlMem)
  have hkA : b.Beli2019Lemma85A k := by
    rw [b.beli2019Lemma85A_iff_not_attainsHalfGap k]
    intro hkHalf
    have H := b.beli2019Lemma84_ii
      i k k hik hik le_rfl hkEndpoint.symm hkHalf
    have hiHalf := H.2 i le_rfl hik
    exact (b.beli2019Lemma85A_iff_not_attainsHalfGap i).1 hA hiHalf
  have hkB : b.Beli2019Lemma85B k := by
    constructor
    · intro l hklSum
      have hkl : k < l := by
        by_contra h
        have hlk : l ≤ k := le_of_not_gt h
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hlk)) hklSum
      exact hleftStrict l hkl
    · intro l hlkSum
      have hlk : l < k := by
        by_contra h
        have hkl : k ≤ l := le_of_not_gt h
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hkl)) hlkSum
      have hrightLe := b.alphaRightEndpoint_antitone hlk.le
      apply lt_of_le_of_ne hrightLe
      intro hrightEq
      let h : Fin (n + 1) := max l i
      have hhk : h < k := by
        change max l i < k
        rw [max_lt_iff]
        exact ⟨hlk, hikStrict⟩
      have hlh : l ≤ h := by
        exact le_max_left _ _
      have hih : i ≤ h := by
        exact le_max_right _ _
      have hrightH₀ := b.beli2019Lemma84_i_right
        l k hlk.le hrightEq.symm h hlh hhk.le
      have hrightH :
          b.alphaRightEndpoint h = b.alphaRightEndpoint k :=
        hrightH₀.trans hrightEq.symm
      have hleftH₀ := b.beli2019Lemma84_i_left
        i k hik hkEndpoint.symm h hih hhk.le
      have hleftH :
          b.alphaLeftEndpoint h = b.alphaLeftEndpoint k :=
        hleftH₀.trans hkEndpoint.symm
      have hsumQ :
          (b.adjacentOrderSum h : ℚ) =
            (b.adjacentOrderSum k : ℚ) := by
        unfold alphaLeftEndpoint at hleftH
        unfold alphaRightEndpoint at hrightH
        unfold adjacentOrderSum
        push_cast at hleftH hrightH ⊢
        linarith
      have hsumEq :
          b.adjacentOrderSum h = b.adjacentOrderSum k := by
        exact_mod_cast hsumQ
      have hsumLt :
          b.adjacentOrderSum h < b.adjacentOrderSum k := by
        rcases le_total l i with hli | hil
        · simpa [h, max_eq_right hli] using hkSum
        · simpa [h, max_eq_left hil] using hlkSum
      rw [hsumEq] at hsumLt
      exact (lt_irrefl _ hsumLt)
  exact ⟨k, hik, hkSum, hkEndpoint.symm, hkA, hkB⟩

/-- Lemma 8.5 for the first case of the paper, `i ∈ A ∩ B`.  The candidate
index supplied by `beli2019Lemma85_rawWitness` has the same adjacent order
sum as `i`, hence also belongs to `B` and therefore lies in `C`. -/
theorem beli2019Lemma85_of_B
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hA : b.Beli2019Lemma85A i) (hB : b.Beli2019Lemma85B i) :
    ∃ j : Fin (n + 1),
      b.Beli2019Lemma85C j ∧
        b.adjacentOrderSum i = b.adjacentOrderSum j ∧
        ((j ≤ i ∧
            b.alphaRightEndpoint i = b.alphaRightEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.leftDefectCandidate i j) ∨
          (i ≤ j ∧
            b.alphaLeftEndpoint i = b.alphaLeftEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.rightDefectCandidate i j)) := by
  rcases b.beli2019Lemma85_rawWitness i hA with
    ⟨j, hAj, hcentral, hleft | hright⟩
  · rcases hleft with ⟨hji, hendpoint, hvalue⟩
    have hsumLe := b.adjacentOrderSum_monotone hji
    have hnotLt :
        ¬b.adjacentOrderSum j < b.adjacentOrderSum i := by
      intro hlt
      have hstrict := hB.2 j hlt
      rw [hendpoint] at hstrict
      exact (lt_irrefl _ hstrict)
    have hsum : b.adjacentOrderSum i = b.adjacentOrderSum j :=
      le_antisymm (le_of_not_gt hnotLt) hsumLe
    have hBj : b.Beli2019Lemma85B j :=
      (b.beli2019Lemma85B_iff_of_adjacentOrderSum_eq
        j i hji hsum.symm).2 hB
    refine ⟨j, ⟨hAj, hBj, hcentral⟩, hsum, ?_⟩
    exact Or.inl ⟨hji, hendpoint, hvalue⟩
  · rcases hright with ⟨hij, hendpoint, hvalue⟩
    have hsumLe := b.adjacentOrderSum_monotone hij
    have hnotLt :
        ¬b.adjacentOrderSum i < b.adjacentOrderSum j := by
      intro hlt
      have hstrict := hB.1 j hlt
      rw [hendpoint] at hstrict
      exact (lt_irrefl _ hstrict)
    have hsum : b.adjacentOrderSum i = b.adjacentOrderSum j :=
      le_antisymm hsumLe (le_of_not_gt hnotLt)
    have hBj : b.Beli2019Lemma85B j :=
      (b.beli2019Lemma85B_iff_of_adjacentOrderSum_eq
        i j hij hsum).1 hB
    refine ⟨j, ⟨hAj, hBj, hcentral⟩, hsum, ?_⟩
    exact Or.inr ⟨hij, hendpoint, hvalue⟩

/-- Beli (2019), Lemma 8.5.  For every `i ∈ A` there is `j ∈ C` on one
of the two endpoint plateaus through `i`; the corresponding defect candidate
attains `α_i`.  If `i ∈ B`, the selected index has the same adjacent order
sum as `i`. -/
theorem beli2019Lemma85
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hA : b.Beli2019Lemma85A i) :
    ∃ j : Fin (n + 1),
      b.Beli2019Lemma85C j ∧
        ((j ≤ i ∧
            b.alphaRightEndpoint i = b.alphaRightEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.leftDefectCandidate i j) ∨
          (i ≤ j ∧
            b.alphaLeftEndpoint i = b.alphaLeftEndpoint j ∧
            (b.alphaValue i : WithTop ℚ) =
              b.rightDefectCandidate i j)) ∧
        (b.Beli2019Lemma85B i →
          b.adjacentOrderSum i = b.adjacentOrderSum j) := by
  classical
  by_cases hB : b.Beli2019Lemma85B i
  · rcases b.beli2019Lemma85_of_B i hA hB with
      ⟨j, hCj, hsum, horientation⟩
    exact ⟨j, hCj, horientation, fun _ => hsum⟩
  · rcases b.beli2019Lemma85_not_B_cases i hB with
      ⟨k₀, hk₀Sum, hk₀Endpoint⟩ | ⟨k₀, hk₀Sum, hk₀Endpoint⟩
    · rcases b.beli2019Lemma85_exists_leftBoundary i hA
          ⟨k₀, hk₀Sum, hk₀Endpoint⟩ with
        ⟨k, hki, hkSum, hikEndpoint, hkA, hkB⟩
      rcases b.beli2019Lemma85_of_B k hkA hkB with
        ⟨j, hCj, hsumKJ, _⟩
      have hjSumLt :
          b.adjacentOrderSum j < b.adjacentOrderSum i := by
        rw [← hsumKJ]
        exact hkSum
      have hji : j ≤ i := by
        by_contra h
        have hij : i ≤ j := (lt_of_not_ge h).le
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hij)) hjSumLt
      have hrightKJ :
          b.alphaRightEndpoint k = b.alphaRightEndpoint j := by
        rcases le_total k j with hkj | hjk
        · have C := b.beli2009Corollary23 k j hkj hsumKJ
          exact (C.rightEndpoint_eq j hkj le_rfl).symm
        · have C := b.beli2009Corollary23 j k hjk hsumKJ.symm
          exact C.rightEndpoint_eq k hjk le_rfl
      have hrightIJ :
          b.alphaRightEndpoint i = b.alphaRightEndpoint j :=
        hikEndpoint.trans hrightKJ
      have hcentral :
          (b.alphaValue j : WithTop ℚ) =
            b.leftDefectCandidate j j := hCj.2.2
      have hvalue := b.beli2019Lemma85_leftCandidate_of_central
        i j hji hcentral hrightIJ
      refine ⟨j, hCj, Or.inl ⟨hji, hrightIJ, hvalue⟩, ?_⟩
      intro hBi
      exact (hB hBi).elim
    · rcases b.beli2019Lemma85_exists_rightBoundary i hA
          ⟨k₀, hk₀Sum, hk₀Endpoint⟩ with
        ⟨k, hik, hkSum, hikEndpoint, hkA, hkB⟩
      rcases b.beli2019Lemma85_of_B k hkA hkB with
        ⟨j, hCj, hsumKJ, _⟩
      have hiSumLt :
          b.adjacentOrderSum i < b.adjacentOrderSum j := by
        rw [← hsumKJ]
        exact hkSum
      have hij : i ≤ j := by
        by_contra h
        have hji : j ≤ i := (lt_of_not_ge h).le
        exact (not_lt_of_ge (b.adjacentOrderSum_monotone hji)) hiSumLt
      have hleftKJ :
          b.alphaLeftEndpoint k = b.alphaLeftEndpoint j := by
        rcases le_total k j with hkj | hjk
        · have C := b.beli2009Corollary23 k j hkj hsumKJ
          exact (C.leftEndpoint_eq j hkj le_rfl).symm
        · have C := b.beli2009Corollary23 j k hjk hsumKJ.symm
          exact C.leftEndpoint_eq k hjk le_rfl
      have hleftIJ :
          b.alphaLeftEndpoint i = b.alphaLeftEndpoint j :=
        hikEndpoint.trans hleftKJ
      have hcentral :
          (b.alphaValue j : WithTop ℚ) =
            b.leftDefectCandidate j j := hCj.2.2
      have hvalue := b.beli2019Lemma85_rightCandidate_of_central
        i j hij hcentral hleftIJ
      refine ⟨j, hCj, Or.inr ⟨hij, hleftIJ, hvalue⟩, ?_⟩
      intro hBi
      exact (hB hBi).elim

end BONG.GoodBONG

end Bong
