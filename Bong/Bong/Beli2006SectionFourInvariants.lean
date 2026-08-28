/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionThree
import Bong.Bong.DefectArithmetic
import Bong.Bong.Representation

/-!
# Beli (2006), Section 4.1 and Definition 4.3

This file proves the domination principle for capped defects, isolates the
prefix-change estimate used in Lemma 4.2, and derives the independence of
the capped defects and the invariants `A_i(M, N)` from the chosen good BONGs.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Domination replaces the left prefix factor modulo its square. -/
theorem defectOrder_replace_left (ε a a' b : Kˣ) :
    min (defectOrder (K := K) (ε * a * b))
        (defectOrder (K := K) (a * a')) ≤
      defectOrder (K := K) (ε * a' * b) := by
  calc
    min (defectOrder (K := K) (ε * a * b))
          (defectOrder (K := K) (a * a')) ≤
        defectOrder (K := K) ((ε * a * b) * (a * a')) :=
      defectOrder_mul_ge_min (ε * a * b) (a * a')
    _ = defectOrder (K := K) ((ε * a' * b) * a ^ 2) := by
      apply congrArg (defectOrder (K := K))
      simp only [pow_two]
      ac_rfl
    _ = defectOrder (K := K) (ε * a' * b) :=
      defectOrder_mul_square (ε * a' * b) a

/-- Domination replaces the right prefix factor modulo its square. -/
theorem defectOrder_replace_right (ε a b b' : Kˣ) :
    min (defectOrder (K := K) (ε * a * b))
        (defectOrder (K := K) (b * b')) ≤
      defectOrder (K := K) (ε * a * b') := by
  calc
    min (defectOrder (K := K) (ε * a * b))
          (defectOrder (K := K) (b * b')) ≤
        defectOrder (K := K) ((ε * a * b) * (b * b')) :=
      defectOrder_mul_ge_min (ε * a * b) (b * b')
    _ = defectOrder (K := K) ((ε * a * b') * b ^ 2) := by
      apply congrArg (defectOrder (K := K))
      simp only [pow_two]
      ac_rfl
    _ = defectOrder (K := K) (ε * a * b') :=
      defectOrder_mul_square (ε * a * b') b

/-- Beli's capped-defect domination principle for three lattices. -/
theorem truncatedPrefixDefect_domination
    {U : Type*} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U} {k : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1)) (ε η : Kˣ) (i j l : Nat) :
    min (a.truncatedPrefixDefect b ε i j)
        (b.truncatedPrefixDefect c η j l) ≤
      a.truncatedPrefixDefect c (ε * η) i l := by
  have hdefect :
      min (a.truncatedPrefixDefect b ε i j)
          (b.truncatedPrefixDefect c η j l) ≤
        defectOrder (K := K)
          ((ε * η) * a.prefixProduct i * c.prefixProduct l) := by
    calc
      min (a.truncatedPrefixDefect b ε i j)
            (b.truncatedPrefixDefect c η j l) ≤
          min
            (defectOrder (K := K)
              (ε * a.prefixProduct i * b.prefixProduct j))
            (defectOrder (K := K)
              (η * b.prefixProduct j * c.prefixProduct l)) :=
        min_le_min
          (a.truncatedPrefixDefect_le_defect b ε i j)
          (b.truncatedPrefixDefect_le_defect c η j l)
      _ ≤ defectOrder (K := K)
          ((ε * a.prefixProduct i * b.prefixProduct j) *
            (η * b.prefixProduct j * c.prefixProduct l)) :=
        defectOrder_mul_ge_min _ _
      _ = defectOrder (K := K)
          (((ε * η) * a.prefixProduct i * c.prefixProduct l) *
            (b.prefixProduct j) ^ 2) := by
        apply congrArg (defectOrder (K := K))
        simp only [pow_two]
        ac_rfl
      _ = defectOrder (K := K)
          ((ε * η) * a.prefixProduct i * c.prefixProduct l) :=
        defectOrder_mul_square _ _
  have hleft :
      min (a.truncatedPrefixDefect b ε i j)
          (b.truncatedPrefixDefect c η j l) ≤ a.prefixAlphaCap i :=
    (min_le_left _ _).trans
      (a.truncatedPrefixDefect_le_leftCap b ε i j)
  have hright :
      min (a.truncatedPrefixDefect b ε i j)
          (b.truncatedPrefixDefect c η j l) ≤ c.prefixAlphaCap l :=
    (min_le_right _ _).trans
      (b.truncatedPrefixDefect_le_rightCap c η j l)
  change _ ≤ min _ (min (a.prefixAlphaCap i) (c.prefixAlphaCap l))
  exact le_min hdefect (le_min hleft hright)

/-- Every candidate in Definition 4.3 is bounded below by `A_i`. -/
theorem representationAlpha_le_primary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i ≤ a.representationPrimaryDefect b i := by
  apply Finset.min'_le
  rw [representationAlphaCandidates]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem representationAlpha_le_secondary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationAlpha b i ≤ a.representationSecondaryDefect b i hi := by
  apply Finset.min'_le
  simp [representationAlphaCandidates, hi]

theorem terminalAdjustedAlpha_le_primary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedAlpha b hgap ≤ a.terminalAdjustedPrimary b hgap :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem terminalAdjustedAlpha_le_secondary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1)
    (hinner : n + 3 < m + 1) :
    a.terminalAdjustedAlpha b hgap ≤
      a.terminalAdjustedSecondary b hinner := by
  apply Finset.min'_le
  simp [terminalAdjustedCandidates, hinner]

end BONG.GoodBONG

/-- The prefix-change defect estimate used in Beli (2006), Lemma 4.2.
It includes the determinant endpoint and intentionally has no default
instance. -/
class Beli2006PrefixChangeLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  prefixChangeDefectBound
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (a a' : BONG.GoodBONG q L (n + 1)) (i : Nat) :
    a.prefixAlphaCap i ≤
      BONG.GoodBONG.defectOrder (K := K)
        (a.prefixProduct i * a'.prefixProduct i)

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

section OneLattice

variable [classification : GoodBONGClassificationLaws.{u, v, v} K]

/-- The alpha cap at every prefix boundary is independent of the good BONG. -/
theorem prefixAlphaCap_invariant (a a' : GoodBONG q L (m + 1)) (i : Nat) :
    a.prefixAlphaCap i = a'.prefixAlphaCap i := by
  by_cases hi : 0 < i ∧ i < m + 1
  · rw [a.prefixAlphaCap_of_internal hi.1 hi.2,
      a'.prefixAlphaCap_of_internal hi.1 hi.2]
    have hα := a.alpha_invariant a' ⟨i - 1, by omega⟩
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hα
  · have hi' : ¬(0 < i ∧ i ≤ m) := by omega
    simp [prefixAlphaCap, hi']

end OneLattice

variable
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}
  [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
  [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
  [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
  [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]

/-- One direction of Lemma 4.2, separated so the equality proof can use it
twice with the two choices of BONG interchanged. -/
theorem truncatedPrefixDefect_le_of_change
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j ≤
      a'.truncatedPrefixDefect b' ε i j := by
  have hleftChange :
      a.prefixAlphaCap i ≤
        defectOrder (K := K) (a.prefixProduct i * a'.prefixProduct i) := by
    letI := prefixChangeV
    exact Beli2006PrefixChangeLaws.prefixChangeDefectBound a a' i
  have hrightChange :
      b.prefixAlphaCap j ≤
        defectOrder (K := K) (b.prefixProduct j * b'.prefixProduct j) := by
    letI := prefixChangeW
    exact Beli2006PrefixChangeLaws.prefixChangeDefectBound b b' j
  have hleftDefect :
      a.truncatedPrefixDefect b ε i j ≤
        defectOrder (K := K)
          (ε * a'.prefixProduct i * b.prefixProduct j) := by
    calc
      a.truncatedPrefixDefect b ε i j ≤
          min
            (defectOrder (K := K)
              (ε * a.prefixProduct i * b.prefixProduct j))
            (defectOrder (K := K)
              (a.prefixProduct i * a'.prefixProduct i)) :=
        le_min
          (a.truncatedPrefixDefect_le_defect b ε i j)
          ((a.truncatedPrefixDefect_le_leftCap b ε i j).trans
            hleftChange)
      _ ≤ defectOrder (K := K)
          (ε * a'.prefixProduct i * b.prefixProduct j) :=
        defectOrder_replace_left _ _ _ _
  have htargetDefect :
      a.truncatedPrefixDefect b ε i j ≤
        defectOrder (K := K)
          (ε * a'.prefixProduct i * b'.prefixProduct j) := by
    calc
      a.truncatedPrefixDefect b ε i j ≤
          min
            (defectOrder (K := K)
              (ε * a'.prefixProduct i * b.prefixProduct j))
            (defectOrder (K := K)
              (b.prefixProduct j * b'.prefixProduct j)) :=
        le_min hleftDefect
          ((a.truncatedPrefixDefect_le_rightCap b ε i j).trans
            hrightChange)
      _ ≤ defectOrder (K := K)
          (ε * a'.prefixProduct i * b'.prefixProduct j) :=
        defectOrder_replace_right _ _ _ _
  have htargetLeft :
      a.truncatedPrefixDefect b ε i j ≤ a'.prefixAlphaCap i := by
    rw [← prefixAlphaCap_invariant (classification := classificationV) a a' i]
    exact a.truncatedPrefixDefect_le_leftCap b ε i j
  have htargetRight :
      a.truncatedPrefixDefect b ε i j ≤ b'.prefixAlphaCap j := by
    rw [← prefixAlphaCap_invariant (classification := classificationW) b b' j]
    exact a.truncatedPrefixDefect_le_rightCap b ε i j
  change a.truncatedPrefixDefect b ε i j ≤
    min _ (min (a'.prefixAlphaCap i) (b'.prefixAlphaCap j))
  exact le_min htargetDefect (le_min htargetLeft htargetRight)

/-- Beli (2006), Lemma 4.2 for `d[ε a₁,ᵢ b₁,ⱼ]`. -/
theorem truncatedPrefixDefect_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j =
      a'.truncatedPrefixDefect b' ε i j :=
  le_antisymm
    (truncatedPrefixDefect_le_of_change
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a a' b b' ε i j)
    (truncatedPrefixDefect_le_of_change
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a' a b' b ε i j)

omit classificationW prefixChangeW in
/-- Beli (2006), Lemma 4.2 for the segment notation `d[ε aᵢ,ⱼ]`. -/
theorem truncatedSegmentDefect_invariant
    (a a' : GoodBONG q L (m + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedSegmentDefect ε i j =
      a'.truncatedSegmentDefect ε i j :=
  truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationV)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeV)
    a a' a a' ε (i - 1) j

omit prefixChangeV prefixChangeW in
theorem representationHalfGap_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationHalfGap b i = a'.representationHalfGap b' i := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  have hai := ha ⟨i.val, i.lt_large⟩
  have hbi := hb ⟨i.val - 1, by have := i.le_small; omega⟩
  unfold representationHalfGap
  rw [hai, hbi]

theorem representationPrimaryDefect_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationPrimaryDefect b i =
      a'.representationPrimaryDefect b' i := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  have hai := ha ⟨i.val, i.lt_large⟩
  have hbi := hb ⟨i.val - 1, by have := i.le_small; omega⟩
  have hdefect := truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' (-1) (i.val + 1) (i.val - 1)
  unfold representationPrimaryDefect
  rw [hai, hbi, hdefect]

theorem representationSecondaryDefect_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) :
    a.representationSecondaryDefect b i hi =
      a'.representationSecondaryDefect b' i hi := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  have hai := ha ⟨i.val, i.lt_large⟩
  have hais := ha ⟨i.val + 1, hi.2⟩
  have hbim := hb ⟨i.val - 2, by have := i.le_small; omega⟩
  have hbi := hb ⟨i.val - 1, by have := i.le_small; omega⟩
  have hdefect := truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' 1 (i.val + 2) (i.val - 2)
  unfold representationSecondaryDefect
  rw [hai, hais, hbim, hbi, hdefect]

theorem representationAlphaCandidates_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaCandidates b i =
      a'.representationAlphaCandidates b' i := by
  have hh := representationHalfGap_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    a a' b b' i
  have hp := representationPrimaryDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' i
  unfold representationAlphaCandidates
  rw [hh, hp]
  split_ifs with hi
  · rw [representationSecondaryDefect_invariant
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a a' b b' i hi]
  · rfl

/-- Definition 4.3's `A_i(M, N)` is independent of both chosen good BONGs. -/
theorem representationAlpha_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i = a'.representationAlpha b' i := by
  have hcandidates := representationAlphaCandidates_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' i
  unfold representationAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [hcandidates] using hx
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [hcandidates] using hx

theorem representationAlphaValue_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlphaValue b i =
      a'.representationAlphaValue b' i := by
  apply WithTop.coe_injective
  rw [coe_representationAlphaValue, coe_representationAlphaValue,
    representationAlpha_invariant
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a a' b b' i]

theorem terminalAdjustedPrimary_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedPrimary b hgap =
      a'.terminalAdjustedPrimary b' hgap := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hai := ha ⟨n + 2, hgap⟩
  have hdefect := truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' (-1) (n + 3) (n + 1)
  unfold terminalAdjustedPrimary
  rw [hai, hdefect]

theorem terminalAdjustedSecondary_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hinner : n + 3 < m + 1) :
    a.terminalAdjustedSecondary b hinner =
      a'.terminalAdjustedSecondary b' hinner := by
  have ha : a.SameOrders a' := by
    letI := classificationV
    exact a.order_invariant a'
  have hb : b.SameOrders b' := by
    letI := classificationW
    exact b.order_invariant b'
  have hai := ha ⟨n + 2, by omega⟩
  have hais := ha ⟨n + 3, hinner⟩
  have hbi := hb ⟨n, by omega⟩
  have hdefect := truncatedPrefixDefect_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' 1 (n + 4) n
  unfold terminalAdjustedSecondary
  rw [hai, hais, hbi, hdefect]

theorem terminalAdjustedCandidates_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedCandidates b hgap =
      a'.terminalAdjustedCandidates b' hgap := by
  have hp := terminalAdjustedPrimary_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' hgap
  unfold terminalAdjustedCandidates
  rw [hp]
  split_ifs with hinner
  · rw [terminalAdjustedSecondary_invariant
      (classificationV := classificationV) (classificationW := classificationW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      a a' b b' hinner]
  · rfl

/-- The exceptional value `S_{n+1} + A_{n+1}` is also BONG-independent. -/
theorem terminalAdjustedAlpha_invariant
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedAlpha b hgap =
      a'.terminalAdjustedAlpha b' hgap := by
  have hcandidates := terminalAdjustedCandidates_invariant
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a a' b b' hgap
  unfold terminalAdjustedAlpha
  apply le_antisymm
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [hcandidates] using hx
  · apply Finset.le_min'
    intro x hx
    apply Finset.min'_le
    simpa only [hcandidates] using hx

end BONG.GoodBONG

end Bong
