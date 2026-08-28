/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718ReplacementGlue
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.18: replacing a canonical hyperbolic tower

This file iterates the coordinate-free binary replacement from Lemma 7.18.
For an even prefix made of canonical hyperbolic pairs, with the two boundary
order estimates appearing in the paper, it constructs a literal sublattice
whose prefix coefficients are multiplied by one uniformizer and whose suffix
is unchanged.  The construction recursively splits off the first pair using
Corollary 4.4, replaces it, and glues it to the recursively modified tail.
-/

namespace Bong

open Dyadic

namespace BONG


universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace GoodBONG

structure Lemma718CanonicalPrefixData
    (a : GoodBONG q L n) (R : Int) (s : Nat) : Prop where
  even : Even s
  two_le : 2 ≤ s
  le_rank : s ≤ n
  sourcePair (j : Nat) (hj : 2 * j + 1 < s) :
    a.valueUnit ⟨2 * j, by omega⟩ = lemma718CanonicalHigh (K := K) R ∧
    a.valueUnit ⟨2 * j + 1, by omega⟩ = lemma718CanonicalLow (K := K) R
  suffixHead (hs : s < n) : R + 1 ≤ a.order ⟨s, hs⟩
  suffixSecond (hs : s + 1 < n) :
    R - 2 * (ramificationIndex K : Int) + 1 ≤ a.order ⟨s + 1, hs⟩

structure Lemma718CanonicalPrefixReplacement
    (a : GoodBONG q L n) (R : Int) (s : Nat) where
  target : Lattice K V
  lattice_le : target ≤ L
  bong : GoodBONG q target n
  valueUnit (i : Fin n) : bong.valueUnit i =
    if i.val < s then uniformizerUnit K * a.valueUnit i else a.valueUnit i

theorem lemma718_valueUnit_castLength
    {M : Lattice K V} {m n : Nat} (a : GoodBONG q M m)
    (h : m = n) (i : Fin n) :
    (a.castLength h).valueUnit i = a.valueUnit ⟨i.val, by omega⟩ := by
  subst n
  rfl

theorem lemma718_segmentGood_valueUnit
    {a : GoodBONG q L n} {start length : Nat}
    {bound : start + length ≤ n}
    (w : SegmentWitness a.toBONG start length bound) (i : Fin length) :
    (w.toGoodBONG a.good).valueUnit i = a.valueUnit (w.sourceIndex i) := by
  change w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i)
  exact w.valueUnit_eq i

theorem lemma718_segmentGood_order
    {a : GoodBONG q L n} {start length : Nat}
    {bound : start + length ≤ n}
    (w : SegmentWitness a.toBONG start length bound) (i : Fin length) :
    (w.toGoodBONG a.good).order i = a.order (w.sourceIndex i) := by
  change w.bong.order i = a.toBONG.order (w.sourceIndex i)
  exact w.order_eq i

theorem lemma718_two_add_lt_add_three {m i : Nat} (hi : i < m + 1) :
    2 + i < m + 3 := by
  omega

theorem lemma718_add_three_sub_two (m : Nat) : (m + 3) - 2 = m + 1 := by
  omega

theorem lemma718_one_next_lt_add_three (m : Nat) :
    (1 : Fin (m + 3)).val + 1 < m + 3 := by
  simp

theorem lemma718IndexPHigh_eq_uniformizer_mul (R : Int) :
    lemma718IndexPHigh (K := K) R =
      uniformizerUnit K * lemma718CanonicalHigh (K := K) R := by
  unfold lemma718IndexPHigh lemma718CanonicalHigh
  rw [mul_comm, lemma718_uniformizerPowerUnit_mul_uniformizerUnit]

theorem lemma718IndexPLow_eq_uniformizer_mul (R : Int) :
    lemma718IndexPLow (K := K) R =
      uniformizerUnit K * lemma718CanonicalLow (K := K) R := by
  unfold lemma718IndexPLow lemma718CanonicalLow
  have hexponent :
      R - 2 * (ramificationIndex K : Int) + 1 =
        (R - 2 * (ramificationIndex K : Int)) + 1 := by omega
  rw [hexponent, ← lemma718_uniformizerPowerUnit_mul_uniformizerUnit]
  simp [mul_comm]

noncomputable def lemma718CanonicalPrefixReplacement_terminal
    (a : GoodBONG q L 2) (R : Int)
    (D : Lemma718CanonicalPrefixData a R 2) :
    Lemma718CanonicalPrefixReplacement a R 2 := by
  let C := lemma718CanonicalPairReplacement a R
    (D.sourcePair 0 (by omega)).1 (D.sourcePair 0 (by omega)).2
  exact {
    target := C.target
    lattice_le := C.inclusion.lattice_le
    bong := C.bong
    valueUnit := by
      intro i
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        have hzero : a.valueUnit (0 : Fin 2) =
            lemma718CanonicalHigh (K := K) R := by
          simpa using (D.sourcePair 0 (by omega)).1
        rw [if_pos (by omega), C.valueUnit, hzero]
        simp only [Matrix.cons_val_zero]
        exact lemma718IndexPHigh_eq_uniformizer_mul R
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        have hone : a.valueUnit (1 : Fin 2) =
            lemma718CanonicalLow (K := K) R := by
          simpa using (D.sourcePair 0 (by omega)).2
        rw [if_pos (by omega), C.valueUnit, hone]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        exact lemma718IndexPLow_eq_uniformizer_mul R }

noncomputable def lemma718CanonicalPrefixReplacement_two_with_split
    (a : GoodBONG q L (n + 3)) (R : Int)
    (D : Lemma718CanonicalPrefixData a R 2)
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega)) :
    Lemma718CanonicalPrefixReplacement a R 2 := by
  let left := S.left.toGoodBONG a.good
  have hleftZero : left.valueUnit (0 : Fin 2) =
      lemma718CanonicalHigh (K := K) R := by
    have hsource := (D.sourcePair 0 (by omega)).1
    change a.toBONG.valueUnit ⟨2 * 0, by omega⟩ = _ at hsource
    change S.left.bong.valueUnit (0 : Fin 2) = _
    rw [S.left.valueUnit_eq]
    simpa [SegmentWitness.sourceIndex] using hsource
  have hleftOne : left.valueUnit (1 : Fin 2) =
      lemma718CanonicalLow (K := K) R := by
    have hsource := (D.sourcePair 0 (by omega)).2
    change a.toBONG.valueUnit ⟨2 * 0 + 1, by omega⟩ = _ at hsource
    change S.left.bong.valueUnit (1 : Fin 2) = _
    rw [S.left.valueUnit_eq]
    simpa [SegmentWitness.sourceIndex] using hsource
  let C := lemma718CanonicalPairReplacement left R hleftZero hleftOne
  let rightRaw := S.right.toGoodBONG a.good
  have hrightLength : (n + 3) - 2 = n + 1 := by omega
  let right := rightRaw.castLength hrightLength
  have hrightOrder (i : Fin (n + 1)) :
      right.order i = a.order ⟨2 + i.val, by omega⟩ := by
    rw [show right = rightRaw.castLength hrightLength by rfl,
      GoodBONG.order_castLength]
    change S.right.bong.order ⟨i.val, by omega⟩ = _
    rw [S.right.order_eq]
    congr 1
  have hCZero : C.bong.order (0 : Fin 2) = R + 1 := by
    change ordUnit K (C.bong.valueUnit 0) = R + 1
    rw [C.valueUnit]
    simp only [Matrix.cons_val_zero]
    unfold lemma718IndexPHigh
    rw [ordUnit_uniformizerPowerUnit]
  have hCOne : C.bong.order (1 : Fin 2) =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    change ordUnit K (C.bong.valueUnit 1) = _
    rw [C.valueUnit]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    unfold lemma718IndexPLow
    rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
  have horder : ∀ i : Fin 2, C.bong.order i ≤ right.order 0 := by
    intro i
    have hsuffix := D.suffixHead (by omega)
    rw [hrightOrder]
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      rw [hieq, hCZero]
      simpa using hsuffix
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      rw [hieq, hCOne]
      have hepos := ramificationIndex_pos (K := K)
      have : R - 2 * (ramificationIndex K : Int) + 1 ≤ R + 1 := by omega
      exact this.trans (by simpa using hsuffix)
  have hlastSecond : ∀ (_ : 0 < 2) (hm : 1 < n + 1),
      C.bong.order ⟨1, by omega⟩ ≤ right.order ⟨1, hm⟩ := by
    intro _ hm
    have honeIndex : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
    rw [honeIndex, hCOne, hrightOrder]
    simpa using D.suffixSecond (by omega)
  let G := lemma718SplitReplacement a S C.target C.bong
    S.right.lattice right C.inclusion.lattice_le
      (fun _ hx => hx) horder hlastSecond
  exact {
    target := G.target
    lattice_le := G.lattice_le
    bong := G.bong
    valueUnit := by
      intro i
      by_cases hi : i.val < 2
      · have hiCases : i.val = 0 ∨ i.val = 1 := by omega
        rcases hiCases with hiZero | hiOne
        · have hieq : i = (0 : Fin (n + 3)) := Fin.ext hiZero
          subst i
          rw [if_pos (by omega)]
          have hindex : (0 : Fin (n + 3)) =
              orthogonalProductLeftIndex (n + 1) (0 : Fin 2) := by
            apply Fin.ext
            rfl
          rw [hindex, G.valueUnit_left, C.valueUnit]
          simp only [Matrix.cons_val_zero]
          rw [lemma718IndexPHigh_eq_uniformizer_mul]
          have hsource := (D.sourcePair 0 (by omega)).1
          change a.toBONG.valueUnit ⟨2 * 0, by omega⟩ = _ at hsource
          change uniformizerUnit K * lemma718CanonicalHigh (K := K) R =
            uniformizerUnit K * a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (0 : Fin 2))
          rw [show a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (0 : Fin 2)) =
                lemma718CanonicalHigh (K := K) R by
            simpa [orthogonalProductLeftIndex] using hsource]
        · have hieq : i = (1 : Fin (n + 3)) := Fin.ext hiOne
          subst i
          rw [if_pos (by omega)]
          have hindex : (1 : Fin (n + 3)) =
              orthogonalProductLeftIndex (n + 1) (1 : Fin 2) := by
            apply Fin.ext
            rfl
          rw [hindex, G.valueUnit_left, C.valueUnit]
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [lemma718IndexPLow_eq_uniformizer_mul]
          have hsource := (D.sourcePair 0 (by omega)).2
          change a.toBONG.valueUnit ⟨2 * 0 + 1, by omega⟩ = _ at hsource
          change uniformizerUnit K * lemma718CanonicalLow (K := K) R =
            uniformizerUnit K * a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (1 : Fin 2))
          rw [show a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (1 : Fin 2)) =
                lemma718CanonicalLow (K := K) R by
            simpa [orthogonalProductLeftIndex] using hsource]
      · let k : Fin (n + 1) := ⟨i.val - 2, by omega⟩
        have hindex : i = orthogonalProductRightIndex 2 k := by
          apply Fin.ext
          simp [k, orthogonalProductRightIndex]
          omega
        rw [if_neg hi, hindex, G.valueUnit_right]
        rw [show right = rightRaw.castLength hrightLength by rfl,
          lemma718_valueUnit_castLength]
        change S.right.bong.valueUnit ⟨k.val, by omega⟩ =
          a.toBONG.valueUnit (orthogonalProductRightIndex 2 k)
        rw [S.right.valueUnit_eq]
        congr 1 }

noncomputable def lemma718CanonicalPrefixReplacement_step
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) (hs : 2 ≤ s)
    (D : Lemma718CanonicalPrefixData a R (s + 2))
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (right : GoodBONG
      (q.restrict S.right.carrier S.right.nondegenerate)
      S.right.lattice (n + 1))
    (hrightValue : ∀ i : Fin (n + 1), right.valueUnit i =
      a.valueUnit ⟨2 + i.val, by omega⟩)
    (E : Lemma718CanonicalPrefixReplacement right R s) :
    Lemma718CanonicalPrefixReplacement a R (s + 2) := by
  have hsRank := D.le_rank
  have hnTwo : 1 < n + 1 := by omega
  let left := S.left.toGoodBONG a.good
  have hleftZero : left.valueUnit (0 : Fin 2) =
      lemma718CanonicalHigh (K := K) R := by
    have hsource := (D.sourcePair 0 (by omega)).1
    change a.toBONG.valueUnit ⟨2 * 0, by omega⟩ = _ at hsource
    change S.left.bong.valueUnit (0 : Fin 2) = _
    rw [S.left.valueUnit_eq]
    simpa [SegmentWitness.sourceIndex] using hsource
  have hleftOne : left.valueUnit (1 : Fin 2) =
      lemma718CanonicalLow (K := K) R := by
    have hsource := (D.sourcePair 0 (by omega)).2
    change a.toBONG.valueUnit ⟨2 * 0 + 1, by omega⟩ = _ at hsource
    change S.left.bong.valueUnit (1 : Fin 2) = _
    rw [S.left.valueUnit_eq]
    simpa [SegmentWitness.sourceIndex] using hsource
  let C := lemma718CanonicalPairReplacement left R hleftZero hleftOne
  have hrightZero : right.valueUnit (0 : Fin (n + 1)) =
      lemma718CanonicalHigh (K := K) R := by
    rw [hrightValue]
    have hsource := (D.sourcePair 1 (by omega)).1
    simpa using hsource
  have hrightOne : right.valueUnit ⟨1, hnTwo⟩ =
      lemma718CanonicalLow (K := K) R := by
    rw [hrightValue]
    have hsource := (D.sourcePair 1 (by omega)).2
    simpa using hsource
  have hCZero : C.bong.order (0 : Fin 2) = R + 1 := by
    change ordUnit K (C.bong.valueUnit 0) = R + 1
    rw [C.valueUnit]
    simp only [Matrix.cons_val_zero]
    unfold lemma718IndexPHigh
    rw [ordUnit_uniformizerPowerUnit]
  have hCOne : C.bong.order (1 : Fin 2) =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    change ordUnit K (C.bong.valueUnit 1) = _
    rw [C.valueUnit]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    unfold lemma718IndexPLow
    rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
  have hEZero : E.bong.order (0 : Fin (n + 1)) = R + 1 := by
    change ordUnit K (E.bong.valueUnit 0) = R + 1
    rw [E.valueUnit, if_pos (by simp; omega), hrightZero]
    rw [← lemma718IndexPHigh_eq_uniformizer_mul]
    unfold lemma718IndexPHigh
    rw [ordUnit_uniformizerPowerUnit]
  have hEOne : E.bong.order ⟨1, hnTwo⟩ =
      R - 2 * (ramificationIndex K : Int) + 1 := by
    change ordUnit K (E.bong.valueUnit ⟨1, hnTwo⟩) = _
    rw [E.valueUnit, if_pos (by simp; omega), hrightOne]
    rw [← lemma718IndexPLow_eq_uniformizer_mul]
    unfold lemma718IndexPLow
    rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
  have horder : ∀ i : Fin 2, C.bong.order i ≤ E.bong.order 0 := by
    intro i
    rw [hEZero]
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      rw [hieq, hCZero]
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      rw [hieq, hCOne]
      have hepos := ramificationIndex_pos (K := K)
      omega
  have hlastSecond : ∀ (_ : 0 < 2) (hm : 1 < n + 1),
      C.bong.order ⟨1, by omega⟩ ≤ E.bong.order ⟨1, hm⟩ := by
    intro _ hm
    have hleftIndex : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
    have hrightIndex : (⟨1, hm⟩ : Fin (n + 1)) =
        (⟨1, hnTwo⟩ : Fin (n + 1)) := Fin.ext rfl
    rw [hleftIndex, hrightIndex, hCOne, hEOne]
  let G := lemma718SplitReplacement a S C.target C.bong
    E.target E.bong C.inclusion.lattice_le E.lattice_le horder hlastSecond
  exact {
    target := G.target
    lattice_le := G.lattice_le
    bong := G.bong
    valueUnit := by
      intro i
      by_cases hi : i.val < 2
      · have hiCases : i.val = 0 ∨ i.val = 1 := by omega
        rcases hiCases with hiZero | hiOne
        · have hieq : i = (0 : Fin (n + 3)) := Fin.ext hiZero
          subst i
          rw [if_pos (by omega)]
          have hindex : (0 : Fin (n + 3)) =
              orthogonalProductLeftIndex (n + 1) (0 : Fin 2) := by
            apply Fin.ext
            rfl
          rw [hindex, G.valueUnit_left, C.valueUnit]
          simp only [Matrix.cons_val_zero]
          rw [lemma718IndexPHigh_eq_uniformizer_mul]
          have hsource := (D.sourcePair 0 (by omega)).1
          change a.toBONG.valueUnit ⟨2 * 0, by omega⟩ = _ at hsource
          change uniformizerUnit K * lemma718CanonicalHigh (K := K) R =
            uniformizerUnit K * a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (0 : Fin 2))
          rw [show a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (0 : Fin 2)) =
                lemma718CanonicalHigh (K := K) R by
            simpa [orthogonalProductLeftIndex] using hsource]
        · have hieq : i = (1 : Fin (n + 3)) := Fin.ext hiOne
          subst i
          rw [if_pos (by omega)]
          have hindex : (1 : Fin (n + 3)) =
              orthogonalProductLeftIndex (n + 1) (1 : Fin 2) := by
            apply Fin.ext
            rfl
          rw [hindex, G.valueUnit_left, C.valueUnit]
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [lemma718IndexPLow_eq_uniformizer_mul]
          have hsource := (D.sourcePair 0 (by omega)).2
          change a.toBONG.valueUnit ⟨2 * 0 + 1, by omega⟩ = _ at hsource
          change uniformizerUnit K * lemma718CanonicalLow (K := K) R =
            uniformizerUnit K * a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (1 : Fin 2))
          rw [show a.toBONG.valueUnit
              (orthogonalProductLeftIndex (n + 1) (1 : Fin 2)) =
                lemma718CanonicalLow (K := K) R by
            simpa [orthogonalProductLeftIndex] using hsource]
      · let k : Fin (n + 1) := ⟨i.val - 2, by omega⟩
        have hindex : i = orthogonalProductRightIndex 2 k := by
          apply Fin.ext
          simp [k, orthogonalProductRightIndex]
          omega
        rw [hindex, G.valueUnit_right, E.valueUnit]
        by_cases hk : k.val < s
        · rw [if_pos hk, if_pos (by
            simp only [orthogonalProductRightIndex_val]
            omega), hrightValue]
          congr 2
        · rw [if_neg hk, if_neg (by
            simp only [orthogonalProductRightIndex_val]
            omega), hrightValue]
          congr 1 }

theorem exists_lemma718CanonicalPrefixReplacement
    [BeliCorollary44Laws.{u, v} K]
    (a : GoodBONG q L n) (R : Int) (s : Nat)
    (D : Lemma718CanonicalPrefixData a R s) :
    Nonempty (Lemma718CanonicalPrefixReplacement a R s) := by
  classical
  let motive : Nat → Prop := fun s =>
    ∀ {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
      (a : GoodBONG q L n) (R : Int),
      Lemma718CanonicalPrefixData a R s →
        Nonempty (Lemma718CanonicalPrefixReplacement a R s)
  have hmot : ∀ s, motive s := by
    intro current
    induction current using Nat.strong_induction_on with
    | h current ih =>
      intro V _ _ q L n a R D
      by_cases hnTwo : n = 2
      · subst n
        have hsTwo : current = 2 := by
          have := D.two_le
          have := D.le_rank
          omega
        subst current
        exact ⟨lemma718CanonicalPrefixReplacement_terminal a R D⟩
      · have hnThree : 3 ≤ n := by
          have := D.two_le
          have := D.le_rank
          omega
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := by
          refine ⟨n - 3, ?_⟩
          omega
        have htwo := D.two_le
        have hrank := D.le_rank
        have hsourceLow := (D.sourcePair 0 (by omega)).2
        have hlow : a.order (1 : Fin (m + 3)) =
            R - 2 * (ramificationIndex K : Int) := by
          change ordUnit K (a.valueUnit (1 : Fin (m + 3))) = _
          have hsourceLow' : a.valueUnit (1 : Fin (m + 3)) =
              lemma718CanonicalLow (K := K) R := by
            have hindex : (1 : Fin (m + 3)) =
                (⟨2 * 0 + 1, by omega⟩ : Fin (m + 3)) := Fin.ext (by norm_num)
            rw [hindex]
            exact hsourceLow
          rw [hsourceLow']
          unfold lemma718CanonicalLow
          rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
        have hcutOrder : a.order (1 : Fin (m + 3)) ≤
            a.order (2 : Fin (m + 3)) := by
          rw [hlow]
          by_cases hsTwo : current = 2
          · subst current
            have hsuffix := D.suffixHead (by omega)
            have hepos := ramificationIndex_pos (K := K)
            exact (by omega :
              R - 2 * (ramificationIndex K : Int) ≤ R + 1).trans hsuffix
          · have hcurrentFour : 4 ≤ current := by
              rcases D.even with ⟨d, hd⟩
              omega
            have hsourceHigh := (D.sourcePair 1 (by omega)).1
            have hhigh : a.order (2 : Fin (m + 3)) = R := by
              change ordUnit K (a.valueUnit (2 : Fin (m + 3))) = R
              have hsourceHigh' : a.valueUnit (2 : Fin (m + 3)) =
                  lemma718CanonicalHigh (K := K) R := by
                have hindex : (2 : Fin (m + 3)) =
                    (⟨2 * 1, by omega⟩ : Fin (m + 3)) := Fin.ext (by norm_num)
                rw [hindex]
                exact hsourceHigh
              rw [hsourceHigh']
              unfold lemma718CanonicalHigh
              rw [ordUnit_uniformizerPowerUnit]
            rw [hhigh]
            have hepos := ramificationIndex_pos (K := K)
            omega
        have hcut : 2 ≤ m + 3 := by omega
        have hsplit : a.toBONG.HasTwoBlockSplit 2 hcut := by
          have h := a.toBONG.beliCorollary44_i_unconditional a.good
            (1 : Fin (m + 3)) (lemma718_one_next_lt_add_three m) (by
              change a.order (1 : Fin (m + 3)) ≤
                a.order (2 : Fin (m + 3))
              exact hcutOrder)
          simpa using h
        let S : TwoBlockSplitWitness a.toBONG 2 hcut :=
          Classical.choice hsplit
        let rightRaw := S.right.toGoodBONG a.good
        have hrightLength : (m + 3) - 2 = m + 1 :=
          lemma718_add_three_sub_two m
        let right := rightRaw.castLength hrightLength
        have hrightValue (i : Fin (m + 1)) : right.valueUnit i =
            a.valueUnit ⟨2 + i.val, lemma718_two_add_lt_add_three i.isLt⟩ := by
          let iraw : Fin ((m + 3) - 2) :=
            ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
          calc
            right.valueUnit i = rightRaw.valueUnit iraw := by
              simpa only [right, iraw] using
                lemma718_valueUnit_castLength rightRaw hrightLength i
            _ = a.valueUnit (S.right.sourceIndex iraw) := by
              exact lemma718_segmentGood_valueUnit S.right iraw
            _ = a.valueUnit ⟨2 + i.val, by
                  exact lemma718_two_add_lt_add_three i.isLt⟩ := by
              congr 1
        have hrightOrder (i : Fin (m + 1)) : right.order i =
            a.order ⟨2 + i.val, lemma718_two_add_lt_add_three i.isLt⟩ := by
          let iraw : Fin ((m + 3) - 2) :=
            ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
          calc
            right.order i = rightRaw.order iraw := by
              simpa only [right, iraw] using
                GoodBONG.order_castLength rightRaw hrightLength i
            _ = a.order (S.right.sourceIndex iraw) := by
              exact lemma718_segmentGood_order S.right iraw
            _ = a.order ⟨2 + i.val, by
                  exact lemma718_two_add_lt_add_three i.isLt⟩ := by
              congr 1
        by_cases hsTwo : current = 2
        · subst current
          exact ⟨lemma718CanonicalPrefixReplacement_two_with_split a R D S⟩
        · have hcurrentFour : 4 ≤ current := by
            rcases D.even with ⟨d, hd⟩
            omega
          obtain ⟨t, htCurrent⟩ : ∃ t, current = t + 2 := by
            exact ⟨current - 2, by omega⟩
          subst current
          have htTwo : 2 ≤ t := by omega
          have Dright : Lemma718CanonicalPrefixData right R t := by
            refine {
              even := ?_
              two_le := htTwo
              le_rank := by
                have := D.le_rank
                omega
              sourcePair := ?_
              suffixHead := ?_
              suffixSecond := ?_ }
            · rcases D.even with ⟨d, hd⟩
              refine ⟨d - 1, ?_⟩
              omega
            · intro j hj
              constructor
              · rw [hrightValue]
                have h := (D.sourcePair (j + 1) (by omega)).1
                have hindex :
                    (⟨2 + 2 * j, by omega⟩ : Fin (m + 3)) =
                      ⟨2 * (j + 1), by omega⟩ := by
                  apply Fin.ext
                  simp
                  omega
                rw [hindex]
                exact h
              · rw [hrightValue]
                have h := (D.sourcePair (j + 1) (by omega)).2
                have hindex :
                    (⟨2 + (2 * j + 1), by omega⟩ : Fin (m + 3)) =
                      ⟨2 * (j + 1) + 1, by omega⟩ := by
                  apply Fin.ext
                  simp
                  omega
                rw [hindex]
                exact h
            · intro ht
              rw [hrightOrder]
              have h := D.suffixHead (by omega)
              have hindex : (⟨2 + t, by omega⟩ : Fin (m + 3)) =
                  ⟨t + 2, by omega⟩ := by
                apply Fin.ext
                simp
                omega
              rw [hindex]
              exact h
            · intro ht
              rw [hrightOrder]
              have h := D.suffixSecond (by omega)
              have hindex : (⟨2 + (t + 1), by omega⟩ : Fin (m + 3)) =
                  ⟨t + 2 + 1, by omega⟩ := by
                apply Fin.ext
                simp
                omega
              rw [hindex]
              exact h
          rcases ih t (by omega) right R Dright with ⟨E⟩
          exact ⟨lemma718CanonicalPrefixReplacement_step a R t htTwo D S
            right hrightValue E⟩
  exact hmot s a R D

end GoodBONG

end BONG

end Bong
