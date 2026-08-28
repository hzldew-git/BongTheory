/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma717Boundary
import Bong.Bong.Beli2019Lemma718TowerReplacement
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.18(ii): realization of the type-II normal form

The first binary discriminant block is kept unchanged.  When the selected
prefix has length greater than two, Corollary 4.4 splits it from the remaining
canonical tower; the tower replacement is then applied to the right factor and
the two factors are glued back into the original ambient lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete constructive output of Lemma 7.18(ii). -/
structure Lemma718TypeIIRealization
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) where
  target : Lattice K V
  lattice_le : target ≤ L
  bong : GoodBONG q target (n + 3)
  normalForm : Lemma718TypeIINormalForm a bong R s

/-- Construct the type-II replacement lattice and its exact normal form. -/
theorem exists_lemma718TypeIIRealization
    [BeliCorollary44Laws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (stopping : Lemma717StoppingData a R s)
    (typeII : Lemma717IsTypeII a R s)
    (initialFirst : a.valueUnit ⟨0, by omega⟩ =
      lemma718CanonicalHigh (K := K) R)
    (initialSecond : a.valueUnit ⟨1, by omega⟩ =
      -(laws.discriminantUnit * uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int))))
    (sourcePair : ∀ (j : Nat) (hjOne : 1 ≤ j) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by
        have hs := stopping.le_rank
        omega⟩ = lemma718CanonicalHigh (K := K) R ∧
      a.valueUnit ⟨2 * j + 1, by
        have hs := stopping.le_rank
        omega⟩ = lemma718CanonicalLow (K := K) R) :
    Nonempty (Lemma718TypeIIRealization a R s) := by
  classical
  by_cases hsTwo : s = 2
  · subst s
    exact ⟨{
      target := L
      lattice_le := fun _ hx => hx
      bong := a
      normalForm := {
        stopping := stopping
        typeII := typeII
        initialFirst := initialFirst
        initialSecond := initialSecond
        sourcePair := sourcePair
        targetValues := by
          intro i
          change a.valueUnit i = if 2 ≤ i.val ∧ i.val < 2 then
            uniformizerUnit K * a.valueUnit i else a.valueUnit i
          rw [if_neg (by omega)] } }⟩
  · have hsFour : 4 ≤ s := by
      rcases stopping.even with ⟨d, hd⟩
      have hsTwoLe := stopping.two_le
      omega
    have hsRank := stopping.le_rank
    have hzeroOrder : a.order (0 : Fin (n + 3)) = R := by
      have hfirst : a.valueUnit (0 : Fin (n + 3)) =
          lemma718CanonicalHigh (K := K) R := by
        simpa using initialFirst
      calc
        a.order (0 : Fin (n + 3)) =
            ordUnit K (a.valueUnit (0 : Fin (n + 3))) :=
          a.toBONG.order_eq_ordUnit _
        _ = ordUnit K (lemma718CanonicalHigh (K := K) R) := by
          rw [hfirst]
        _ = R := by
          unfold lemma718CanonicalHigh
          rw [ordUnit_uniformizerPowerUnit]
    have honeOrder : a.order (1 : Fin (n + 3)) =
        R - 2 * (ramificationIndex K : Int) := by
      have hsecond : a.valueUnit (1 : Fin (n + 3)) =
          -(laws.discriminantUnit * uniformizerPowerUnit K
            (R - 2 * (ramificationIndex K : Int))) := by
        simpa using initialSecond
      calc
        a.order (1 : Fin (n + 3)) =
            ordUnit K (a.valueUnit (1 : Fin (n + 3))) :=
          a.toBONG.order_eq_ordUnit _
        _ = ordUnit K (-(laws.discriminantUnit * uniformizerPowerUnit K
              (R - 2 * (ramificationIndex K : Int)))) := by
          rw [hsecond]
        _ = R - 2 * (ramificationIndex K : Int) := by
          rw [ordUnit_neg, ordUnit_mul,
            (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
              laws.discriminant_isValuationUnit,
            ordUnit_uniformizerPowerUnit]
          ring
    have htwoOrder : a.order ⟨2, by omega⟩ = R := by
      have htwo : a.valueUnit ⟨2, by omega⟩ =
          lemma718CanonicalHigh (K := K) R := by
        have h := (sourcePair 1 (by omega) (by omega)).1
        simpa using h
      calc
        a.order ⟨2, by omega⟩ =
            ordUnit K (a.valueUnit ⟨2, by omega⟩) :=
          a.toBONG.order_eq_ordUnit _
        _ = ordUnit K (lemma718CanonicalHigh (K := K) R) := by
          rw [htwo]
        _ = R := by
          unfold lemma718CanonicalHigh
          rw [ordUnit_uniformizerPowerUnit]
    have hcutOrder : a.order (1 : Fin (n + 3)) ≤
        a.order ⟨2, by omega⟩ := by
      rw [honeOrder, htwoOrder]
      have hepos := ramificationIndex_pos (K := K)
      omega
    have hsplit : a.toBONG.HasTwoBlockSplit 2 (by omega) := by
      have hnext : (1 : Fin (n + 3)).val + 1 < n + 3 := by
        change 2 < n + 3
        omega
      have h := a.toBONG.beliCorollary44_i_unconditional a.good
        (1 : Fin (n + 3)) hnext hcutOrder
      simpa using h
    let S : TwoBlockSplitWitness a.toBONG 2 (by omega) :=
      Classical.choice hsplit
    let left := S.left.toGoodBONG a.good
    let rightRaw := S.right.toGoodBONG a.good
    have hrightLength : (n + 3) - 2 = n + 1 := by omega
    let right := rightRaw.castLength hrightLength
    have hleftValue (i : Fin 2) : left.valueUnit i =
        a.valueUnit (orthogonalProductLeftIndex (n + 1) i) := by
      change S.left.bong.valueUnit i = _
      rw [S.left.valueUnit_eq]
      congr 1
      apply Fin.ext
      rw [S.left.sourceIndex_val, orthogonalProductLeftIndex_val]
      simp
    have hleftOrder (i : Fin 2) : left.order i =
        a.order (orthogonalProductLeftIndex (n + 1) i) := by
      change S.left.bong.order i = _
      rw [S.left.order_eq]
      congr 1
      apply Fin.ext
      rw [S.left.sourceIndex_val, orthogonalProductLeftIndex_val]
      simp
    have hrightValue (i : Fin (n + 1)) : right.valueUnit i =
        a.valueUnit ⟨2 + i.val, by omega⟩ := by
      let iraw : Fin ((n + 3) - 2) :=
        ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
      calc
        right.valueUnit i = rightRaw.valueUnit iraw := by
          simpa only [right, iraw] using
            lemma718_valueUnit_castLength rightRaw hrightLength i
        _ = a.valueUnit (S.right.sourceIndex iraw) :=
          lemma718_segmentGood_valueUnit S.right iraw
        _ = a.valueUnit ⟨2 + i.val, by omega⟩ := by
          congr 1
    have hrightOrder (i : Fin (n + 1)) : right.order i =
        a.order ⟨2 + i.val, by omega⟩ := by
      let iraw : Fin ((n + 3) - 2) :=
        ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
      calc
        right.order i = rightRaw.order iraw := by
          simpa only [right, iraw] using
            GoodBONG.order_castLength rightRaw hrightLength i
        _ = a.order (S.right.sourceIndex iraw) :=
          lemma718_segmentGood_order S.right iraw
        _ = a.order ⟨2 + i.val, by omega⟩ := by
          congr 1
    have Dright : Lemma718CanonicalPrefixData right R (s - 2) := by
      refine {
        even := ?_
        two_le := by omega
        le_rank := by omega
        sourcePair := ?_
        suffixHead := ?_
        suffixSecond := ?_ }
      · rcases stopping.even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      · intro j hj
        constructor
        · rw [hrightValue]
          have h := (sourcePair (j + 1) (by omega) (by omega)).1
          have hindex : (⟨2 + 2 * j, by omega⟩ : Fin (n + 3)) =
              ⟨2 * (j + 1), by omega⟩ := by
            apply Fin.ext
            simp only [Fin.val_mk]
            omega
          rw [hindex]
          exact h
        · rw [hrightValue]
          have h := (sourcePair (j + 1) (by omega) (by omega)).2
          have hindex : (⟨2 + (2 * j + 1), by omega⟩ : Fin (n + 3)) =
              ⟨2 * (j + 1) + 1, by omega⟩ := by
            apply Fin.ext
            simp only [Fin.val_mk]
            omega
          rw [hindex]
          exact h
      · intro hsuffix
        rw [hrightOrder]
        have h := lemma717_suffixHead_ge a R s typeII.1 (by omega)
        have hindex : (⟨2 + (s - 2), by omega⟩ : Fin (n + 3)) =
            ⟨s, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hindex]
        exact h
      · intro hsuffix
        rw [hrightOrder]
        have h := lemma717_suffixSecond_ge a R s stopping (by omega)
        have hindex : (⟨2 + (s - 2 + 1), by omega⟩ : Fin (n + 3)) =
            ⟨s + 1, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hindex]
        exact h
    rcases right.exists_lemma718CanonicalPrefixReplacement R (s - 2) Dright with ⟨E⟩
    have hrightZero : right.valueUnit (0 : Fin (n + 1)) =
        lemma718CanonicalHigh (K := K) R := by
      rw [hrightValue]
      have h := (sourcePair 1 (by omega) (by omega)).1
      simpa using h
    have hrightOne : right.valueUnit ⟨1, by omega⟩ =
        lemma718CanonicalLow (K := K) R := by
      rw [hrightValue]
      have h := (sourcePair 1 (by omega) (by omega)).2
      have hindex : (⟨2 + (⟨1, by omega⟩ : Fin (n + 1)).val,
          by omega⟩ : Fin (n + 3)) = ⟨3, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact h
    have hEZero : E.bong.order (0 : Fin (n + 1)) = R + 1 := by
      change ordUnit K (E.bong.valueUnit 0) = R + 1
      rw [E.valueUnit, if_pos (by
        change (0 : Nat) < s - 2
        omega), hrightZero]
      rw [← lemma718IndexPHigh_eq_uniformizer_mul]
      unfold lemma718IndexPHigh
      rw [ordUnit_uniformizerPowerUnit]
    have hEOne : E.bong.order ⟨1, by omega⟩ =
        R - 2 * (ramificationIndex K : Int) + 1 := by
      change ordUnit K (E.bong.valueUnit ⟨1, by omega⟩) = _
      rw [E.valueUnit, if_pos (by
        change (1 : Nat) < s - 2
        omega), hrightOne]
      rw [← lemma718IndexPLow_eq_uniformizer_mul]
      unfold lemma718IndexPLow
      rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
    have horder : ∀ i : Fin 2, left.order i ≤ E.bong.order 0 := by
      intro i
      rw [hEZero, hleftOrder]
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with hi | hi
      · have hieq : i = (0 : Fin 2) := Fin.ext hi
        subst i
        rw [show a.order (orthogonalProductLeftIndex (n + 1) (0 : Fin 2)) =
            R by simpa [orthogonalProductLeftIndex] using hzeroOrder]
        omega
      · have hieq : i = (1 : Fin 2) := Fin.ext hi
        subst i
        rw [show a.order (orthogonalProductLeftIndex (n + 1) (1 : Fin 2)) =
            R - 2 * (ramificationIndex K : Int) by
          simpa [orthogonalProductLeftIndex] using honeOrder]
        have hepos := ramificationIndex_pos (K := K)
        omega
    have hlastSecond : ∀ (_ : 0 < 2) (hnRight : 1 < n + 1),
        left.order ⟨1, by omega⟩ ≤ E.bong.order ⟨1, hnRight⟩ := by
      intro _ hnRight
      have hleftIndex : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := Fin.ext rfl
      have hrightIndex : (⟨1, hnRight⟩ : Fin (n + 1)) =
          (⟨1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      rw [hleftIndex, hrightIndex, hleftOrder, hEOne]
      rw [show a.order (orthogonalProductLeftIndex (n + 1) (1 : Fin 2)) =
          R - 2 * (ramificationIndex K : Int) by
        simpa [orthogonalProductLeftIndex] using honeOrder]
      omega
    let G := lemma718SplitReplacement a S S.left.lattice left
      E.target E.bong (fun _ hx => hx) E.lattice_le horder hlastSecond
    exact ⟨{
      target := G.target
      lattice_le := G.lattice_le
      bong := G.bong
      normalForm := {
        stopping := stopping
        typeII := typeII
        initialFirst := initialFirst
        initialSecond := initialSecond
        sourcePair := sourcePair
        targetValues := by
          intro i
          by_cases hi : i.val < 2
          · let k : Fin 2 := ⟨i.val, hi⟩
            have hindex : i = orthogonalProductLeftIndex (n + 1) k := by
              apply Fin.ext
              rfl
            calc
              G.bong.valueUnit i = left.valueUnit k := by
                rw [hindex, G.valueUnit_left]
              _ = a.valueUnit i := by
                rw [hleftValue]
                congr 1
              _ = lemma718TypeIITargetValues a s i :=
                (lemma718TypeIITargetValues_initial a s i hi).symm
          · let k : Fin (n + 1) := ⟨i.val - 2, by omega⟩
            have hindex : i = orthogonalProductRightIndex 2 k := by
              apply Fin.ext
              simp [k, orthogonalProductRightIndex]
              omega
            rw [hindex, G.valueUnit_right, E.valueUnit]
            by_cases hk : k.val < s - 2
            · have htwo : 2 ≤ (orthogonalProductRightIndex 2 k).val := by
                simp [orthogonalProductRightIndex]
              have hlt : (orthogonalProductRightIndex 2 k).val < s := by
                simp only [orthogonalProductRightIndex_val]
                omega
              rw [if_pos hk, hrightValue,
                lemma718TypeIITargetValues_changed a s _ htwo hlt]
              congr 2
            · have hsle : s ≤ (orthogonalProductRightIndex 2 k).val := by
                simp only [orthogonalProductRightIndex_val]
                omega
              rw [if_neg hk, hrightValue,
                lemma718TypeIITargetValues_suffix a s _ hsle]
              congr 1 } }⟩

end BONG.GoodBONG

end Bong
